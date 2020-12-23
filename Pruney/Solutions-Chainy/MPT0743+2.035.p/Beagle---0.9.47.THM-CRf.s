%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:12 EST 2020

% Result     : Theorem 9.93s
% Output     : CNFRefutation 9.93s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 264 expanded)
%              Number of leaves         :   31 (  98 expanded)
%              Depth                    :   14
%              Number of atoms          :  214 ( 625 expanded)
%              Number of equality atoms :   22 (  42 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_99,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_95,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_104,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_69,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_80,axiom,(
    ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_48,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_46,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_30,plain,(
    ! [B_31,A_30] :
      ( r1_ordinal1(B_31,A_30)
      | r1_ordinal1(A_30,B_31)
      | ~ v3_ordinal1(B_31)
      | ~ v3_ordinal1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7682,plain,(
    ! [A_433,B_434] :
      ( r1_tarski(A_433,B_434)
      | ~ r1_ordinal1(A_433,B_434)
      | ~ v3_ordinal1(B_434)
      | ~ v3_ordinal1(A_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_42,plain,(
    ! [A_39] :
      ( v3_ordinal1(k1_ordinal1(A_39))
      | ~ v3_ordinal1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_874,plain,(
    ! [B_128,A_129] :
      ( r2_hidden(B_128,A_129)
      | B_128 = A_129
      | r2_hidden(A_129,B_128)
      | ~ v3_ordinal1(B_128)
      | ~ v3_ordinal1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_44,plain,(
    ! [B_41,A_40] :
      ( ~ r1_tarski(B_41,A_40)
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2547,plain,(
    ! [B_204,A_205] :
      ( ~ r1_tarski(B_204,A_205)
      | r2_hidden(B_204,A_205)
      | B_204 = A_205
      | ~ v3_ordinal1(B_204)
      | ~ v3_ordinal1(A_205) ) ),
    inference(resolution,[status(thm)],[c_874,c_44])).

tff(c_50,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_84,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_2557,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2547,c_84])).

tff(c_2565,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_2557])).

tff(c_2566,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2565])).

tff(c_56,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_133,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_56])).

tff(c_565,plain,(
    ! [A_105,B_106] :
      ( r1_tarski(A_105,B_106)
      | ~ r1_ordinal1(A_105,B_106)
      | ~ v3_ordinal1(B_106)
      | ~ v3_ordinal1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    ! [A_32] : k2_xboole_0(A_32,k1_tarski(A_32)) = k1_ordinal1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_227,plain,(
    ! [A_76,C_77,B_78] :
      ( r1_tarski(A_76,C_77)
      | ~ r1_tarski(k2_xboole_0(A_76,B_78),C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_241,plain,(
    ! [A_32,C_77] :
      ( r1_tarski(A_32,C_77)
      | ~ r1_tarski(k1_ordinal1(A_32),C_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_227])).

tff(c_7128,plain,(
    ! [A_376,B_377] :
      ( r1_tarski(A_376,B_377)
      | ~ r1_ordinal1(k1_ordinal1(A_376),B_377)
      | ~ v3_ordinal1(B_377)
      | ~ v3_ordinal1(k1_ordinal1(A_376)) ) ),
    inference(resolution,[status(thm)],[c_565,c_241])).

tff(c_7158,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_133,c_7128])).

tff(c_7170,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_7158])).

tff(c_7171,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_2566,c_7170])).

tff(c_7174,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_7171])).

tff(c_7178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_7174])).

tff(c_7179,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2565])).

tff(c_7181,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7179,c_133])).

tff(c_38,plain,(
    ! [A_35] : k1_ordinal1(A_35) != A_35 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_71,plain,(
    ! [A_49] : k2_xboole_0(A_49,k1_tarski(A_49)) = k1_ordinal1(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_77,plain,(
    ! [A_49] : r1_tarski(A_49,k1_ordinal1(A_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2296,plain,(
    ! [B_192,A_193] :
      ( B_192 = A_193
      | ~ r1_tarski(B_192,A_193)
      | ~ r1_ordinal1(A_193,B_192)
      | ~ v3_ordinal1(B_192)
      | ~ v3_ordinal1(A_193) ) ),
    inference(resolution,[status(thm)],[c_565,c_2])).

tff(c_2353,plain,(
    ! [A_49] :
      ( k1_ordinal1(A_49) = A_49
      | ~ r1_ordinal1(k1_ordinal1(A_49),A_49)
      | ~ v3_ordinal1(A_49)
      | ~ v3_ordinal1(k1_ordinal1(A_49)) ) ),
    inference(resolution,[status(thm)],[c_77,c_2296])).

tff(c_7297,plain,(
    ! [A_384] :
      ( ~ r1_ordinal1(k1_ordinal1(A_384),A_384)
      | ~ v3_ordinal1(A_384)
      | ~ v3_ordinal1(k1_ordinal1(A_384)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_2353])).

tff(c_7300,plain,
    ( ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_7181,c_7297])).

tff(c_7311,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_7300])).

tff(c_7317,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_7311])).

tff(c_7321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_7317])).

tff(c_7323,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_7326,plain,(
    ! [B_387,A_388] :
      ( ~ r1_tarski(B_387,A_388)
      | ~ r2_hidden(A_388,B_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_7330,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_7323,c_7326])).

tff(c_7723,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_7682,c_7330])).

tff(c_7736,plain,(
    ~ r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_7723])).

tff(c_7739,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_7736])).

tff(c_7745,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_7739])).

tff(c_36,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ r1_ordinal1(A_33,B_34)
      | ~ v3_ordinal1(B_34)
      | ~ v3_ordinal1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(k1_tarski(A_26),B_27)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7935,plain,(
    ! [A_445,C_446,B_447] :
      ( r1_tarski(k2_xboole_0(A_445,C_446),B_447)
      | ~ r1_tarski(C_446,B_447)
      | ~ r1_tarski(A_445,B_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9103,plain,(
    ! [A_511,B_512] :
      ( r1_tarski(k1_ordinal1(A_511),B_512)
      | ~ r1_tarski(k1_tarski(A_511),B_512)
      | ~ r1_tarski(A_511,B_512) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_7935])).

tff(c_9184,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(k1_ordinal1(A_26),B_27)
      | ~ r1_tarski(A_26,B_27)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_26,c_9103])).

tff(c_7620,plain,(
    ! [B_427,A_428] :
      ( r1_ordinal1(B_427,A_428)
      | r1_ordinal1(A_428,B_427)
      | ~ v3_ordinal1(B_427)
      | ~ v3_ordinal1(A_428) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7322,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_7623,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_7620,c_7322])).

tff(c_7629,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_7623])).

tff(c_7750,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_7629])).

tff(c_7753,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_7750])).

tff(c_7757,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_7753])).

tff(c_7759,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_7629])).

tff(c_7758,plain,(
    r1_ordinal1('#skF_2',k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_7629])).

tff(c_12,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(k2_xboole_0(A_8,C_10),B_9)
      | ~ r1_tarski(C_10,B_9)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7505,plain,(
    ! [B_415,A_416] :
      ( B_415 = A_416
      | ~ r1_tarski(B_415,A_416)
      | ~ r1_tarski(A_416,B_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8270,plain,(
    ! [A_481,B_482] :
      ( k2_xboole_0(A_481,B_482) = A_481
      | ~ r1_tarski(k2_xboole_0(A_481,B_482),A_481) ) ),
    inference(resolution,[status(thm)],[c_10,c_7505])).

tff(c_8274,plain,(
    ! [B_9,C_10] :
      ( k2_xboole_0(B_9,C_10) = B_9
      | ~ r1_tarski(C_10,B_9)
      | ~ r1_tarski(B_9,B_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_8270])).

tff(c_8291,plain,(
    ! [B_483,C_484] :
      ( k2_xboole_0(B_483,C_484) = B_483
      | ~ r1_tarski(C_484,B_483) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8274])).

tff(c_17067,plain,(
    ! [B_787,A_788] :
      ( k2_xboole_0(B_787,A_788) = B_787
      | ~ r1_ordinal1(A_788,B_787)
      | ~ v3_ordinal1(B_787)
      | ~ v3_ordinal1(A_788) ) ),
    inference(resolution,[status(thm)],[c_36,c_8291])).

tff(c_17085,plain,
    ( k2_xboole_0(k1_ordinal1('#skF_1'),'#skF_2') = k1_ordinal1('#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_7758,c_17067])).

tff(c_17107,plain,(
    k2_xboole_0(k1_ordinal1('#skF_1'),'#skF_2') = k1_ordinal1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_7759,c_17085])).

tff(c_34,plain,(
    ! [A_33,B_34] :
      ( r1_ordinal1(A_33,B_34)
      | ~ r1_tarski(A_33,B_34)
      | ~ v3_ordinal1(B_34)
      | ~ v3_ordinal1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7954,plain,(
    ! [A_445,C_446,B_447] :
      ( r1_ordinal1(k2_xboole_0(A_445,C_446),B_447)
      | ~ v3_ordinal1(B_447)
      | ~ v3_ordinal1(k2_xboole_0(A_445,C_446))
      | ~ r1_tarski(C_446,B_447)
      | ~ r1_tarski(A_445,B_447) ) ),
    inference(resolution,[status(thm)],[c_7935,c_34])).

tff(c_17290,plain,(
    ! [B_447] :
      ( r1_ordinal1(k1_ordinal1('#skF_1'),B_447)
      | ~ v3_ordinal1(B_447)
      | ~ v3_ordinal1(k2_xboole_0(k1_ordinal1('#skF_1'),'#skF_2'))
      | ~ r1_tarski('#skF_2',B_447)
      | ~ r1_tarski(k1_ordinal1('#skF_1'),B_447) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17107,c_7954])).

tff(c_17776,plain,(
    ! [B_796] :
      ( r1_ordinal1(k1_ordinal1('#skF_1'),B_796)
      | ~ v3_ordinal1(B_796)
      | ~ r1_tarski('#skF_2',B_796)
      | ~ r1_tarski(k1_ordinal1('#skF_1'),B_796) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7759,c_17107,c_17290])).

tff(c_19497,plain,(
    ! [B_837] :
      ( r1_ordinal1(k1_ordinal1('#skF_1'),B_837)
      | ~ v3_ordinal1(B_837)
      | ~ r1_tarski('#skF_2',B_837)
      | ~ r1_tarski('#skF_1',B_837)
      | ~ r2_hidden('#skF_1',B_837) ) ),
    inference(resolution,[status(thm)],[c_9184,c_17776])).

tff(c_19524,plain,
    ( ~ v3_ordinal1('#skF_2')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_19497,c_7322])).

tff(c_19547,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7323,c_6,c_46,c_19524])).

tff(c_19550,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_19547])).

tff(c_19554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_7745,c_19550])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:56:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.93/3.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.93/3.70  
% 9.93/3.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.93/3.70  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 9.93/3.70  
% 9.93/3.70  %Foreground sorts:
% 9.93/3.70  
% 9.93/3.70  
% 9.93/3.70  %Background operators:
% 9.93/3.70  
% 9.93/3.70  
% 9.93/3.70  %Foreground operators:
% 9.93/3.70  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 9.93/3.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.93/3.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.93/3.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.93/3.70  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.93/3.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.93/3.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.93/3.70  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 9.93/3.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.93/3.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.93/3.70  tff('#skF_2', type, '#skF_2': $i).
% 9.93/3.70  tff('#skF_1', type, '#skF_1': $i).
% 9.93/3.70  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 9.93/3.70  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.93/3.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.93/3.70  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.93/3.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.93/3.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.93/3.70  
% 9.93/3.71  tff(f_114, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 9.93/3.71  tff(f_67, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 9.93/3.71  tff(f_77, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 9.93/3.71  tff(f_99, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 9.93/3.71  tff(f_95, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 9.93/3.71  tff(f_104, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 9.93/3.71  tff(f_69, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 9.93/3.71  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 9.93/3.71  tff(f_80, axiom, (![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_ordinal1)).
% 9.93/3.71  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 9.93/3.71  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.93/3.71  tff(f_57, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 9.93/3.71  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 9.93/3.71  tff(c_48, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.93/3.71  tff(c_46, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.93/3.71  tff(c_30, plain, (![B_31, A_30]: (r1_ordinal1(B_31, A_30) | r1_ordinal1(A_30, B_31) | ~v3_ordinal1(B_31) | ~v3_ordinal1(A_30))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.93/3.71  tff(c_7682, plain, (![A_433, B_434]: (r1_tarski(A_433, B_434) | ~r1_ordinal1(A_433, B_434) | ~v3_ordinal1(B_434) | ~v3_ordinal1(A_433))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.93/3.71  tff(c_42, plain, (![A_39]: (v3_ordinal1(k1_ordinal1(A_39)) | ~v3_ordinal1(A_39))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.93/3.71  tff(c_874, plain, (![B_128, A_129]: (r2_hidden(B_128, A_129) | B_128=A_129 | r2_hidden(A_129, B_128) | ~v3_ordinal1(B_128) | ~v3_ordinal1(A_129))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.93/3.71  tff(c_44, plain, (![B_41, A_40]: (~r1_tarski(B_41, A_40) | ~r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.93/3.71  tff(c_2547, plain, (![B_204, A_205]: (~r1_tarski(B_204, A_205) | r2_hidden(B_204, A_205) | B_204=A_205 | ~v3_ordinal1(B_204) | ~v3_ordinal1(A_205))), inference(resolution, [status(thm)], [c_874, c_44])).
% 9.93/3.71  tff(c_50, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.93/3.71  tff(c_84, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 9.93/3.71  tff(c_2557, plain, (~r1_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1' | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_2547, c_84])).
% 9.93/3.71  tff(c_2565, plain, (~r1_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_2557])).
% 9.93/3.71  tff(c_2566, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_2565])).
% 9.93/3.71  tff(c_56, plain, (r2_hidden('#skF_1', '#skF_2') | r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.93/3.71  tff(c_133, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_84, c_56])).
% 9.93/3.71  tff(c_565, plain, (![A_105, B_106]: (r1_tarski(A_105, B_106) | ~r1_ordinal1(A_105, B_106) | ~v3_ordinal1(B_106) | ~v3_ordinal1(A_105))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.93/3.71  tff(c_32, plain, (![A_32]: (k2_xboole_0(A_32, k1_tarski(A_32))=k1_ordinal1(A_32))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.93/3.71  tff(c_227, plain, (![A_76, C_77, B_78]: (r1_tarski(A_76, C_77) | ~r1_tarski(k2_xboole_0(A_76, B_78), C_77))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.93/3.71  tff(c_241, plain, (![A_32, C_77]: (r1_tarski(A_32, C_77) | ~r1_tarski(k1_ordinal1(A_32), C_77))), inference(superposition, [status(thm), theory('equality')], [c_32, c_227])).
% 9.93/3.71  tff(c_7128, plain, (![A_376, B_377]: (r1_tarski(A_376, B_377) | ~r1_ordinal1(k1_ordinal1(A_376), B_377) | ~v3_ordinal1(B_377) | ~v3_ordinal1(k1_ordinal1(A_376)))), inference(resolution, [status(thm)], [c_565, c_241])).
% 9.93/3.71  tff(c_7158, plain, (r1_tarski('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_133, c_7128])).
% 9.93/3.71  tff(c_7170, plain, (r1_tarski('#skF_1', '#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_7158])).
% 9.93/3.71  tff(c_7171, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_2566, c_7170])).
% 9.93/3.71  tff(c_7174, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_42, c_7171])).
% 9.93/3.71  tff(c_7178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_7174])).
% 9.93/3.71  tff(c_7179, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_2565])).
% 9.93/3.71  tff(c_7181, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7179, c_133])).
% 9.93/3.71  tff(c_38, plain, (![A_35]: (k1_ordinal1(A_35)!=A_35)), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.93/3.71  tff(c_71, plain, (![A_49]: (k2_xboole_0(A_49, k1_tarski(A_49))=k1_ordinal1(A_49))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.93/3.71  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.93/3.71  tff(c_77, plain, (![A_49]: (r1_tarski(A_49, k1_ordinal1(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_71, c_10])).
% 9.93/3.71  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.93/3.71  tff(c_2296, plain, (![B_192, A_193]: (B_192=A_193 | ~r1_tarski(B_192, A_193) | ~r1_ordinal1(A_193, B_192) | ~v3_ordinal1(B_192) | ~v3_ordinal1(A_193))), inference(resolution, [status(thm)], [c_565, c_2])).
% 9.93/3.71  tff(c_2353, plain, (![A_49]: (k1_ordinal1(A_49)=A_49 | ~r1_ordinal1(k1_ordinal1(A_49), A_49) | ~v3_ordinal1(A_49) | ~v3_ordinal1(k1_ordinal1(A_49)))), inference(resolution, [status(thm)], [c_77, c_2296])).
% 9.93/3.72  tff(c_7297, plain, (![A_384]: (~r1_ordinal1(k1_ordinal1(A_384), A_384) | ~v3_ordinal1(A_384) | ~v3_ordinal1(k1_ordinal1(A_384)))), inference(negUnitSimplification, [status(thm)], [c_38, c_2353])).
% 9.93/3.72  tff(c_7300, plain, (~v3_ordinal1('#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_7181, c_7297])).
% 9.93/3.72  tff(c_7311, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_7300])).
% 9.93/3.72  tff(c_7317, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_42, c_7311])).
% 9.93/3.72  tff(c_7321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_7317])).
% 9.93/3.72  tff(c_7323, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 9.93/3.72  tff(c_7326, plain, (![B_387, A_388]: (~r1_tarski(B_387, A_388) | ~r2_hidden(A_388, B_387))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.93/3.72  tff(c_7330, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_7323, c_7326])).
% 9.93/3.72  tff(c_7723, plain, (~r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_7682, c_7330])).
% 9.93/3.72  tff(c_7736, plain, (~r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_7723])).
% 9.93/3.72  tff(c_7739, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_30, c_7736])).
% 9.93/3.72  tff(c_7745, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_7739])).
% 9.93/3.72  tff(c_36, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~r1_ordinal1(A_33, B_34) | ~v3_ordinal1(B_34) | ~v3_ordinal1(A_33))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.93/3.72  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.93/3.72  tff(c_26, plain, (![A_26, B_27]: (r1_tarski(k1_tarski(A_26), B_27) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.93/3.72  tff(c_7935, plain, (![A_445, C_446, B_447]: (r1_tarski(k2_xboole_0(A_445, C_446), B_447) | ~r1_tarski(C_446, B_447) | ~r1_tarski(A_445, B_447))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.93/3.72  tff(c_9103, plain, (![A_511, B_512]: (r1_tarski(k1_ordinal1(A_511), B_512) | ~r1_tarski(k1_tarski(A_511), B_512) | ~r1_tarski(A_511, B_512))), inference(superposition, [status(thm), theory('equality')], [c_32, c_7935])).
% 9.93/3.72  tff(c_9184, plain, (![A_26, B_27]: (r1_tarski(k1_ordinal1(A_26), B_27) | ~r1_tarski(A_26, B_27) | ~r2_hidden(A_26, B_27))), inference(resolution, [status(thm)], [c_26, c_9103])).
% 9.93/3.72  tff(c_7620, plain, (![B_427, A_428]: (r1_ordinal1(B_427, A_428) | r1_ordinal1(A_428, B_427) | ~v3_ordinal1(B_427) | ~v3_ordinal1(A_428))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.93/3.72  tff(c_7322, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 9.93/3.72  tff(c_7623, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_7620, c_7322])).
% 9.93/3.72  tff(c_7629, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_7623])).
% 9.93/3.72  tff(c_7750, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_7629])).
% 9.93/3.72  tff(c_7753, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_42, c_7750])).
% 9.93/3.72  tff(c_7757, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_7753])).
% 9.93/3.72  tff(c_7759, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_7629])).
% 9.93/3.72  tff(c_7758, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_7629])).
% 9.93/3.72  tff(c_12, plain, (![A_8, C_10, B_9]: (r1_tarski(k2_xboole_0(A_8, C_10), B_9) | ~r1_tarski(C_10, B_9) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.93/3.72  tff(c_7505, plain, (![B_415, A_416]: (B_415=A_416 | ~r1_tarski(B_415, A_416) | ~r1_tarski(A_416, B_415))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.93/3.72  tff(c_8270, plain, (![A_481, B_482]: (k2_xboole_0(A_481, B_482)=A_481 | ~r1_tarski(k2_xboole_0(A_481, B_482), A_481))), inference(resolution, [status(thm)], [c_10, c_7505])).
% 9.93/3.72  tff(c_8274, plain, (![B_9, C_10]: (k2_xboole_0(B_9, C_10)=B_9 | ~r1_tarski(C_10, B_9) | ~r1_tarski(B_9, B_9))), inference(resolution, [status(thm)], [c_12, c_8270])).
% 9.93/3.72  tff(c_8291, plain, (![B_483, C_484]: (k2_xboole_0(B_483, C_484)=B_483 | ~r1_tarski(C_484, B_483))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8274])).
% 9.93/3.72  tff(c_17067, plain, (![B_787, A_788]: (k2_xboole_0(B_787, A_788)=B_787 | ~r1_ordinal1(A_788, B_787) | ~v3_ordinal1(B_787) | ~v3_ordinal1(A_788))), inference(resolution, [status(thm)], [c_36, c_8291])).
% 9.93/3.72  tff(c_17085, plain, (k2_xboole_0(k1_ordinal1('#skF_1'), '#skF_2')=k1_ordinal1('#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_7758, c_17067])).
% 9.93/3.72  tff(c_17107, plain, (k2_xboole_0(k1_ordinal1('#skF_1'), '#skF_2')=k1_ordinal1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_7759, c_17085])).
% 9.93/3.72  tff(c_34, plain, (![A_33, B_34]: (r1_ordinal1(A_33, B_34) | ~r1_tarski(A_33, B_34) | ~v3_ordinal1(B_34) | ~v3_ordinal1(A_33))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.93/3.72  tff(c_7954, plain, (![A_445, C_446, B_447]: (r1_ordinal1(k2_xboole_0(A_445, C_446), B_447) | ~v3_ordinal1(B_447) | ~v3_ordinal1(k2_xboole_0(A_445, C_446)) | ~r1_tarski(C_446, B_447) | ~r1_tarski(A_445, B_447))), inference(resolution, [status(thm)], [c_7935, c_34])).
% 9.93/3.72  tff(c_17290, plain, (![B_447]: (r1_ordinal1(k1_ordinal1('#skF_1'), B_447) | ~v3_ordinal1(B_447) | ~v3_ordinal1(k2_xboole_0(k1_ordinal1('#skF_1'), '#skF_2')) | ~r1_tarski('#skF_2', B_447) | ~r1_tarski(k1_ordinal1('#skF_1'), B_447))), inference(superposition, [status(thm), theory('equality')], [c_17107, c_7954])).
% 9.93/3.72  tff(c_17776, plain, (![B_796]: (r1_ordinal1(k1_ordinal1('#skF_1'), B_796) | ~v3_ordinal1(B_796) | ~r1_tarski('#skF_2', B_796) | ~r1_tarski(k1_ordinal1('#skF_1'), B_796))), inference(demodulation, [status(thm), theory('equality')], [c_7759, c_17107, c_17290])).
% 9.93/3.72  tff(c_19497, plain, (![B_837]: (r1_ordinal1(k1_ordinal1('#skF_1'), B_837) | ~v3_ordinal1(B_837) | ~r1_tarski('#skF_2', B_837) | ~r1_tarski('#skF_1', B_837) | ~r2_hidden('#skF_1', B_837))), inference(resolution, [status(thm)], [c_9184, c_17776])).
% 9.93/3.72  tff(c_19524, plain, (~v3_ordinal1('#skF_2') | ~r1_tarski('#skF_2', '#skF_2') | ~r1_tarski('#skF_1', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_19497, c_7322])).
% 9.93/3.72  tff(c_19547, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7323, c_6, c_46, c_19524])).
% 9.93/3.72  tff(c_19550, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_36, c_19547])).
% 9.93/3.72  tff(c_19554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_7745, c_19550])).
% 9.93/3.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.93/3.72  
% 9.93/3.72  Inference rules
% 9.93/3.72  ----------------------
% 9.93/3.72  #Ref     : 0
% 9.93/3.72  #Sup     : 4189
% 9.93/3.72  #Fact    : 8
% 9.93/3.72  #Define  : 0
% 9.93/3.72  #Split   : 5
% 9.93/3.72  #Chain   : 0
% 9.93/3.72  #Close   : 0
% 9.93/3.72  
% 9.93/3.72  Ordering : KBO
% 9.93/3.72  
% 9.93/3.72  Simplification rules
% 9.93/3.72  ----------------------
% 9.93/3.72  #Subsume      : 637
% 9.93/3.72  #Demod        : 2510
% 9.93/3.72  #Tautology    : 2137
% 9.93/3.72  #SimpNegUnit  : 39
% 9.93/3.72  #BackRed      : 33
% 9.93/3.72  
% 9.93/3.72  #Partial instantiations: 0
% 9.93/3.72  #Strategies tried      : 1
% 9.93/3.72  
% 9.93/3.72  Timing (in seconds)
% 9.93/3.72  ----------------------
% 9.93/3.72  Preprocessing        : 0.41
% 9.93/3.72  Parsing              : 0.22
% 9.93/3.72  CNF conversion       : 0.02
% 9.93/3.72  Main loop            : 2.43
% 9.93/3.72  Inferencing          : 0.64
% 9.93/3.72  Reduction            : 1.04
% 9.93/3.72  Demodulation         : 0.81
% 9.93/3.72  BG Simplification    : 0.07
% 9.93/3.72  Subsumption          : 0.54
% 9.93/3.72  Abstraction          : 0.10
% 9.93/3.72  MUC search           : 0.00
% 9.93/3.72  Cooper               : 0.00
% 9.93/3.72  Total                : 2.88
% 10.08/3.72  Index Insertion      : 0.00
% 10.08/3.72  Index Deletion       : 0.00
% 10.08/3.72  Index Matching       : 0.00
% 10.08/3.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
