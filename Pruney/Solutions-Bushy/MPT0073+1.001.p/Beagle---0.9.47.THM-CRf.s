%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0073+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:40 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   42 (  85 expanded)
%              Number of leaves         :   11 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 ( 148 expanded)
%              Number of equality atoms :   27 (  90 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_30,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_43,negated_conjecture,(
    ~ ! [A] :
        ( ~ ( ~ r1_xboole_0(A,A)
            & A = k1_xboole_0 )
        & ~ ( A != k1_xboole_0
            & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,
    ( k1_xboole_0 != '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_15,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_10])).

tff(c_8,plain,
    ( r1_xboole_0('#skF_1','#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_25,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_26,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_15])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_34,plain,(
    ! [A_6,B_7] :
      ( r1_xboole_0(A_6,B_7)
      | k3_xboole_0(A_6,B_7) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_4])).

tff(c_12,plain,
    ( r1_xboole_0('#skF_1','#skF_1')
    | ~ r1_xboole_0('#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    ~ r1_xboole_0('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_37,plain,(
    k3_xboole_0('#skF_2','#skF_2') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_32])).

tff(c_41,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_37])).

tff(c_42,plain,(
    r1_xboole_0('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_47,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = '#skF_2'
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_2])).

tff(c_56,plain,(
    k3_xboole_0('#skF_1','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_47])).

tff(c_61,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_56])).

tff(c_63,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_61])).

tff(c_64,plain,(
    r1_xboole_0('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_68,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_74,plain,(
    k3_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_68])).

tff(c_77,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_74])).

tff(c_79,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15,c_77])).

tff(c_81,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_110,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k3_xboole_0(A_17,B_18) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_4])).

tff(c_80,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_86,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_80])).

tff(c_14,plain,
    ( k1_xboole_0 != '#skF_1'
    | ~ r1_xboole_0('#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_106,plain,(
    ~ r1_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_86,c_81,c_14])).

tff(c_113,plain,(
    k3_xboole_0('#skF_1','#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_110,c_106])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_113])).

%------------------------------------------------------------------------------
