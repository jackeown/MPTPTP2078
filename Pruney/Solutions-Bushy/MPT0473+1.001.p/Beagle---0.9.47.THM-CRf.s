%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0473+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:22 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   32 (  87 expanded)
%              Number of leaves         :   11 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 ( 162 expanded)
%              Number of equality atoms :   31 ( 125 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k1_relat_1(A) = k1_xboole_0
        <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_27,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_12,plain,
    ( k2_relat_1('#skF_1') != k1_xboole_0
    | k1_relat_1('#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_27,plain,(
    k1_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_18,plain,
    ( k1_relat_1('#skF_1') = k1_xboole_0
    | k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_27,c_18])).

tff(c_10,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_33,plain,(
    ! [A_2] :
      ( k2_relat_1(A_2) != k1_xboole_0
      | k1_xboole_0 = A_2
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,
    ( k2_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10,c_33])).

tff(c_39,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_36])).

tff(c_42,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_27])).

tff(c_4,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_43,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_39,c_4])).

tff(c_54,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_43])).

tff(c_56,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_63,plain,(
    ! [A_3] :
      ( k1_relat_1(A_3) != k1_xboole_0
      | k1_xboole_0 = A_3
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,
    ( k1_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10,c_63])).

tff(c_69,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_66])).

tff(c_55,plain,(
    k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_72,plain,(
    k2_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_55])).

tff(c_2,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_74,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_69,c_2])).

tff(c_90,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_74])).

%------------------------------------------------------------------------------
