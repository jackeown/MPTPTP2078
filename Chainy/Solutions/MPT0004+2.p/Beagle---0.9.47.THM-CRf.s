%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0004+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:09 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 184 expanded)
%              Number of leaves         :   38 (  81 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 ( 250 expanded)
%              Number of equality atoms :   19 (  71 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_18 > #skF_17 > #skF_6 > #skF_15 > #skF_1 > #skF_12 > #skF_19 > #skF_4 > #skF_16 > #skF_14 > #skF_5 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_18',type,(
    '#skF_18': $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_17',type,(
    '#skF_17': $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_19',type,(
    '#skF_19': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_14',type,(
    '#skF_14': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_90,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_154,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ ( ~ r1_xboole_0(A,B)
            & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
        & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_97,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_96,plain,(
    v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    ! [B_6,A_5] : k3_xboole_0(B_6,A_5) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_192,plain,(
    ! [A_62] :
      ( k1_xboole_0 = A_62
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_201,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_96,c_192])).

tff(c_74,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(A_33,B_34)
      | k3_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_335,plain,(
    ! [A_80,B_81] :
      ( r1_xboole_0(A_80,B_81)
      | k3_xboole_0(A_80,B_81) != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_74])).

tff(c_162,plain,
    ( r1_xboole_0('#skF_15','#skF_16')
    | ~ r1_xboole_0('#skF_18','#skF_19') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_214,plain,(
    ~ r1_xboole_0('#skF_18','#skF_19') ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_343,plain,(
    k3_xboole_0('#skF_18','#skF_19') != '#skF_8' ),
    inference(resolution,[status(thm)],[c_335,c_214])).

tff(c_347,plain,(
    k3_xboole_0('#skF_19','#skF_18') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_343])).

tff(c_12,plain,(
    ! [A_9] :
      ( v1_xboole_0(A_9)
      | r2_hidden('#skF_1'(A_9),A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_158,plain,(
    ! [C_59] :
      ( r1_xboole_0('#skF_15','#skF_16')
      | ~ r2_hidden(C_59,k3_xboole_0('#skF_18','#skF_19')) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_168,plain,(
    ! [C_59] :
      ( r1_xboole_0('#skF_15','#skF_16')
      | ~ r2_hidden(C_59,k3_xboole_0('#skF_19','#skF_18')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_158])).

tff(c_392,plain,(
    ! [C_93] : ~ r2_hidden(C_93,k3_xboole_0('#skF_19','#skF_18')) ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_397,plain,(
    v1_xboole_0(k3_xboole_0('#skF_19','#skF_18')) ),
    inference(resolution,[status(thm)],[c_12,c_392])).

tff(c_94,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_202,plain,(
    ! [A_39] :
      ( A_39 = '#skF_8'
      | ~ v1_xboole_0(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_94])).

tff(c_400,plain,(
    k3_xboole_0('#skF_19','#skF_18') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_397,c_202])).

tff(c_404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_347,c_400])).

tff(c_405,plain,(
    r1_xboole_0('#skF_15','#skF_16') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_100,plain,(
    ! [B_41,A_40] :
      ( r1_xboole_0(B_41,A_40)
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_412,plain,(
    r1_xboole_0('#skF_16','#skF_15') ),
    inference(resolution,[status(thm)],[c_405,c_100])).

tff(c_72,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_xboole_0(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_332,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = '#skF_8'
      | ~ r1_xboole_0(A_33,B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_72])).

tff(c_418,plain,(
    k3_xboole_0('#skF_16','#skF_15') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_412,c_332])).

tff(c_160,plain,(
    ! [C_59] :
      ( r2_hidden('#skF_17',k3_xboole_0('#skF_15','#skF_16'))
      | ~ r2_hidden(C_59,k3_xboole_0('#skF_18','#skF_19')) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_167,plain,(
    ! [C_59] :
      ( r2_hidden('#skF_17',k3_xboole_0('#skF_16','#skF_15'))
      | ~ r2_hidden(C_59,k3_xboole_0('#skF_19','#skF_18')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_160])).

tff(c_451,plain,(
    ! [C_59] :
      ( r2_hidden('#skF_17','#skF_8')
      | ~ r2_hidden(C_59,k3_xboole_0('#skF_19','#skF_18')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_167])).

tff(c_505,plain,(
    ! [C_103] : ~ r2_hidden(C_103,k3_xboole_0('#skF_19','#skF_18')) ),
    inference(splitLeft,[status(thm)],[c_451])).

tff(c_515,plain,(
    v1_xboole_0(k3_xboole_0('#skF_19','#skF_18')) ),
    inference(resolution,[status(thm)],[c_12,c_505])).

tff(c_518,plain,(
    k3_xboole_0('#skF_19','#skF_18') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_515,c_202])).

tff(c_522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_347,c_518])).

tff(c_523,plain,(
    r2_hidden('#skF_17','#skF_8') ),
    inference(splitRight,[status(thm)],[c_451])).

tff(c_10,plain,(
    ! [B_12,A_9] :
      ( ~ r2_hidden(B_12,A_9)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_528,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_523,c_10])).

tff(c_533,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_528])).

tff(c_534,plain,(
    r1_xboole_0('#skF_15','#skF_16') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_543,plain,(
    ! [B_107,A_108] :
      ( r1_xboole_0(B_107,A_108)
      | ~ r1_xboole_0(A_108,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_549,plain,(
    r1_xboole_0('#skF_16','#skF_15') ),
    inference(resolution,[status(thm)],[c_534,c_543])).

tff(c_682,plain,(
    ! [A_121,B_122] :
      ( k3_xboole_0(A_121,B_122) = '#skF_8'
      | ~ r1_xboole_0(A_121,B_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_72])).

tff(c_699,plain,(
    k3_xboole_0('#skF_16','#skF_15') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_549,c_682])).

tff(c_535,plain,(
    r1_xboole_0('#skF_18','#skF_19') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_164,plain,
    ( r2_hidden('#skF_17',k3_xboole_0('#skF_15','#skF_16'))
    | ~ r1_xboole_0('#skF_18','#skF_19') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_169,plain,
    ( r2_hidden('#skF_17',k3_xboole_0('#skF_16','#skF_15'))
    | ~ r1_xboole_0('#skF_18','#skF_19') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_164])).

tff(c_625,plain,(
    r2_hidden('#skF_17',k3_xboole_0('#skF_16','#skF_15')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_169])).

tff(c_629,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_16','#skF_15')) ),
    inference(resolution,[status(thm)],[c_625,c_10])).

tff(c_704,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_629])).

tff(c_708,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_704])).
%------------------------------------------------------------------------------
