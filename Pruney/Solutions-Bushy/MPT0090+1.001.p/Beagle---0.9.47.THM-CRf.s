%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0090+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:42 EST 2020

% Result     : Theorem 8.99s
% Output     : CNFRefutation 8.99s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 529 expanded)
%              Number of leaves         :   23 ( 171 expanded)
%              Depth                    :   15
%              Number of atoms          :  165 (1108 expanded)
%              Number of equality atoms :   33 ( 325 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_56,plain,
    ( ~ r1_xboole_0('#skF_6','#skF_7')
    | r1_xboole_0('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_69,plain,(
    ~ r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_7956,plain,(
    ! [A_357,B_358] :
      ( r2_hidden('#skF_5'(A_357,B_358),k3_xboole_0(A_357,B_358))
      | r1_xboole_0(A_357,B_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7973,plain,(
    ! [A_357,B_358] :
      ( r2_hidden('#skF_5'(A_357,B_358),A_357)
      | r1_xboole_0(A_357,B_358) ) ),
    inference(resolution,[status(thm)],[c_7956,c_8])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7986,plain,(
    ! [A_362,B_363] :
      ( r2_hidden('#skF_5'(A_362,B_363),B_363)
      | r1_xboole_0(A_362,B_363) ) ),
    inference(resolution,[status(thm)],[c_7956,c_6])).

tff(c_7387,plain,(
    ! [A_300,B_301] :
      ( r2_hidden('#skF_5'(A_300,B_301),k3_xboole_0(A_300,B_301))
      | r1_xboole_0(A_300,B_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_7415,plain,(
    ! [A_300,B_301] :
      ( r2_hidden('#skF_5'(A_300,B_301),B_301)
      | r1_xboole_0(A_300,B_301) ) ),
    inference(resolution,[status(thm)],[c_7387,c_6])).

tff(c_7420,plain,(
    ! [A_302,B_303] :
      ( r2_hidden('#skF_5'(A_302,B_303),A_302)
      | r1_xboole_0(A_302,B_303) ) ),
    inference(resolution,[status(thm)],[c_7387,c_8])).

tff(c_54,plain,
    ( k4_xboole_0('#skF_6','#skF_7') = '#skF_6'
    | k4_xboole_0('#skF_8','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_201,plain,(
    k4_xboole_0('#skF_8','#skF_9') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_38,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden('#skF_3'(A_9,B_10,C_11),A_9)
      | r2_hidden('#skF_4'(A_9,B_10,C_11),C_11)
      | k4_xboole_0(A_9,B_10) = C_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5016,plain,(
    ! [A_237,B_238,C_239] :
      ( r2_hidden('#skF_3'(A_237,B_238,C_239),A_237)
      | r2_hidden('#skF_4'(A_237,B_238,C_239),B_238)
      | ~ r2_hidden('#skF_4'(A_237,B_238,C_239),A_237)
      | k4_xboole_0(A_237,B_238) = C_239 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5609,plain,(
    ! [C_252,B_253] :
      ( r2_hidden('#skF_4'(C_252,B_253,C_252),B_253)
      | r2_hidden('#skF_3'(C_252,B_253,C_252),C_252)
      | k4_xboole_0(C_252,B_253) = C_252 ) ),
    inference(resolution,[status(thm)],[c_38,c_5016])).

tff(c_58,plain,
    ( k4_xboole_0('#skF_6','#skF_7') = '#skF_6'
    | r1_xboole_0('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_103,plain,(
    r1_xboole_0('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_119,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_131,plain,(
    k3_xboole_0('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_103,c_119])).

tff(c_184,plain,(
    ! [A_41,B_42,C_43] :
      ( ~ r1_xboole_0(A_41,B_42)
      | ~ r2_hidden(C_43,k3_xboole_0(A_41,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_190,plain,(
    ! [C_43] :
      ( ~ r1_xboole_0('#skF_8','#skF_9')
      | ~ r2_hidden(C_43,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_184])).

tff(c_200,plain,(
    ! [C_43] : ~ r2_hidden(C_43,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_190])).

tff(c_370,plain,(
    ! [D_64,A_65,B_66] :
      ( r2_hidden(D_64,k3_xboole_0(A_65,B_66))
      | ~ r2_hidden(D_64,B_66)
      | ~ r2_hidden(D_64,A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_391,plain,(
    ! [D_64] :
      ( r2_hidden(D_64,k1_xboole_0)
      | ~ r2_hidden(D_64,'#skF_9')
      | ~ r2_hidden(D_64,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_370])).

tff(c_404,plain,(
    ! [D_64] :
      ( ~ r2_hidden(D_64,'#skF_9')
      | ~ r2_hidden(D_64,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_391])).

tff(c_6005,plain,(
    ! [C_256] :
      ( ~ r2_hidden('#skF_4'(C_256,'#skF_9',C_256),'#skF_8')
      | r2_hidden('#skF_3'(C_256,'#skF_9',C_256),C_256)
      | k4_xboole_0(C_256,'#skF_9') = C_256 ) ),
    inference(resolution,[status(thm)],[c_5609,c_404])).

tff(c_6011,plain,
    ( r2_hidden('#skF_3'('#skF_8','#skF_9','#skF_8'),'#skF_8')
    | k4_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_38,c_6005])).

tff(c_6017,plain,(
    r2_hidden('#skF_3'('#skF_8','#skF_9','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_201,c_6011])).

tff(c_34,plain,(
    ! [A_9,B_10,C_11] :
      ( ~ r2_hidden('#skF_3'(A_9,B_10,C_11),C_11)
      | r2_hidden('#skF_4'(A_9,B_10,C_11),C_11)
      | k4_xboole_0(A_9,B_10) = C_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ! [A_9,B_10,C_11] :
      ( ~ r2_hidden('#skF_3'(A_9,B_10,C_11),C_11)
      | r2_hidden('#skF_4'(A_9,B_10,C_11),B_10)
      | ~ r2_hidden('#skF_4'(A_9,B_10,C_11),A_9)
      | k4_xboole_0(A_9,B_10) = C_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6286,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_9','#skF_8'),'#skF_9')
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_9','#skF_8'),'#skF_8')
    | k4_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_6017,c_28])).

tff(c_6294,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_9','#skF_8'),'#skF_9')
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_9','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_6286])).

tff(c_6750,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_9','#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_6294])).

tff(c_6753,plain,
    ( ~ r2_hidden('#skF_3'('#skF_8','#skF_9','#skF_8'),'#skF_8')
    | k4_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_34,c_6750])).

tff(c_6759,plain,(
    k4_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6017,c_6753])).

tff(c_6761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_6759])).

tff(c_6763,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_9','#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_6294])).

tff(c_6762,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_9','#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_6294])).

tff(c_6777,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_9','#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_6762,c_404])).

tff(c_7323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6763,c_6777])).

tff(c_7324,plain,(
    k4_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_7335,plain,(
    ! [D_286,B_287,A_288] :
      ( ~ r2_hidden(D_286,B_287)
      | ~ r2_hidden(D_286,k4_xboole_0(A_288,B_287)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7341,plain,(
    ! [D_286] :
      ( ~ r2_hidden(D_286,'#skF_7')
      | ~ r2_hidden(D_286,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7324,c_7335])).

tff(c_7861,plain,(
    ! [B_332] :
      ( ~ r2_hidden('#skF_5'('#skF_7',B_332),'#skF_6')
      | r1_xboole_0('#skF_7',B_332) ) ),
    inference(resolution,[status(thm)],[c_7420,c_7341])).

tff(c_7866,plain,(
    r1_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_7415,c_7861])).

tff(c_44,plain,(
    ! [B_18,A_17] :
      ( r1_xboole_0(B_18,A_17)
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_7871,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_7866,c_44])).

tff(c_7876,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_7871])).

tff(c_7877,plain,(
    k4_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_7932,plain,(
    ! [D_345,B_346,A_347] :
      ( ~ r2_hidden(D_345,B_346)
      | ~ r2_hidden(D_345,k4_xboole_0(A_347,B_346)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7935,plain,(
    ! [D_345] :
      ( ~ r2_hidden(D_345,'#skF_7')
      | ~ r2_hidden(D_345,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7877,c_7932])).

tff(c_8116,plain,(
    ! [A_374] :
      ( ~ r2_hidden('#skF_5'(A_374,'#skF_7'),'#skF_6')
      | r1_xboole_0(A_374,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_7986,c_7935])).

tff(c_8120,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_7973,c_8116])).

tff(c_8124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_69,c_8120])).

tff(c_8126,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_52,plain,
    ( ~ r1_xboole_0('#skF_6','#skF_7')
    | k4_xboole_0('#skF_8','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8201,plain,(
    k4_xboole_0('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8126,c_52])).

tff(c_10208,plain,(
    ! [A_491,B_492,C_493] :
      ( r2_hidden('#skF_3'(A_491,B_492,C_493),A_491)
      | r2_hidden('#skF_4'(A_491,B_492,C_493),B_492)
      | ~ r2_hidden('#skF_4'(A_491,B_492,C_493),A_491)
      | k4_xboole_0(A_491,B_492) = C_493 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_13343,plain,(
    ! [C_591,B_592] :
      ( r2_hidden('#skF_4'(C_591,B_592,C_591),B_592)
      | r2_hidden('#skF_3'(C_591,B_592,C_591),C_591)
      | k4_xboole_0(C_591,B_592) = C_591 ) ),
    inference(resolution,[status(thm)],[c_38,c_10208])).

tff(c_8125,plain,(
    r1_xboole_0('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_8175,plain,(
    ! [A_377,B_378] :
      ( k3_xboole_0(A_377,B_378) = k1_xboole_0
      | ~ r1_xboole_0(A_377,B_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8191,plain,(
    k3_xboole_0('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8125,c_8175])).

tff(c_8277,plain,(
    ! [A_386,B_387,C_388] :
      ( ~ r1_xboole_0(A_386,B_387)
      | ~ r2_hidden(C_388,k3_xboole_0(A_386,B_387)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8286,plain,(
    ! [C_388] :
      ( ~ r1_xboole_0('#skF_8','#skF_9')
      | ~ r2_hidden(C_388,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8191,c_8277])).

tff(c_8301,plain,(
    ! [C_388] : ~ r2_hidden(C_388,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8125,c_8286])).

tff(c_8446,plain,(
    ! [D_407,A_408,B_409] :
      ( r2_hidden(D_407,k3_xboole_0(A_408,B_409))
      | ~ r2_hidden(D_407,B_409)
      | ~ r2_hidden(D_407,A_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8467,plain,(
    ! [D_407] :
      ( r2_hidden(D_407,k1_xboole_0)
      | ~ r2_hidden(D_407,'#skF_9')
      | ~ r2_hidden(D_407,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8191,c_8446])).

tff(c_8483,plain,(
    ! [D_407] :
      ( ~ r2_hidden(D_407,'#skF_9')
      | ~ r2_hidden(D_407,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_8301,c_8467])).

tff(c_13919,plain,(
    ! [C_597] :
      ( ~ r2_hidden('#skF_4'(C_597,'#skF_9',C_597),'#skF_8')
      | r2_hidden('#skF_3'(C_597,'#skF_9',C_597),C_597)
      | k4_xboole_0(C_597,'#skF_9') = C_597 ) ),
    inference(resolution,[status(thm)],[c_13343,c_8483])).

tff(c_13922,plain,
    ( r2_hidden('#skF_3'('#skF_8','#skF_9','#skF_8'),'#skF_8')
    | k4_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_38,c_13919])).

tff(c_13928,plain,(
    r2_hidden('#skF_3'('#skF_8','#skF_9','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_8201,c_8201,c_13922])).

tff(c_13940,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_9','#skF_8'),'#skF_9')
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_9','#skF_8'),'#skF_8')
    | k4_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_13928,c_28])).

tff(c_13946,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_9','#skF_8'),'#skF_9')
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_9','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_8201,c_13940])).

tff(c_14614,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_9','#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_13946])).

tff(c_14620,plain,
    ( ~ r2_hidden('#skF_3'('#skF_8','#skF_9','#skF_8'),'#skF_8')
    | k4_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_34,c_14614])).

tff(c_14626,plain,(
    k4_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13928,c_14620])).

tff(c_14628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8201,c_14626])).

tff(c_14630,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_9','#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_13946])).

tff(c_14629,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_9','#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_13946])).

tff(c_14644,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_9','#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_14629,c_8483])).

tff(c_14671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14630,c_14644])).

%------------------------------------------------------------------------------
