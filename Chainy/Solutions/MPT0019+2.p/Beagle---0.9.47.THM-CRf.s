%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0019+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:09 EST 2020

% Result     : Theorem 6.33s
% Output     : CNFRefutation 6.33s
% Verified   : 
% Statistics : Number of formulae       :   53 (  54 expanded)
%              Number of leaves         :   40 (  41 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  32 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_20 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_19 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_9 > #skF_7 > #skF_14 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_20',type,(
    '#skF_20': $i )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_19',type,(
    '#skF_19': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff(f_267,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_298,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_125,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',idempotence_k2_xboole_0)).

tff(f_316,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_242,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_206,plain,(
    k2_xboole_0('#skF_19','#skF_20') != '#skF_20' ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_208,plain,(
    r1_tarski('#skF_19','#skF_20') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_348,plain,(
    ! [B_142,A_143] : k2_xboole_0(B_142,A_143) = k2_xboole_0(A_143,B_142) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_228,plain,(
    ! [A_110,B_111] : r1_tarski(A_110,k2_xboole_0(A_110,B_111)) ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_369,plain,(
    ! [A_143,B_142] : r1_tarski(A_143,k2_xboole_0(B_142,A_143)) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_228])).

tff(c_104,plain,(
    ! [A_44] : k2_xboole_0(A_44,A_44) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2224,plain,(
    ! [A_318,C_319,B_320] :
      ( r1_tarski(k2_xboole_0(A_318,C_319),k2_xboole_0(B_320,C_319))
      | ~ r1_tarski(A_318,B_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_316])).

tff(c_2930,plain,(
    ! [A_341,A_342] :
      ( r1_tarski(k2_xboole_0(A_341,A_342),A_342)
      | ~ r1_tarski(A_341,A_342) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_2224])).

tff(c_192,plain,(
    ! [B_82,A_81] :
      ( B_82 = A_81
      | ~ r1_tarski(B_82,A_81)
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_2951,plain,(
    ! [A_341,A_342] :
      ( k2_xboole_0(A_341,A_342) = A_342
      | ~ r1_tarski(A_342,k2_xboole_0(A_341,A_342))
      | ~ r1_tarski(A_341,A_342) ) ),
    inference(resolution,[status(thm)],[c_2930,c_192])).

tff(c_3010,plain,(
    ! [A_343,A_344] :
      ( k2_xboole_0(A_343,A_344) = A_344
      | ~ r1_tarski(A_343,A_344) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_2951])).

tff(c_3049,plain,(
    k2_xboole_0('#skF_19','#skF_20') = '#skF_20' ),
    inference(resolution,[status(thm)],[c_208,c_3010])).

tff(c_3071,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_3049])).
%------------------------------------------------------------------------------
