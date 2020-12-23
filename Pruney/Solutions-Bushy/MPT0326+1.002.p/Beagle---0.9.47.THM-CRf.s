%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0326+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:06 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 118 expanded)
%              Number of leaves         :   18 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 224 expanded)
%              Number of equality atoms :   29 (  70 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_53,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B,C,D] :
            ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
              | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
           => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_25,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_22,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3'))
    | r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_62,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_63,plain,(
    ! [A_16,C_17,B_18,D_19] :
      ( r1_tarski(A_16,C_17)
      | k2_zfmisc_1(A_16,B_18) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_16,B_18),k2_zfmisc_1(C_17,D_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_79,plain,
    ( r1_tarski('#skF_1','#skF_3')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_63])).

tff(c_84,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_6,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_101,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_6])).

tff(c_103,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_2,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_25])).

tff(c_4,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_23,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_110,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_23])).

tff(c_113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_110])).

tff(c_114,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_16,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_148,plain,(
    ! [A_7] : r1_tarski('#skF_2',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_16])).

tff(c_18,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_18])).

tff(c_167,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_168,plain,(
    ! [B_24,D_25,A_26,C_27] :
      ( r1_tarski(B_24,D_25)
      | k2_zfmisc_1(A_26,B_24) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_26,B_24),k2_zfmisc_1(C_27,D_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_171,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_168])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_18,c_171])).

tff(c_188,plain,(
    r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_190,plain,(
    ! [B_28,D_29,A_30,C_31] :
      ( r1_tarski(B_28,D_29)
      | k2_zfmisc_1(A_30,B_28) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_30,B_28),k2_zfmisc_1(C_31,D_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_206,plain,
    ( r1_tarski('#skF_1','#skF_3')
    | k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_188,c_190])).

tff(c_211,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_228,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_6])).

tff(c_230,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_236,plain,(
    ! [A_7] : r1_tarski('#skF_2',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_16])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_18])).

tff(c_252,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_261,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_23])).

tff(c_264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_261])).

tff(c_266,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_287,plain,(
    ! [A_41,C_42,B_43,D_44] :
      ( r1_tarski(A_41,C_42)
      | k2_zfmisc_1(A_41,B_43) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_41,B_43),k2_zfmisc_1(C_42,D_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_290,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_188,c_287])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_18,c_290])).

%------------------------------------------------------------------------------
