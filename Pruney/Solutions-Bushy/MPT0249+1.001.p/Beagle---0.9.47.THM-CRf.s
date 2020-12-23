%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0249+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:58 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   26 (  50 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   36 ( 112 expanded)
%              Number of equality atoms :   35 ( 111 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(c_22,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_29,plain,(
    ! [A_4,C_5,B_6] :
      ( k1_tarski(A_4) = C_5
      | k1_xboole_0 = C_5
      | k2_xboole_0(B_6,C_5) != k1_tarski(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_32,plain,(
    ! [A_4] :
      ( k1_tarski(A_4) = '#skF_3'
      | k1_xboole_0 = '#skF_3'
      | k1_tarski(A_4) != k1_tarski('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_29])).

tff(c_33,plain,(
    ! [A_4] :
      ( k1_tarski(A_4) = '#skF_3'
      | k1_tarski(A_4) != k1_tarski('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_32])).

tff(c_41,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_33])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_24])).

tff(c_16,plain,(
    ! [B_2,A_1,C_3] :
      ( k1_xboole_0 = B_2
      | k1_tarski(A_1) = B_2
      | k2_xboole_0(B_2,C_3) != k1_tarski(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_52,plain,(
    ! [A_1] :
      ( k1_xboole_0 = '#skF_2'
      | k1_tarski(A_1) = '#skF_2'
      | k1_tarski(A_1) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_16])).

tff(c_61,plain,(
    ! [A_11] :
      ( k1_tarski(A_11) = '#skF_2'
      | k1_tarski(A_11) != '#skF_3' ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_52])).

tff(c_64,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_61])).

tff(c_66,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_64])).

tff(c_68,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_66])).

%------------------------------------------------------------------------------
