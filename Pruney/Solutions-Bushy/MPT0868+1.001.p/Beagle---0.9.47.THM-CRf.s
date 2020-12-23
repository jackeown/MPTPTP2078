%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0868+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:59 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   35 (  82 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 ( 192 expanded)
%              Number of equality atoms :   40 ( 160 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => ( C != k1_mcart_1(C)
                  & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ! [C] :
              ( m1_subset_1(C,k2_zfmisc_1(A,B))
             => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(c_14,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_15,plain,(
    k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_10,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [C_15,A_16,B_17] :
      ( k4_tarski(k1_mcart_1(C_15),k2_mcart_1(C_15)) = C_15
      | ~ m1_subset_1(C_15,k2_zfmisc_1(A_16,B_17))
      | k1_xboole_0 = B_17
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10,c_22])).

tff(c_26,plain,
    ( k4_tarski('#skF_3',k2_mcart_1('#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15,c_24])).

tff(c_27,plain,(
    k4_tarski('#skF_3',k2_mcart_1('#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_12,c_26])).

tff(c_4,plain,(
    ! [B_4,C_5] : k1_mcart_1(k4_tarski(B_4,C_5)) != k4_tarski(B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_31,plain,(
    k4_tarski('#skF_3',k2_mcart_1('#skF_3')) != k1_mcart_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_4])).

tff(c_39,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_15,c_31])).

tff(c_40,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_48,plain,(
    ! [C_22,A_23,B_24] :
      ( k4_tarski(k1_mcart_1(C_22),k2_mcart_1(C_22)) = C_22
      | ~ m1_subset_1(C_22,k2_zfmisc_1(A_23,B_24))
      | k1_xboole_0 = B_24
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10,c_48])).

tff(c_52,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),'#skF_3') = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_50])).

tff(c_53,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),'#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_12,c_52])).

tff(c_2,plain,(
    ! [B_4,C_5] : k2_mcart_1(k4_tarski(B_4,C_5)) != k4_tarski(B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_57,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),'#skF_3') != k2_mcart_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_2])).

tff(c_65,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_40,c_57])).

%------------------------------------------------------------------------------
