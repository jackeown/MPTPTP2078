%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0352+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:09 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   47 (  79 expanded)
%              Number of leaves         :   16 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 ( 135 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_28,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_20,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_14,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_63,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_10,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( k3_subset_1(A_13,k3_subset_1(A_13,B_14)) = B_14
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10,c_22])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = k3_subset_1(A_15,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_100,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,k3_subset_1(A_22,B_23)) = k3_subset_1(A_22,k3_subset_1(A_22,B_23))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(resolution,[status(thm)],[c_4,c_49])).

tff(c_104,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_10,c_100])).

tff(c_109,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_104])).

tff(c_12,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_31,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_12,c_22])).

tff(c_106,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_100])).

tff(c_111,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_106])).

tff(c_8,plain,(
    ! [C_9,B_8,A_7] :
      ( r1_tarski(k4_xboole_0(C_9,B_8),k4_xboole_0(C_9,A_7))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_298,plain,(
    ! [A_31] :
      ( r1_tarski('#skF_2',k4_xboole_0('#skF_1',A_31))
      | ~ r1_tarski(A_31,k3_subset_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_8])).

tff(c_302,plain,(
    r1_tarski('#skF_2',k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_40,c_298])).

tff(c_305,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_302])).

tff(c_307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_305])).

tff(c_308,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_319,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_14])).

tff(c_320,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k3_subset_1(A_32,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_331,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_320])).

tff(c_332,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_320])).

tff(c_341,plain,(
    ! [C_34,B_35,A_36] :
      ( r1_tarski(k4_xboole_0(C_34,B_35),k4_xboole_0(C_34,A_36))
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_409,plain,(
    ! [B_40] :
      ( r1_tarski(k4_xboole_0('#skF_1',B_40),k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_341])).

tff(c_415,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_409])).

tff(c_417,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_415])).

tff(c_419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_319,c_417])).

%------------------------------------------------------------------------------
