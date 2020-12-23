%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0309+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:05 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   22 (  30 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  24 expanded)
%              Number of equality atoms :   13 (  23 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_zfmisc_1(k2_xboole_0(A,B),k2_xboole_0(C,D)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(A,D)),k2_zfmisc_1(B,C)),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_zfmisc_1)).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] : k2_xboole_0(k2_zfmisc_1(A_1,C_3),k2_zfmisc_1(B_2,C_3)) = k2_zfmisc_1(k2_xboole_0(A_1,B_2),C_3) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_40,plain,(
    ! [C_13,A_14,B_15] : k2_xboole_0(k2_zfmisc_1(C_13,A_14),k2_zfmisc_1(C_13,B_15)) = k2_zfmisc_1(C_13,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_xboole_0(k2_xboole_0(A_4,B_5),C_6) = k2_xboole_0(A_4,k2_xboole_0(B_5,C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_50,plain,(
    ! [C_13,A_14,B_15,C_6] : k2_xboole_0(k2_zfmisc_1(C_13,A_14),k2_xboole_0(k2_zfmisc_1(C_13,B_15),C_6)) = k2_xboole_0(k2_zfmisc_1(C_13,k2_xboole_0(A_14,B_15)),C_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_6])).

tff(c_4,plain,(
    ! [C_3,A_1,B_2] : k2_xboole_0(k2_zfmisc_1(C_3,A_1),k2_zfmisc_1(C_3,B_2)) = k2_zfmisc_1(C_3,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_8,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1('#skF_1','#skF_3'),k2_zfmisc_1('#skF_1','#skF_4')),k2_zfmisc_1('#skF_2','#skF_3')),k2_zfmisc_1('#skF_2','#skF_4')) != k2_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_9,plain,(
    k2_xboole_0(k2_zfmisc_1('#skF_1','#skF_3'),k2_xboole_0(k2_zfmisc_1('#skF_1','#skF_4'),k2_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')))) != k2_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_6,c_8])).

tff(c_10,plain,(
    k2_xboole_0(k2_zfmisc_1('#skF_1','#skF_3'),k2_xboole_0(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_2',k2_xboole_0('#skF_3','#skF_4')))) != k2_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_9])).

tff(c_1296,plain,(
    k2_xboole_0(k2_zfmisc_1('#skF_1',k2_xboole_0('#skF_3','#skF_4')),k2_zfmisc_1('#skF_2',k2_xboole_0('#skF_3','#skF_4'))) != k2_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_10])).

tff(c_1299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1296])).

%------------------------------------------------------------------------------
