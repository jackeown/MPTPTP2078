%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0312+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:05 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   26 (  30 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   20 (  30 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => k3_xboole_0(k2_zfmisc_1(A,D),k2_zfmisc_1(B,C)) = k2_zfmisc_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_28,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_47,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10,c_47])).

tff(c_69,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_54])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_55,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_12,c_47])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4,D_6] : k3_xboole_0(k2_zfmisc_1(A_3,C_5),k2_zfmisc_1(B_4,D_6)) = k2_zfmisc_1(k3_xboole_0(A_3,B_4),k3_xboole_0(C_5,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_8,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_2','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_13,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_72,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_13])).

tff(c_85,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_72])).

%------------------------------------------------------------------------------
