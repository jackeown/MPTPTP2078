%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0319+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:05 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   26 (  34 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  44 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_43,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( A != B
       => ( r1_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),D))
          & r1_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(D,k1_tarski(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(c_10,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(k1_tarski(A_5),k1_tarski(B_6))
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [C_3,D_4,A_1,B_2] :
      ( ~ r1_xboole_0(C_3,D_4)
      | r1_xboole_0(k2_zfmisc_1(A_1,C_3),k2_zfmisc_1(B_2,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_4,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( ~ r1_xboole_0(A_1,B_2)
      | r1_xboole_0(k2_zfmisc_1(A_1,C_3),k2_zfmisc_1(B_2,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_8,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_1')),k2_zfmisc_1('#skF_4',k1_tarski('#skF_2')))
    | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_3'),k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_3'),k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_22,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_14])).

tff(c_25,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_22])).

tff(c_29,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_25])).

tff(c_30,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_1')),k2_zfmisc_1('#skF_4',k1_tarski('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_38,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2,c_30])).

tff(c_42,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_38])).

tff(c_46,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_42])).

%------------------------------------------------------------------------------
