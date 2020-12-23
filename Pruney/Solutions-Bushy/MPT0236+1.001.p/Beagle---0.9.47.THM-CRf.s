%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0236+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:57 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 137 expanded)
%              Number of leaves         :   16 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :   67 ( 289 expanded)
%              Number of equality atoms :   23 ( 125 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > #nlpp > k3_tarski > k1_tarski > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(c_32,plain,(
    k3_tarski(k1_tarski('#skF_7')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_4'(A_6,B_7),A_6)
      | r2_hidden('#skF_5'(A_6,B_7),B_7)
      | k3_tarski(A_6) = B_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_353,plain,(
    ! [A_77,B_78,D_79] :
      ( r2_hidden('#skF_4'(A_77,B_78),A_77)
      | ~ r2_hidden(D_79,A_77)
      | ~ r2_hidden('#skF_5'(A_77,B_78),D_79)
      | k3_tarski(A_77) = B_78 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_381,plain,(
    ! [B_80,A_81] :
      ( ~ r2_hidden(B_80,A_81)
      | r2_hidden('#skF_4'(A_81,B_80),A_81)
      | k3_tarski(A_81) = B_80 ) ),
    inference(resolution,[status(thm)],[c_28,c_353])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_400,plain,(
    ! [A_82,B_83] :
      ( '#skF_4'(k1_tarski(A_82),B_83) = A_82
      | ~ r2_hidden(B_83,k1_tarski(A_82))
      | k3_tarski(k1_tarski(A_82)) = B_83 ) ),
    inference(resolution,[status(thm)],[c_381,c_2])).

tff(c_440,plain,(
    ! [C_84] :
      ( '#skF_4'(k1_tarski(C_84),C_84) = C_84
      | k3_tarski(k1_tarski(C_84)) = C_84 ) ),
    inference(resolution,[status(thm)],[c_4,c_400])).

tff(c_501,plain,(
    '#skF_4'(k1_tarski('#skF_7'),'#skF_7') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_32])).

tff(c_30,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7),'#skF_4'(A_6,B_7))
      | r2_hidden('#skF_5'(A_6,B_7),B_7)
      | k3_tarski(A_6) = B_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_511,plain,
    ( r2_hidden('#skF_3'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | k3_tarski(k1_tarski('#skF_7')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_30])).

tff(c_521,plain,
    ( r2_hidden('#skF_3'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_511])).

tff(c_525,plain,(
    r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_521])).

tff(c_620,plain,(
    ! [A_89,B_90,D_91] :
      ( r2_hidden('#skF_3'(A_89,B_90),'#skF_4'(A_89,B_90))
      | ~ r2_hidden(D_91,A_89)
      | ~ r2_hidden('#skF_5'(A_89,B_90),D_91)
      | k3_tarski(A_89) = B_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_624,plain,
    ( r2_hidden('#skF_3'(k1_tarski('#skF_7'),'#skF_7'),'#skF_4'(k1_tarski('#skF_7'),'#skF_7'))
    | ~ r2_hidden('#skF_7',k1_tarski('#skF_7'))
    | k3_tarski(k1_tarski('#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_525,c_620])).

tff(c_650,plain,
    ( r2_hidden('#skF_3'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | k3_tarski(k1_tarski('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_501,c_624])).

tff(c_651,plain,(
    r2_hidden('#skF_3'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_650])).

tff(c_20,plain,(
    ! [A_6,B_7,D_20] :
      ( ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | ~ r2_hidden(D_20,A_6)
      | ~ r2_hidden('#skF_5'(A_6,B_7),D_20)
      | k3_tarski(A_6) = B_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_662,plain,(
    ! [D_20] :
      ( ~ r2_hidden(D_20,k1_tarski('#skF_7'))
      | ~ r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),D_20)
      | k3_tarski(k1_tarski('#skF_7')) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_651,c_20])).

tff(c_679,plain,(
    ! [D_92] :
      ( ~ r2_hidden(D_92,k1_tarski('#skF_7'))
      | ~ r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),D_92) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_662])).

tff(c_685,plain,(
    ~ r2_hidden('#skF_7',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_525,c_679])).

tff(c_716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_685])).

tff(c_717,plain,(
    r2_hidden('#skF_3'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_521])).

tff(c_26,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | r2_hidden('#skF_5'(A_6,B_7),B_7)
      | k3_tarski(A_6) = B_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_725,plain,
    ( r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | k3_tarski(k1_tarski('#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_717,c_26])).

tff(c_736,plain,(
    r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_725])).

tff(c_718,plain,(
    ~ r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_521])).

tff(c_755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_718])).

%------------------------------------------------------------------------------
