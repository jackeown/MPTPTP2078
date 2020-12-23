%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0929+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:06 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :   63 (  80 expanded)
%              Number of leaves         :   33 (  41 expanded)
%              Depth                    :    6
%              Number of atoms          :   54 ( 109 expanded)
%              Number of equality atoms :   51 ( 106 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_tarski > #nlpp > k2_mcart_1 > k20_mcart_1 > k1_mcart_1 > k19_mcart_1 > k18_mcart_1 > k17_mcart_1 > #skF_11 > #skF_15 > #skF_7 > #skF_3 > #skF_10 > #skF_16 > #skF_14 > #skF_5 > #skF_6 > #skF_13 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k17_mcart_1,type,(
    k17_mcart_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k20_mcart_1,type,(
    k20_mcart_1: $i > $i )).

tff(k18_mcart_1,type,(
    k18_mcart_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k19_mcart_1,type,(
    k19_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ! [B] :
          ( B = k1_mcart_1(A)
        <=> ! [C,D] :
              ( A = k4_tarski(C,D)
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_mcart_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ! [B] :
          ( B = k2_mcart_1(A)
        <=> ! [C,D] :
              ( A = k4_tarski(C,D)
             => B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_mcart_1)).

tff(f_30,axiom,(
    ! [A] : k19_mcart_1(A) = k1_mcart_1(k2_mcart_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_mcart_1)).

tff(f_28,axiom,(
    ! [A] : k18_mcart_1(A) = k2_mcart_1(k1_mcart_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_mcart_1)).

tff(f_26,axiom,(
    ! [A] : k17_mcart_1(A) = k1_mcart_1(k1_mcart_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_mcart_1)).

tff(f_32,axiom,(
    ! [A] : k20_mcart_1(A) = k2_mcart_1(k2_mcart_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_mcart_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( k17_mcart_1(k4_tarski(k4_tarski(A,B),C)) = A
        & k18_mcart_1(k4_tarski(k4_tarski(A,B),C)) = B
        & k19_mcart_1(k4_tarski(F,k4_tarski(D,E))) = D
        & k20_mcart_1(k4_tarski(F,k4_tarski(D,E))) = E ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_mcart_1)).

tff(c_10,plain,(
    ! [C_24,D_25,B_17,C_18] :
      ( k1_mcart_1(k4_tarski(C_24,D_25)) = C_24
      | k4_tarski(C_24,D_25) != k4_tarski(B_17,C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1870,plain,(
    ! [B_17,C_18] : k1_mcart_1(k4_tarski(B_17,C_18)) = B_17 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_10])).

tff(c_16,plain,(
    ! [C_45,D_46,B_38,C_39] :
      ( k2_mcart_1(k4_tarski(C_45,D_46)) = D_46
      | k4_tarski(C_45,D_46) != k4_tarski(B_38,C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2940,plain,(
    ! [B_147,C_148] : k2_mcart_1(k4_tarski(B_147,C_148)) = C_148 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_16])).

tff(c_6,plain,(
    ! [A_3] : k1_mcart_1(k2_mcart_1(A_3)) = k19_mcart_1(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2970,plain,(
    ! [B_147,C_148] : k19_mcart_1(k4_tarski(B_147,C_148)) = k1_mcart_1(C_148) ),
    inference(superposition,[status(thm),theory(equality)],[c_2940,c_6])).

tff(c_2934,plain,(
    ! [B_38,C_39] : k2_mcart_1(k4_tarski(B_38,C_39)) = C_39 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_16])).

tff(c_1873,plain,(
    ! [B_121,C_122] : k1_mcart_1(k4_tarski(B_121,C_122)) = B_121 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_10])).

tff(c_4,plain,(
    ! [A_2] : k2_mcart_1(k1_mcart_1(A_2)) = k18_mcart_1(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_1885,plain,(
    ! [B_121,C_122] : k18_mcart_1(k4_tarski(B_121,C_122)) = k2_mcart_1(B_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_1873,c_4])).

tff(c_1592,plain,(
    ! [B_17,C_18] : k1_mcart_1(k4_tarski(B_17,C_18)) = B_17 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_10])).

tff(c_1596,plain,(
    ! [B_109,C_110] : k1_mcart_1(k4_tarski(B_109,C_110)) = B_109 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_10])).

tff(c_2,plain,(
    ! [A_1] : k1_mcart_1(k1_mcart_1(A_1)) = k17_mcart_1(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1629,plain,(
    ! [B_109,C_110] : k17_mcart_1(k4_tarski(B_109,C_110)) = k1_mcart_1(B_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_1596,c_2])).

tff(c_309,plain,(
    ! [B_38,C_39] : k2_mcart_1(k4_tarski(B_38,C_39)) = C_39 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_16])).

tff(c_313,plain,(
    ! [B_68,C_69] : k2_mcart_1(k4_tarski(B_68,C_69)) = C_69 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_16])).

tff(c_8,plain,(
    ! [A_4] : k2_mcart_1(k2_mcart_1(A_4)) = k20_mcart_1(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_325,plain,(
    ! [B_68,C_69] : k20_mcart_1(k4_tarski(B_68,C_69)) = k2_mcart_1(C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_8])).

tff(c_22,plain,
    ( k17_mcart_1(k4_tarski(k4_tarski('#skF_14','#skF_15'),'#skF_16')) != '#skF_14'
    | k18_mcart_1(k4_tarski(k4_tarski('#skF_11','#skF_12'),'#skF_13')) != '#skF_12'
    | k19_mcart_1(k4_tarski('#skF_10',k4_tarski('#skF_8','#skF_9'))) != '#skF_8'
    | k20_mcart_1(k4_tarski('#skF_7',k4_tarski('#skF_5','#skF_6'))) != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_150,plain,(
    k20_mcart_1(k4_tarski('#skF_7',k4_tarski('#skF_5','#skF_6'))) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_349,plain,(
    k2_mcart_1(k4_tarski('#skF_5','#skF_6')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_150])).

tff(c_352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_349])).

tff(c_353,plain,
    ( k19_mcart_1(k4_tarski('#skF_10',k4_tarski('#skF_8','#skF_9'))) != '#skF_8'
    | k18_mcart_1(k4_tarski(k4_tarski('#skF_11','#skF_12'),'#skF_13')) != '#skF_12'
    | k17_mcart_1(k4_tarski(k4_tarski('#skF_14','#skF_15'),'#skF_16')) != '#skF_14' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_426,plain,(
    k17_mcart_1(k4_tarski(k4_tarski('#skF_14','#skF_15'),'#skF_16')) != '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_353])).

tff(c_1660,plain,(
    k1_mcart_1(k4_tarski('#skF_14','#skF_15')) != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1629,c_426])).

tff(c_1663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1592,c_1660])).

tff(c_1664,plain,
    ( k18_mcart_1(k4_tarski(k4_tarski('#skF_11','#skF_12'),'#skF_13')) != '#skF_12'
    | k19_mcart_1(k4_tarski('#skF_10',k4_tarski('#skF_8','#skF_9'))) != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_3016,plain,(
    k19_mcart_1(k4_tarski('#skF_10',k4_tarski('#skF_8','#skF_9'))) != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2934,c_1885,c_1664])).

tff(c_3017,plain,(
    k1_mcart_1(k4_tarski('#skF_8','#skF_9')) != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2970,c_3016])).

tff(c_3021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1870,c_3017])).

%------------------------------------------------------------------------------
