%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0854+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:57 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   52 (  69 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   56 ( 106 expanded)
%              Number of equality atoms :   27 (  41 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_11 > #skF_6 > #skF_10 > #skF_9 > #skF_3 > #skF_13 > #skF_5 > #skF_7 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,C))
       => ( r2_hidden(k1_mcart_1(A),B)
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ! [B] :
          ( B = k1_mcart_1(A)
        <=> ! [C,D] :
              ( A = k4_tarski(C,D)
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_mcart_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ! [B] :
          ( B = k2_mcart_1(A)
        <=> ! [C,D] :
              ( A = k4_tarski(C,D)
             => B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_mcart_1)).

tff(c_38,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_11'),'#skF_13')
    | ~ r2_hidden(k1_mcart_1('#skF_11'),'#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_41,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_11'),'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    r2_hidden('#skF_11',k2_zfmisc_1('#skF_12','#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_280,plain,(
    ! [A_146,B_147,D_148] :
      ( k4_tarski('#skF_9'(A_146,B_147,k2_zfmisc_1(A_146,B_147),D_148),'#skF_10'(A_146,B_147,k2_zfmisc_1(A_146,B_147),D_148)) = D_148
      | ~ r2_hidden(D_148,k2_zfmisc_1(A_146,B_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [C_20,D_21,B_13,C_14] :
      ( k1_mcart_1(k4_tarski(C_20,D_21)) = C_20
      | k4_tarski(C_20,D_21) != k4_tarski(B_13,C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    ! [B_13,C_14] : k1_mcart_1(k4_tarski(B_13,C_14)) = B_13 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2])).

tff(c_354,plain,(
    ! [A_157,B_158,D_159] :
      ( '#skF_9'(A_157,B_158,k2_zfmisc_1(A_157,B_158),D_159) = k1_mcart_1(D_159)
      | ~ r2_hidden(D_159,k2_zfmisc_1(A_157,B_158)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_62])).

tff(c_385,plain,(
    '#skF_9'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_11') = k1_mcart_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_40,c_354])).

tff(c_20,plain,(
    ! [A_43,B_44,D_70] :
      ( r2_hidden('#skF_9'(A_43,B_44,k2_zfmisc_1(A_43,B_44),D_70),A_43)
      | ~ r2_hidden(D_70,k2_zfmisc_1(A_43,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_392,plain,
    ( r2_hidden(k1_mcart_1('#skF_11'),'#skF_12')
    | ~ r2_hidden('#skF_11',k2_zfmisc_1('#skF_12','#skF_13')) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_20])).

tff(c_398,plain,(
    r2_hidden(k1_mcart_1('#skF_11'),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_392])).

tff(c_400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_398])).

tff(c_401,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_11'),'#skF_13') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_658,plain,(
    ! [A_234,B_235,D_236] :
      ( k4_tarski('#skF_9'(A_234,B_235,k2_zfmisc_1(A_234,B_235),D_236),'#skF_10'(A_234,B_235,k2_zfmisc_1(A_234,B_235),D_236)) = D_236
      | ~ r2_hidden(D_236,k2_zfmisc_1(A_234,B_235)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_422,plain,(
    ! [B_13,C_14] : k1_mcart_1(k4_tarski(B_13,C_14)) = B_13 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2])).

tff(c_714,plain,(
    ! [A_237,B_238,D_239] :
      ( '#skF_9'(A_237,B_238,k2_zfmisc_1(A_237,B_238),D_239) = k1_mcart_1(D_239)
      | ~ r2_hidden(D_239,k2_zfmisc_1(A_237,B_238)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_658,c_422])).

tff(c_745,plain,(
    '#skF_9'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_11') = k1_mcart_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_40,c_714])).

tff(c_16,plain,(
    ! [A_43,B_44,D_70] :
      ( k4_tarski('#skF_9'(A_43,B_44,k2_zfmisc_1(A_43,B_44),D_70),'#skF_10'(A_43,B_44,k2_zfmisc_1(A_43,B_44),D_70)) = D_70
      | ~ r2_hidden(D_70,k2_zfmisc_1(A_43,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_749,plain,
    ( k4_tarski(k1_mcart_1('#skF_11'),'#skF_10'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_11')) = '#skF_11'
    | ~ r2_hidden('#skF_11',k2_zfmisc_1('#skF_12','#skF_13')) ),
    inference(superposition,[status(thm),theory(equality)],[c_745,c_16])).

tff(c_756,plain,(
    k4_tarski(k1_mcart_1('#skF_11'),'#skF_10'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_11')) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_749])).

tff(c_8,plain,(
    ! [C_41,D_42,B_34,C_35] :
      ( k2_mcart_1(k4_tarski(C_41,D_42)) = D_42
      | k4_tarski(C_41,D_42) != k4_tarski(B_34,C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_405,plain,(
    ! [B_34,C_35] : k2_mcart_1(k4_tarski(B_34,C_35)) = C_35 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8])).

tff(c_807,plain,(
    '#skF_10'('#skF_12','#skF_13',k2_zfmisc_1('#skF_12','#skF_13'),'#skF_11') = k2_mcart_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_756,c_405])).

tff(c_18,plain,(
    ! [A_43,B_44,D_70] :
      ( r2_hidden('#skF_10'(A_43,B_44,k2_zfmisc_1(A_43,B_44),D_70),B_44)
      | ~ r2_hidden(D_70,k2_zfmisc_1(A_43,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_853,plain,
    ( r2_hidden(k2_mcart_1('#skF_11'),'#skF_13')
    | ~ r2_hidden('#skF_11',k2_zfmisc_1('#skF_12','#skF_13')) ),
    inference(superposition,[status(thm),theory(equality)],[c_807,c_18])).

tff(c_859,plain,(
    r2_hidden(k2_mcart_1('#skF_11'),'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_853])).

tff(c_861,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_401,c_859])).

%------------------------------------------------------------------------------
