%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0153+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:49 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   31 (  48 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 ( 106 expanded)
%              Number of equality atoms :   40 (  81 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_5 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_43,negated_conjecture,(
    ~ ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [A_52,B_53,C_54] :
      ( '#skF_3'(A_52,B_53,C_54) = B_53
      | '#skF_3'(A_52,B_53,C_54) = A_52
      | r2_hidden('#skF_4'(A_52,B_53,C_54),C_54)
      | k2_tarski(A_52,B_53) = C_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_305,plain,(
    ! [A_64,B_65,A_66] :
      ( '#skF_4'(A_64,B_65,k1_tarski(A_66)) = A_66
      | '#skF_3'(A_64,B_65,k1_tarski(A_66)) = B_65
      | '#skF_3'(A_64,B_65,k1_tarski(A_66)) = A_64
      | k2_tarski(A_64,B_65) = k1_tarski(A_66) ) ),
    inference(resolution,[status(thm)],[c_117,c_2])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( '#skF_3'(A_6,B_7,C_8) = B_7
      | '#skF_3'(A_6,B_7,C_8) = A_6
      | '#skF_4'(A_6,B_7,C_8) != B_7
      | k2_tarski(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_325,plain,(
    ! [A_64,B_65] :
      ( '#skF_3'(A_64,B_65,k1_tarski(B_65)) = B_65
      | '#skF_3'(A_64,B_65,k1_tarski(B_65)) = A_64
      | k2_tarski(A_64,B_65) = k1_tarski(B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_22])).

tff(c_394,plain,(
    ! [B_69] :
      ( k2_tarski(B_69,B_69) = k1_tarski(B_69)
      | '#skF_3'(B_69,B_69,k1_tarski(B_69)) = B_69 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_325])).

tff(c_102,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r2_hidden('#skF_3'(A_38,B_39,C_40),C_40)
      | r2_hidden('#skF_4'(A_38,B_39,C_40),C_40)
      | k2_tarski(A_38,B_39) = C_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_112,plain,(
    ! [A_38,B_39,A_1] :
      ( '#skF_4'(A_38,B_39,k1_tarski(A_1)) = A_1
      | ~ r2_hidden('#skF_3'(A_38,B_39,k1_tarski(A_1)),k1_tarski(A_1))
      | k2_tarski(A_38,B_39) = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_102,c_2])).

tff(c_406,plain,(
    ! [B_69] :
      ( '#skF_4'(B_69,B_69,k1_tarski(B_69)) = B_69
      | ~ r2_hidden(B_69,k1_tarski(B_69))
      | k2_tarski(B_69,B_69) = k1_tarski(B_69)
      | k2_tarski(B_69,B_69) = k1_tarski(B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_112])).

tff(c_422,plain,(
    ! [B_69] :
      ( '#skF_4'(B_69,B_69,k1_tarski(B_69)) = B_69
      | k2_tarski(B_69,B_69) = k1_tarski(B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_406])).

tff(c_20,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | '#skF_4'(A_6,B_7,C_8) != B_7
      | k2_tarski(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_409,plain,(
    ! [B_69] :
      ( ~ r2_hidden(B_69,k1_tarski(B_69))
      | '#skF_4'(B_69,B_69,k1_tarski(B_69)) != B_69
      | k2_tarski(B_69,B_69) = k1_tarski(B_69)
      | k2_tarski(B_69,B_69) = k1_tarski(B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_20])).

tff(c_550,plain,(
    ! [B_73] :
      ( '#skF_4'(B_73,B_73,k1_tarski(B_73)) != B_73
      | k2_tarski(B_73,B_73) = k1_tarski(B_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_409])).

tff(c_558,plain,(
    ! [B_69] : k2_tarski(B_69,B_69) = k1_tarski(B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_550])).

tff(c_32,plain,(
    k2_tarski('#skF_5','#skF_5') != k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_32])).

%------------------------------------------------------------------------------
