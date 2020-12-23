%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0034+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:36 EST 2020

% Result     : Theorem 6.51s
% Output     : CNFRefutation 6.73s
% Verified   : 
% Statistics : Number of formulae       :   40 (  62 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 ( 128 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_47,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

tff(c_33,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_1'(A_18,B_19),A_18)
      | r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_91,plain,(
    ! [A_32,B_33,B_34] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_32,B_33),B_34),A_32)
      | r1_tarski(k3_xboole_0(A_32,B_33),B_34) ) ),
    inference(resolution,[status(thm)],[c_33,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [A_32,B_33] : r1_tarski(k3_xboole_0(A_32,B_33),A_32) ),
    inference(resolution,[status(thm)],[c_91,c_4])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_111,plain,(
    ! [A_37,B_38,B_39] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_37,B_38),B_39),B_38)
      | r1_tarski(k3_xboole_0(A_37,B_38),B_39) ) ),
    inference(resolution,[status(thm)],[c_33,c_10])).

tff(c_127,plain,(
    ! [A_37,B_38] : r1_tarski(k3_xboole_0(A_37,B_38),B_38) ),
    inference(resolution,[status(thm)],[c_111,c_4])).

tff(c_30,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ! [C_23,B_24,A_25] :
      ( r2_hidden(C_23,B_24)
      | ~ r2_hidden(C_23,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [A_29,B_30,B_31] :
      ( r2_hidden('#skF_1'(A_29,B_30),B_31)
      | ~ r1_tarski(A_29,B_31)
      | r1_tarski(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_222,plain,(
    ! [A_60,B_61,B_62,B_63] :
      ( r2_hidden('#skF_1'(A_60,B_61),B_62)
      | ~ r1_tarski(B_63,B_62)
      | ~ r1_tarski(A_60,B_63)
      | r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_72,c_2])).

tff(c_237,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_1'(A_60,B_61),'#skF_5')
      | ~ r1_tarski(A_60,'#skF_4')
      | r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_30,c_222])).

tff(c_28,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_236,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_1'(A_60,B_61),'#skF_7')
      | ~ r1_tarski(A_60,'#skF_6')
      | r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_28,c_222])).

tff(c_55,plain,(
    ! [D_26,A_27,B_28] :
      ( r2_hidden(D_26,k3_xboole_0(A_27,B_28))
      | ~ r2_hidden(D_26,B_28)
      | ~ r2_hidden(D_26,A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3029,plain,(
    ! [A_309,A_310,B_311] :
      ( r1_tarski(A_309,k3_xboole_0(A_310,B_311))
      | ~ r2_hidden('#skF_1'(A_309,k3_xboole_0(A_310,B_311)),B_311)
      | ~ r2_hidden('#skF_1'(A_309,k3_xboole_0(A_310,B_311)),A_310) ) ),
    inference(resolution,[status(thm)],[c_55,c_4])).

tff(c_4580,plain,(
    ! [A_352,A_353] :
      ( ~ r2_hidden('#skF_1'(A_352,k3_xboole_0(A_353,'#skF_7')),A_353)
      | ~ r1_tarski(A_352,'#skF_6')
      | r1_tarski(A_352,k3_xboole_0(A_353,'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_236,c_3029])).

tff(c_4758,plain,(
    ! [A_355] :
      ( ~ r1_tarski(A_355,'#skF_6')
      | ~ r1_tarski(A_355,'#skF_4')
      | r1_tarski(A_355,k3_xboole_0('#skF_5','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_237,c_4580])).

tff(c_26,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_6'),k3_xboole_0('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4808,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_6'),'#skF_6')
    | ~ r1_tarski(k3_xboole_0('#skF_4','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4758,c_26])).

tff(c_4836,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_127,c_4808])).

%------------------------------------------------------------------------------
