%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0040+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:37 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :   36 (  47 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 (  87 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k4_xboole_0(A,C),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).

tff(c_31,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_1'(A_18,B_19),A_18)
      | r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_107,plain,(
    ! [A_41,B_42,B_43] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_41,B_42),B_43),A_41)
      | r1_tarski(k4_xboole_0(A_41,B_42),B_43) ) ),
    inference(resolution,[status(thm)],[c_31,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [A_41,B_42] : r1_tarski(k4_xboole_0(A_41,B_42),A_41) ),
    inference(resolution,[status(thm)],[c_107,c_4])).

tff(c_28,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [C_23,B_24,A_25] :
      ( r2_hidden(C_23,B_24)
      | ~ r2_hidden(C_23,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    ! [A_32,B_33,B_34] :
      ( r2_hidden('#skF_1'(A_32,B_33),B_34)
      | ~ r1_tarski(A_32,B_34)
      | r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_374,plain,(
    ! [A_96,B_97,B_98,B_99] :
      ( r2_hidden('#skF_1'(A_96,B_97),B_98)
      | ~ r1_tarski(B_99,B_98)
      | ~ r1_tarski(A_96,B_99)
      | r1_tarski(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_386,plain,(
    ! [A_96,B_97] :
      ( r2_hidden('#skF_1'(A_96,B_97),'#skF_5')
      | ~ r1_tarski(A_96,'#skF_4')
      | r1_tarski(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_28,c_374])).

tff(c_53,plain,(
    ! [D_26,A_27,B_28] :
      ( r2_hidden(D_26,k4_xboole_0(A_27,B_28))
      | r2_hidden(D_26,B_28)
      | ~ r2_hidden(D_26,A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1073,plain,(
    ! [A_156,A_157,B_158] :
      ( r1_tarski(A_156,k4_xboole_0(A_157,B_158))
      | r2_hidden('#skF_1'(A_156,k4_xboole_0(A_157,B_158)),B_158)
      | ~ r2_hidden('#skF_1'(A_156,k4_xboole_0(A_157,B_158)),A_157) ) ),
    inference(resolution,[status(thm)],[c_53,c_4])).

tff(c_1244,plain,(
    ! [A_164,B_165] :
      ( r2_hidden('#skF_1'(A_164,k4_xboole_0('#skF_5',B_165)),B_165)
      | ~ r1_tarski(A_164,'#skF_4')
      | r1_tarski(A_164,k4_xboole_0('#skF_5',B_165)) ) ),
    inference(resolution,[status(thm)],[c_386,c_1073])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_40,plain,(
    ! [A_6,B_7,B_19] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_6,B_7),B_19),B_7)
      | r1_tarski(k4_xboole_0(A_6,B_7),B_19) ) ),
    inference(resolution,[status(thm)],[c_31,c_10])).

tff(c_1399,plain,(
    ! [A_174,B_175] :
      ( ~ r1_tarski(k4_xboole_0(A_174,B_175),'#skF_4')
      | r1_tarski(k4_xboole_0(A_174,B_175),k4_xboole_0('#skF_5',B_175)) ) ),
    inference(resolution,[status(thm)],[c_1244,c_40])).

tff(c_26,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_4','#skF_6'),k4_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1421,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_4','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1399,c_26])).

tff(c_1436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_1421])).

%------------------------------------------------------------------------------
