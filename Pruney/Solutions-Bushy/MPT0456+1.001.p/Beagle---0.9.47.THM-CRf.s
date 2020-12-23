%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0456+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:20 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   44 (  52 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 (  84 expanded)
%              Number of equality atoms :    2 (   3 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_6 > #skF_3 > #skF_13 > #skF_5 > #skF_11 > #skF_7 > #skF_9 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_42,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_38,plain,(
    ! [A_124,B_125] :
      ( v1_relat_1(k5_relat_1(A_124,B_125))
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [C_21,A_6] :
      ( r2_hidden(k4_tarski(C_21,'#skF_5'(A_6,k1_relat_1(A_6),C_21)),A_6)
      | ~ r2_hidden(C_21,k1_relat_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_233,plain,(
    ! [D_198,B_199,A_200,E_201] :
      ( r2_hidden(k4_tarski(D_198,'#skF_6'(D_198,B_199,A_200,E_201,k5_relat_1(A_200,B_199))),A_200)
      | ~ r2_hidden(k4_tarski(D_198,E_201),k5_relat_1(A_200,B_199))
      | ~ v1_relat_1(k5_relat_1(A_200,B_199))
      | ~ v1_relat_1(B_199)
      | ~ v1_relat_1(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k1_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(C_21,D_24),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_248,plain,(
    ! [D_202,A_203,E_204,B_205] :
      ( r2_hidden(D_202,k1_relat_1(A_203))
      | ~ r2_hidden(k4_tarski(D_202,E_204),k5_relat_1(A_203,B_205))
      | ~ v1_relat_1(k5_relat_1(A_203,B_205))
      | ~ v1_relat_1(B_205)
      | ~ v1_relat_1(A_203) ) ),
    inference(resolution,[status(thm)],[c_233,c_10])).

tff(c_274,plain,(
    ! [C_206,A_207,B_208] :
      ( r2_hidden(C_206,k1_relat_1(A_207))
      | ~ v1_relat_1(k5_relat_1(A_207,B_208))
      | ~ v1_relat_1(B_208)
      | ~ v1_relat_1(A_207)
      | ~ r2_hidden(C_206,k1_relat_1(k5_relat_1(A_207,B_208))) ) ),
    inference(resolution,[status(thm)],[c_8,c_248])).

tff(c_1031,plain,(
    ! [A_316,B_317,B_318] :
      ( r2_hidden('#skF_1'(k1_relat_1(k5_relat_1(A_316,B_317)),B_318),k1_relat_1(A_316))
      | ~ v1_relat_1(k5_relat_1(A_316,B_317))
      | ~ v1_relat_1(B_317)
      | ~ v1_relat_1(A_316)
      | r1_tarski(k1_relat_1(k5_relat_1(A_316,B_317)),B_318) ) ),
    inference(resolution,[status(thm)],[c_6,c_274])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1045,plain,(
    ! [A_319,B_320] :
      ( ~ v1_relat_1(k5_relat_1(A_319,B_320))
      | ~ v1_relat_1(B_320)
      | ~ v1_relat_1(A_319)
      | r1_tarski(k1_relat_1(k5_relat_1(A_319,B_320)),k1_relat_1(A_319)) ) ),
    inference(resolution,[status(thm)],[c_1031,c_4])).

tff(c_40,plain,(
    ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_12','#skF_13')),k1_relat_1('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1071,plain,
    ( ~ v1_relat_1(k5_relat_1('#skF_12','#skF_13'))
    | ~ v1_relat_1('#skF_13')
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_1045,c_40])).

tff(c_1085,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_12','#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1071])).

tff(c_1097,plain,
    ( ~ v1_relat_1('#skF_13')
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_38,c_1085])).

tff(c_1101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1097])).

%------------------------------------------------------------------------------
