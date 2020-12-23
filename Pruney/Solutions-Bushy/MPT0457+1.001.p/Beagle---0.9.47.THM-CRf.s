%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0457+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:20 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
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
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k2_relat_1 > #skF_6 > #skF_3 > #skF_13 > #skF_5 > #skF_11 > #skF_7 > #skF_9 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_4 > #skF_10

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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
           => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

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
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

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
    ! [A_6,C_21] :
      ( r2_hidden(k4_tarski('#skF_5'(A_6,k2_relat_1(A_6),C_21),C_21),A_6)
      | ~ r2_hidden(C_21,k2_relat_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_295,plain,(
    ! [D_213,B_214,A_215,E_216] :
      ( r2_hidden(k4_tarski('#skF_6'(D_213,B_214,A_215,E_216,k5_relat_1(A_215,B_214)),E_216),B_214)
      | ~ r2_hidden(k4_tarski(D_213,E_216),k5_relat_1(A_215,B_214))
      | ~ v1_relat_1(k5_relat_1(A_215,B_214))
      | ~ v1_relat_1(B_214)
      | ~ v1_relat_1(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k2_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(D_24,C_21),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_310,plain,(
    ! [E_217,B_218,D_219,A_220] :
      ( r2_hidden(E_217,k2_relat_1(B_218))
      | ~ r2_hidden(k4_tarski(D_219,E_217),k5_relat_1(A_220,B_218))
      | ~ v1_relat_1(k5_relat_1(A_220,B_218))
      | ~ v1_relat_1(B_218)
      | ~ v1_relat_1(A_220) ) ),
    inference(resolution,[status(thm)],[c_295,c_10])).

tff(c_346,plain,(
    ! [C_221,B_222,A_223] :
      ( r2_hidden(C_221,k2_relat_1(B_222))
      | ~ v1_relat_1(k5_relat_1(A_223,B_222))
      | ~ v1_relat_1(B_222)
      | ~ v1_relat_1(A_223)
      | ~ r2_hidden(C_221,k2_relat_1(k5_relat_1(A_223,B_222))) ) ),
    inference(resolution,[status(thm)],[c_8,c_310])).

tff(c_1052,plain,(
    ! [A_320,B_321,B_322] :
      ( r2_hidden('#skF_1'(k2_relat_1(k5_relat_1(A_320,B_321)),B_322),k2_relat_1(B_321))
      | ~ v1_relat_1(k5_relat_1(A_320,B_321))
      | ~ v1_relat_1(B_321)
      | ~ v1_relat_1(A_320)
      | r1_tarski(k2_relat_1(k5_relat_1(A_320,B_321)),B_322) ) ),
    inference(resolution,[status(thm)],[c_6,c_346])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1075,plain,(
    ! [A_327,B_328] :
      ( ~ v1_relat_1(k5_relat_1(A_327,B_328))
      | ~ v1_relat_1(B_328)
      | ~ v1_relat_1(A_327)
      | r1_tarski(k2_relat_1(k5_relat_1(A_327,B_328)),k2_relat_1(B_328)) ) ),
    inference(resolution,[status(thm)],[c_1052,c_4])).

tff(c_40,plain,(
    ~ r1_tarski(k2_relat_1(k5_relat_1('#skF_12','#skF_13')),k2_relat_1('#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1104,plain,
    ( ~ v1_relat_1(k5_relat_1('#skF_12','#skF_13'))
    | ~ v1_relat_1('#skF_13')
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_1075,c_40])).

tff(c_1119,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_12','#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1104])).

tff(c_1122,plain,
    ( ~ v1_relat_1('#skF_13')
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_38,c_1119])).

tff(c_1126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1122])).

%------------------------------------------------------------------------------
