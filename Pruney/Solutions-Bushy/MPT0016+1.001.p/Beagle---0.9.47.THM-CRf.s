%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0016+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:34 EST 2020

% Result     : Theorem 15.97s
% Output     : CNFRefutation 15.97s
% Verified   : 
% Statistics : Number of formulae       :   48 (  83 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   85 ( 200 expanded)
%              Number of equality atoms :   13 (  36 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_45,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [D_26,B_27,A_28] :
      ( r2_hidden(D_26,B_27)
      | r2_hidden(D_26,A_28)
      | ~ r2_hidden(D_26,k2_xboole_0(A_28,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_9883,plain,(
    ! [A_409,B_410,B_411] :
      ( r2_hidden('#skF_1'(k2_xboole_0(A_409,B_410),B_411),B_410)
      | r2_hidden('#skF_1'(k2_xboole_0(A_409,B_410),B_411),A_409)
      | r1_tarski(k2_xboole_0(A_409,B_410),B_411) ) ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( ~ r2_hidden('#skF_1'(A_20,B_21),B_21)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_20,A_6,B_7] :
      ( r1_tarski(A_20,k2_xboole_0(A_6,B_7))
      | ~ r2_hidden('#skF_1'(A_20,k2_xboole_0(A_6,B_7)),B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_32])).

tff(c_33379,plain,(
    ! [A_844,B_845,A_846] :
      ( r2_hidden('#skF_1'(k2_xboole_0(A_844,B_845),k2_xboole_0(A_846,B_845)),A_844)
      | r1_tarski(k2_xboole_0(A_844,B_845),k2_xboole_0(A_846,B_845)) ) ),
    inference(resolution,[status(thm)],[c_9883,c_46])).

tff(c_28,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_458,plain,(
    ! [A_89,B_90,C_91] :
      ( r2_hidden('#skF_2'(A_89,B_90,C_91),B_90)
      | r2_hidden('#skF_2'(A_89,B_90,C_91),A_89)
      | r2_hidden('#skF_3'(A_89,B_90,C_91),C_91)
      | k2_xboole_0(A_89,B_90) = C_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k2_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_510,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_2'(A_89,B_90,A_89),B_90)
      | r2_hidden('#skF_3'(A_89,B_90,A_89),A_89)
      | k2_xboole_0(A_89,B_90) = A_89 ) ),
    inference(resolution,[status(thm)],[c_458,c_22])).

tff(c_721,plain,(
    ! [A_117,B_118,C_119] :
      ( r2_hidden('#skF_2'(A_117,B_118,C_119),B_118)
      | r2_hidden('#skF_2'(A_117,B_118,C_119),A_117)
      | ~ r2_hidden('#skF_3'(A_117,B_118,C_119),A_117)
      | k2_xboole_0(A_117,B_118) = C_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | ~ r2_hidden('#skF_3'(A_6,B_7,C_8),A_6)
      | k2_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3282,plain,(
    ! [A_275,B_276] :
      ( r2_hidden('#skF_2'(A_275,B_276,A_275),B_276)
      | ~ r2_hidden('#skF_3'(A_275,B_276,A_275),A_275)
      | k2_xboole_0(A_275,B_276) = A_275 ) ),
    inference(resolution,[status(thm)],[c_721,c_18])).

tff(c_3344,plain,(
    ! [A_277,B_278] :
      ( r2_hidden('#skF_2'(A_277,B_278,A_277),B_278)
      | k2_xboole_0(A_277,B_278) = A_277 ) ),
    inference(resolution,[status(thm)],[c_510,c_3282])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3411,plain,(
    ! [A_279,B_280,B_281] :
      ( r2_hidden('#skF_2'(A_279,B_280,A_279),B_281)
      | ~ r1_tarski(B_280,B_281)
      | k2_xboole_0(A_279,B_280) = A_279 ) ),
    inference(resolution,[status(thm)],[c_3344,c_2])).

tff(c_3470,plain,(
    ! [B_281,B_280] :
      ( r2_hidden('#skF_3'(B_281,B_280,B_281),B_281)
      | ~ r1_tarski(B_280,B_281)
      | k2_xboole_0(B_281,B_280) = B_281 ) ),
    inference(resolution,[status(thm)],[c_3411,c_22])).

tff(c_3668,plain,(
    ! [B_291,B_292] :
      ( ~ r2_hidden('#skF_3'(B_291,B_292,B_291),B_291)
      | ~ r1_tarski(B_292,B_291)
      | k2_xboole_0(B_291,B_292) = B_291 ) ),
    inference(resolution,[status(thm)],[c_3411,c_18])).

tff(c_3747,plain,(
    ! [B_293,B_294] :
      ( ~ r1_tarski(B_293,B_294)
      | k2_xboole_0(B_294,B_293) = B_294 ) ),
    inference(resolution,[status(thm)],[c_3470,c_3668])).

tff(c_3808,plain,(
    k2_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_28,c_3747])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( ~ r2_hidden(D_11,A_6)
      | r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_231,plain,(
    ! [A_65,A_66,B_67] :
      ( r1_tarski(A_65,k2_xboole_0(A_66,B_67))
      | ~ r2_hidden('#skF_1'(A_65,k2_xboole_0(A_66,B_67)),A_66) ) ),
    inference(resolution,[status(thm)],[c_12,c_32])).

tff(c_262,plain,(
    ! [A_68,B_69] : r1_tarski(A_68,k2_xboole_0(A_68,B_69)) ),
    inference(resolution,[status(thm)],[c_6,c_231])).

tff(c_49,plain,(
    ! [C_23,B_24,A_25] :
      ( r2_hidden(C_23,B_24)
      | ~ r2_hidden(C_23,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [D_11,B_24,A_6,B_7] :
      ( r2_hidden(D_11,B_24)
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),B_24)
      | ~ r2_hidden(D_11,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_49])).

tff(c_269,plain,(
    ! [D_11,A_6,B_7,B_69] :
      ( r2_hidden(D_11,k2_xboole_0(k2_xboole_0(A_6,B_7),B_69))
      | ~ r2_hidden(D_11,B_7) ) ),
    inference(resolution,[status(thm)],[c_262,c_57])).

tff(c_4492,plain,(
    ! [D_301,B_302] :
      ( r2_hidden(D_301,k2_xboole_0('#skF_5',B_302))
      | ~ r2_hidden(D_301,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3808,c_269])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4575,plain,(
    ! [A_1,B_302] :
      ( r1_tarski(A_1,k2_xboole_0('#skF_5',B_302))
      | ~ r2_hidden('#skF_1'(A_1,k2_xboole_0('#skF_5',B_302)),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4492,c_4])).

tff(c_33534,plain,(
    ! [B_845] : r1_tarski(k2_xboole_0('#skF_4',B_845),k2_xboole_0('#skF_5',B_845)) ),
    inference(resolution,[status(thm)],[c_33379,c_4575])).

tff(c_26,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_4','#skF_6'),k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_33582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33534,c_26])).

%------------------------------------------------------------------------------
