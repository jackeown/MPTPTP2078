%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0444+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:19 EST 2020

% Result     : Theorem 6.54s
% Output     : CNFRefutation 6.54s
% Verified   : 
% Statistics : Number of formulae       :   51 (  85 expanded)
%              Number of leaves         :   22 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :   74 ( 168 expanded)
%              Number of equality atoms :    2 (   7 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_45,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_1'(A_38,B_39),A_38)
      | r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_109,plain,(
    ! [A_55,B_56,B_57] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_55,B_56),B_57),A_55)
      | r1_tarski(k3_xboole_0(A_55,B_56),B_57) ) ),
    inference(resolution,[status(thm)],[c_45,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_125,plain,(
    ! [A_55,B_56] : r1_tarski(k3_xboole_0(A_55,B_56),A_55) ),
    inference(resolution,[status(thm)],[c_109,c_4])).

tff(c_163,plain,(
    ! [A_67,C_68] :
      ( r2_hidden(k4_tarski('#skF_7'(A_67,k2_relat_1(A_67),C_68),C_68),A_67)
      | ~ r2_hidden(C_68,k2_relat_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_573,plain,(
    ! [A_151,C_152,B_153] :
      ( r2_hidden(k4_tarski('#skF_7'(A_151,k2_relat_1(A_151),C_152),C_152),B_153)
      | ~ r1_tarski(A_151,B_153)
      | ~ r2_hidden(C_152,k2_relat_1(A_151)) ) ),
    inference(resolution,[status(thm)],[c_163,c_2])).

tff(c_28,plain,(
    ! [C_27,A_12,D_30] :
      ( r2_hidden(C_27,k2_relat_1(A_12))
      | ~ r2_hidden(k4_tarski(D_30,C_27),A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_598,plain,(
    ! [C_154,B_155,A_156] :
      ( r2_hidden(C_154,k2_relat_1(B_155))
      | ~ r1_tarski(A_156,B_155)
      | ~ r2_hidden(C_154,k2_relat_1(A_156)) ) ),
    inference(resolution,[status(thm)],[c_573,c_28])).

tff(c_728,plain,(
    ! [C_163,A_164,B_165] :
      ( r2_hidden(C_163,k2_relat_1(A_164))
      | ~ r2_hidden(C_163,k2_relat_1(k3_xboole_0(A_164,B_165))) ) ),
    inference(resolution,[status(thm)],[c_125,c_598])).

tff(c_1018,plain,(
    ! [A_177,B_178,B_179] :
      ( r2_hidden('#skF_1'(k2_relat_1(k3_xboole_0(A_177,B_178)),B_179),k2_relat_1(A_177))
      | r1_tarski(k2_relat_1(k3_xboole_0(A_177,B_178)),B_179) ) ),
    inference(resolution,[status(thm)],[c_6,c_728])).

tff(c_1044,plain,(
    ! [A_177,B_178] : r1_tarski(k2_relat_1(k3_xboole_0(A_177,B_178)),k2_relat_1(A_177)) ),
    inference(resolution,[status(thm)],[c_1018,c_4])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_129,plain,(
    ! [A_60,B_61,B_62] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_60,B_61),B_62),B_61)
      | r1_tarski(k3_xboole_0(A_60,B_61),B_62) ) ),
    inference(resolution,[status(thm)],[c_45,c_10])).

tff(c_145,plain,(
    ! [A_60,B_61] : r1_tarski(k3_xboole_0(A_60,B_61),B_61) ),
    inference(resolution,[status(thm)],[c_129,c_4])).

tff(c_627,plain,(
    ! [C_160,B_161,A_162] :
      ( r2_hidden(C_160,k2_relat_1(B_161))
      | ~ r2_hidden(C_160,k2_relat_1(k3_xboole_0(A_162,B_161))) ) ),
    inference(resolution,[status(thm)],[c_145,c_598])).

tff(c_1235,plain,(
    ! [A_196,B_197,B_198] :
      ( r2_hidden('#skF_1'(k2_relat_1(k3_xboole_0(A_196,B_197)),B_198),k2_relat_1(B_197))
      | r1_tarski(k2_relat_1(k3_xboole_0(A_196,B_197)),B_198) ) ),
    inference(resolution,[status(thm)],[c_6,c_627])).

tff(c_1266,plain,(
    ! [A_196,B_197] : r1_tarski(k2_relat_1(k3_xboole_0(A_196,B_197)),k2_relat_1(B_197)) ),
    inference(resolution,[status(thm)],[c_1235,c_4])).

tff(c_63,plain,(
    ! [C_43,B_44,A_45] :
      ( r2_hidden(C_43,B_44)
      | ~ r2_hidden(C_43,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [A_1,B_2,B_44] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_44)
      | ~ r1_tarski(A_1,B_44)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_63])).

tff(c_68,plain,(
    ! [D_49,A_50,B_51] :
      ( r2_hidden(D_49,k3_xboole_0(A_50,B_51))
      | ~ r2_hidden(D_49,B_51)
      | ~ r2_hidden(D_49,A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3076,plain,(
    ! [A_286,A_287,B_288] :
      ( r1_tarski(A_286,k3_xboole_0(A_287,B_288))
      | ~ r2_hidden('#skF_1'(A_286,k3_xboole_0(A_287,B_288)),B_288)
      | ~ r2_hidden('#skF_1'(A_286,k3_xboole_0(A_287,B_288)),A_287) ) ),
    inference(resolution,[status(thm)],[c_68,c_4])).

tff(c_5178,plain,(
    ! [A_367,A_368,B_369] :
      ( ~ r2_hidden('#skF_1'(A_367,k3_xboole_0(A_368,B_369)),A_368)
      | ~ r1_tarski(A_367,B_369)
      | r1_tarski(A_367,k3_xboole_0(A_368,B_369)) ) ),
    inference(resolution,[status(thm)],[c_66,c_3076])).

tff(c_5332,plain,(
    ! [A_372,B_373,B_374] :
      ( ~ r1_tarski(A_372,B_373)
      | ~ r1_tarski(A_372,B_374)
      | r1_tarski(A_372,k3_xboole_0(B_374,B_373)) ) ),
    inference(resolution,[status(thm)],[c_66,c_5178])).

tff(c_38,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_8','#skF_9')),k3_xboole_0(k2_relat_1('#skF_8'),k2_relat_1('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_5372,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_8','#skF_9')),k2_relat_1('#skF_9'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_8','#skF_9')),k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_5332,c_38])).

tff(c_5395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1044,c_1266,c_5372])).

%------------------------------------------------------------------------------
