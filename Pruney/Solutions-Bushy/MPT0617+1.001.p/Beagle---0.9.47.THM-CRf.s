%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0617+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:35 EST 2020

% Result     : Theorem 16.31s
% Output     : CNFRefutation 16.34s
% Verified   : 
% Statistics : Number of formulae       :  128 (2153 expanded)
%              Number of leaves         :   24 ( 748 expanded)
%              Depth                    :   31
%              Number of atoms          :  318 (8835 expanded)
%              Number of equality atoms :  108 (3102 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( k1_relat_1(A) = k1_relat_1(B)
                & ! [C] :
                    ( r2_hidden(C,k1_relat_1(A))
                   => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( A = B
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),A)
              <=> r2_hidden(k4_tarski(C,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_53,plain,(
    ! [A_51,B_52] :
      ( k1_funct_1(A_51,B_52) = k1_xboole_0
      | r2_hidden(B_52,k1_relat_1(A_51))
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    ! [C_46] :
      ( k1_funct_1('#skF_10',C_46) = k1_funct_1('#skF_9',C_46)
      | ~ r2_hidden(C_46,k1_relat_1('#skF_9')) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_57,plain,(
    ! [B_52] :
      ( k1_funct_1('#skF_10',B_52) = k1_funct_1('#skF_9',B_52)
      | k1_funct_1('#skF_9',B_52) = k1_xboole_0
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_53,c_36])).

tff(c_67,plain,(
    ! [B_52] :
      ( k1_funct_1('#skF_10',B_52) = k1_funct_1('#skF_9',B_52)
      | k1_funct_1('#skF_9',B_52) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_57])).

tff(c_34,plain,(
    '#skF_10' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,(
    k1_relat_1('#skF_10') = k1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2777,plain,(
    ! [A_163,B_164] :
      ( r2_hidden(k4_tarski('#skF_1'(A_163,B_164),'#skF_2'(A_163,B_164)),B_164)
      | r2_hidden(k4_tarski('#skF_3'(A_163,B_164),'#skF_4'(A_163,B_164)),A_163)
      | B_164 = A_163
      | ~ v1_relat_1(B_164)
      | ~ v1_relat_1(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    ! [C_38,A_23,D_41] :
      ( r2_hidden(C_38,k1_relat_1(A_23))
      | ~ r2_hidden(k4_tarski(C_38,D_41),A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2831,plain,(
    ! [A_165,B_166] :
      ( r2_hidden('#skF_1'(A_165,B_166),k1_relat_1(B_166))
      | r2_hidden(k4_tarski('#skF_3'(A_165,B_166),'#skF_4'(A_165,B_166)),A_165)
      | B_166 = A_165
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(A_165) ) ),
    inference(resolution,[status(thm)],[c_2777,c_24])).

tff(c_2860,plain,(
    ! [A_167,B_168] :
      ( r2_hidden('#skF_3'(A_167,B_168),k1_relat_1(A_167))
      | r2_hidden('#skF_1'(A_167,B_168),k1_relat_1(B_168))
      | B_168 = A_167
      | ~ v1_relat_1(B_168)
      | ~ v1_relat_1(A_167) ) ),
    inference(resolution,[status(thm)],[c_2831,c_24])).

tff(c_2879,plain,(
    ! [B_168] :
      ( r2_hidden('#skF_3'('#skF_10',B_168),k1_relat_1('#skF_9'))
      | r2_hidden('#skF_1'('#skF_10',B_168),k1_relat_1(B_168))
      | B_168 = '#skF_10'
      | ~ v1_relat_1(B_168)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2860])).

tff(c_2891,plain,(
    ! [B_169] :
      ( r2_hidden('#skF_3'('#skF_10',B_169),k1_relat_1('#skF_9'))
      | r2_hidden('#skF_1'('#skF_10',B_169),k1_relat_1(B_169))
      | B_169 = '#skF_10'
      | ~ v1_relat_1(B_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2879])).

tff(c_2913,plain,(
    ! [B_170] :
      ( k1_funct_1('#skF_10','#skF_3'('#skF_10',B_170)) = k1_funct_1('#skF_9','#skF_3'('#skF_10',B_170))
      | r2_hidden('#skF_1'('#skF_10',B_170),k1_relat_1(B_170))
      | B_170 = '#skF_10'
      | ~ v1_relat_1(B_170) ) ),
    inference(resolution,[status(thm)],[c_2891,c_36])).

tff(c_2923,plain,
    ( k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9'))
    | k1_funct_1('#skF_10','#skF_3'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9'))
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_2913,c_36])).

tff(c_2934,plain,
    ( k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9'))
    | k1_funct_1('#skF_10','#skF_3'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9'))
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2923])).

tff(c_2935,plain,
    ( k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9'))
    | k1_funct_1('#skF_10','#skF_3'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_2934])).

tff(c_3135,plain,(
    k1_funct_1('#skF_10','#skF_3'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_2935])).

tff(c_16,plain,(
    ! [B_21,A_18] :
      ( r2_hidden(k4_tarski(B_21,k1_funct_1(A_18,B_21)),A_18)
      | ~ r2_hidden(B_21,k1_relat_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3145,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9'))),'#skF_10')
    | ~ r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_3135,c_16])).

tff(c_3168,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9'))),'#skF_10')
    | ~ r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_3145])).

tff(c_3178,plain,(
    ~ r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_3168])).

tff(c_2890,plain,(
    ! [B_168] :
      ( r2_hidden('#skF_3'('#skF_10',B_168),k1_relat_1('#skF_9'))
      | r2_hidden('#skF_1'('#skF_10',B_168),k1_relat_1(B_168))
      | B_168 = '#skF_10'
      | ~ v1_relat_1(B_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2879])).

tff(c_3181,plain,
    ( r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_9'))
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_2890,c_3178])).

tff(c_3190,plain,
    ( r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_9'))
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3181])).

tff(c_3191,plain,(
    r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_3190])).

tff(c_14,plain,(
    ! [A_18,B_21,C_22] :
      ( k1_funct_1(A_18,B_21) = C_22
      | ~ r2_hidden(k4_tarski(B_21,C_22),A_18)
      | ~ r2_hidden(B_21,k1_relat_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6102,plain,(
    ! [B_222,A_223] :
      ( k1_funct_1(B_222,'#skF_1'(A_223,B_222)) = '#skF_2'(A_223,B_222)
      | ~ r2_hidden('#skF_1'(A_223,B_222),k1_relat_1(B_222))
      | ~ v1_funct_1(B_222)
      | r2_hidden(k4_tarski('#skF_3'(A_223,B_222),'#skF_4'(A_223,B_222)),A_223)
      | B_222 = A_223
      | ~ v1_relat_1(B_222)
      | ~ v1_relat_1(A_223) ) ),
    inference(resolution,[status(thm)],[c_2777,c_14])).

tff(c_11951,plain,(
    ! [A_343,B_344] :
      ( r2_hidden('#skF_3'(A_343,B_344),k1_relat_1(A_343))
      | k1_funct_1(B_344,'#skF_1'(A_343,B_344)) = '#skF_2'(A_343,B_344)
      | ~ r2_hidden('#skF_1'(A_343,B_344),k1_relat_1(B_344))
      | ~ v1_funct_1(B_344)
      | B_344 = A_343
      | ~ v1_relat_1(B_344)
      | ~ v1_relat_1(A_343) ) ),
    inference(resolution,[status(thm)],[c_6102,c_24])).

tff(c_11973,plain,
    ( r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_10'))
    | k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9')
    | ~ v1_funct_1('#skF_9')
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_3191,c_11951])).

tff(c_12036,plain,
    ( r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_9'))
    | k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9')
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_44,c_38,c_11973])).

tff(c_12037,plain,(
    k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_3178,c_12036])).

tff(c_3208,plain,(
    k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) ),
    inference(resolution,[status(thm)],[c_3191,c_36])).

tff(c_12068,plain,(
    k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12037,c_3208])).

tff(c_12102,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_10')
    | ~ r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_12068,c_16])).

tff(c_12128,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_3191,c_38,c_12102])).

tff(c_1443,plain,(
    ! [A_126,B_127] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_126,B_127),'#skF_2'(A_126,B_127)),A_126)
      | r2_hidden(k4_tarski('#skF_3'(A_126,B_127),'#skF_4'(A_126,B_127)),A_126)
      | B_127 = A_126
      | ~ v1_relat_1(B_127)
      | ~ v1_relat_1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1471,plain,(
    ! [A_126,B_127] :
      ( r2_hidden('#skF_3'(A_126,B_127),k1_relat_1(A_126))
      | ~ r2_hidden(k4_tarski('#skF_1'(A_126,B_127),'#skF_2'(A_126,B_127)),A_126)
      | B_127 = A_126
      | ~ v1_relat_1(B_127)
      | ~ v1_relat_1(A_126) ) ),
    inference(resolution,[status(thm)],[c_1443,c_24])).

tff(c_12183,plain,
    ( r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_10'))
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_12128,c_1471])).

tff(c_12198,plain,
    ( r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_9'))
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_38,c_12183])).

tff(c_12200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_3178,c_12198])).

tff(c_12202,plain,(
    r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_3168])).

tff(c_21362,plain,(
    ! [A_531,B_532] :
      ( k1_funct_1(A_531,'#skF_3'(A_531,B_532)) = '#skF_4'(A_531,B_532)
      | ~ r2_hidden('#skF_3'(A_531,B_532),k1_relat_1(A_531))
      | ~ v1_funct_1(A_531)
      | r2_hidden('#skF_1'(A_531,B_532),k1_relat_1(B_532))
      | B_532 = A_531
      | ~ v1_relat_1(B_532)
      | ~ v1_relat_1(A_531) ) ),
    inference(resolution,[status(thm)],[c_2831,c_14])).

tff(c_21422,plain,(
    ! [B_532] :
      ( k1_funct_1('#skF_10','#skF_3'('#skF_10',B_532)) = '#skF_4'('#skF_10',B_532)
      | ~ r2_hidden('#skF_3'('#skF_10',B_532),k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_10')
      | r2_hidden('#skF_1'('#skF_10',B_532),k1_relat_1(B_532))
      | B_532 = '#skF_10'
      | ~ v1_relat_1(B_532)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_21362])).

tff(c_21743,plain,(
    ! [B_538] :
      ( k1_funct_1('#skF_10','#skF_3'('#skF_10',B_538)) = '#skF_4'('#skF_10',B_538)
      | ~ r2_hidden('#skF_3'('#skF_10',B_538),k1_relat_1('#skF_9'))
      | r2_hidden('#skF_1'('#skF_10',B_538),k1_relat_1(B_538))
      | B_538 = '#skF_10'
      | ~ v1_relat_1(B_538) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_21422])).

tff(c_21747,plain,
    ( k1_funct_1('#skF_10','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9')
    | r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_9'))
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_12202,c_21743])).

tff(c_21759,plain,
    ( k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9')
    | r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_9'))
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3135,c_21747])).

tff(c_21760,plain,
    ( k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9')
    | r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_21759])).

tff(c_21766,plain,(
    r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_21760])).

tff(c_15298,plain,(
    ! [A_407,B_408] :
      ( k1_funct_1(A_407,'#skF_3'(A_407,B_408)) = '#skF_4'(A_407,B_408)
      | ~ r2_hidden('#skF_3'(A_407,B_408),k1_relat_1(A_407))
      | ~ v1_funct_1(A_407)
      | r2_hidden(k4_tarski('#skF_1'(A_407,B_408),'#skF_2'(A_407,B_408)),B_408)
      | B_408 = A_407
      | ~ v1_relat_1(B_408)
      | ~ v1_relat_1(A_407) ) ),
    inference(resolution,[status(thm)],[c_2777,c_14])).

tff(c_48482,plain,(
    ! [B_14268,A_14269] :
      ( k1_funct_1(B_14268,'#skF_1'(A_14269,B_14268)) = '#skF_2'(A_14269,B_14268)
      | ~ r2_hidden('#skF_1'(A_14269,B_14268),k1_relat_1(B_14268))
      | ~ v1_funct_1(B_14268)
      | k1_funct_1(A_14269,'#skF_3'(A_14269,B_14268)) = '#skF_4'(A_14269,B_14268)
      | ~ r2_hidden('#skF_3'(A_14269,B_14268),k1_relat_1(A_14269))
      | ~ v1_funct_1(A_14269)
      | B_14268 = A_14269
      | ~ v1_relat_1(B_14268)
      | ~ v1_relat_1(A_14269) ) ),
    inference(resolution,[status(thm)],[c_15298,c_14])).

tff(c_48558,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9')
    | ~ v1_funct_1('#skF_9')
    | k1_funct_1('#skF_10','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9')
    | ~ r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_21766,c_48482])).

tff(c_48644,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9')
    | k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9')
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_40,c_12202,c_38,c_3135,c_44,c_48558])).

tff(c_48645,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9')
    | k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_48644])).

tff(c_48692,plain,(
    k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_48645])).

tff(c_22,plain,(
    ! [C_38,A_23] :
      ( r2_hidden(k4_tarski(C_38,'#skF_8'(A_23,k1_relat_1(A_23),C_38)),A_23)
      | ~ r2_hidden(C_38,k1_relat_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_560,plain,(
    ! [A_90,B_91,C_92] :
      ( k1_funct_1(A_90,B_91) = C_92
      | ~ r2_hidden(k4_tarski(B_91,C_92),A_90)
      | ~ r2_hidden(B_91,k1_relat_1(A_90))
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_629,plain,(
    ! [A_23,C_38] :
      ( '#skF_8'(A_23,k1_relat_1(A_23),C_38) = k1_funct_1(A_23,C_38)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23)
      | ~ r2_hidden(C_38,k1_relat_1(A_23)) ) ),
    inference(resolution,[status(thm)],[c_22,c_560])).

tff(c_12204,plain,
    ( '#skF_8'('#skF_9',k1_relat_1('#skF_9'),'#skF_3'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_12202,c_629])).

tff(c_12213,plain,(
    '#skF_8'('#skF_9',k1_relat_1('#skF_9'),'#skF_3'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_12204])).

tff(c_12238,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9'))),'#skF_9')
    | ~ r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12213,c_22])).

tff(c_12253,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9'))),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12202,c_12238])).

tff(c_48694,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),'#skF_4'('#skF_10','#skF_9')),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48692,c_12253])).

tff(c_4,plain,(
    ! [A_1,B_11] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),B_11)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1,B_11),'#skF_4'(A_1,B_11)),B_11)
      | B_11 = A_1
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_49154,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_9')
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_48694,c_4])).

tff(c_49163,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_9')
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_49154])).

tff(c_49164,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_49163])).

tff(c_49184,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9')
    | ~ r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_49164,c_14])).

tff(c_49190,plain,(
    k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_21766,c_49184])).

tff(c_21779,plain,(
    k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9')) = k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) ),
    inference(resolution,[status(thm)],[c_21766,c_36])).

tff(c_21789,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9'))),'#skF_10')
    | ~ r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_21779,c_16])).

tff(c_21815,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9'))),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_21766,c_38,c_21789])).

tff(c_49196,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49190,c_21815])).

tff(c_2,plain,(
    ! [A_1,B_11] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),A_1)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1,B_11),'#skF_4'(A_1,B_11)),B_11)
      | B_11 = A_1
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_49344,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),'#skF_4'('#skF_10','#skF_9')),'#skF_9')
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_49196,c_2])).

tff(c_49361,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_48694,c_49344])).

tff(c_49363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_49361])).

tff(c_49365,plain,(
    k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) != '#skF_4'('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_48645])).

tff(c_49364,plain,(
    k1_funct_1('#skF_9','#skF_1'('#skF_10','#skF_9')) = '#skF_2'('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_48645])).

tff(c_49369,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49364,c_21815])).

tff(c_1469,plain,(
    ! [A_126,B_127] :
      ( k1_funct_1(A_126,'#skF_3'(A_126,B_127)) = '#skF_4'(A_126,B_127)
      | ~ r2_hidden('#skF_3'(A_126,B_127),k1_relat_1(A_126))
      | ~ v1_funct_1(A_126)
      | ~ r2_hidden(k4_tarski('#skF_1'(A_126,B_127),'#skF_2'(A_126,B_127)),A_126)
      | B_127 = A_126
      | ~ v1_relat_1(B_127)
      | ~ v1_relat_1(A_126) ) ),
    inference(resolution,[status(thm)],[c_1443,c_14])).

tff(c_49521,plain,
    ( k1_funct_1('#skF_10','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9')
    | ~ r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_49369,c_1469])).

tff(c_49535,plain,
    ( k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9')
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_40,c_12202,c_38,c_3135,c_49521])).

tff(c_49537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_49365,c_49535])).

tff(c_49539,plain,(
    ~ r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_21760])).

tff(c_49538,plain,(
    k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) = '#skF_4'('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_21760])).

tff(c_49663,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),'#skF_4'('#skF_10','#skF_9')),'#skF_9')
    | ~ r2_hidden('#skF_3'('#skF_10','#skF_9'),k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_49538,c_16])).

tff(c_49673,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_10','#skF_9'),'#skF_4'('#skF_10','#skF_9')),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_12202,c_49663])).

tff(c_49734,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_9')
    | '#skF_10' = '#skF_9'
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_49673,c_4])).

tff(c_49743,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_9')
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_49734])).

tff(c_49744,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9'),'#skF_2'('#skF_10','#skF_9')),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_49743])).

tff(c_49757,plain,(
    r2_hidden('#skF_1'('#skF_10','#skF_9'),k1_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_49744,c_24])).

tff(c_49764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49539,c_49757])).

tff(c_49766,plain,(
    k1_funct_1('#skF_10','#skF_3'('#skF_10','#skF_9')) != k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_2935])).

tff(c_49817,plain,(
    k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_49766])).

tff(c_64,plain,(
    ! [B_52] :
      ( k1_funct_1('#skF_10',B_52) = k1_xboole_0
      | r2_hidden(B_52,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_53])).

tff(c_71,plain,(
    ! [B_53] :
      ( k1_funct_1('#skF_10',B_53) = k1_xboole_0
      | r2_hidden(B_53,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_64])).

tff(c_79,plain,(
    ! [B_53] :
      ( k1_funct_1('#skF_10',B_53) = k1_funct_1('#skF_9',B_53)
      | k1_funct_1('#skF_10',B_53) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_71,c_36])).

tff(c_49816,plain,(
    k1_funct_1('#skF_10','#skF_3'('#skF_10','#skF_9')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_49766])).

tff(c_49843,plain,(
    k1_funct_1('#skF_9','#skF_3'('#skF_10','#skF_9')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_49816,c_49766])).

tff(c_49904,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49817,c_49843])).

%------------------------------------------------------------------------------
