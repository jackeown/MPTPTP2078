%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:44 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 122 expanded)
%              Number of leaves         :   24 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  119 ( 211 expanded)
%              Number of equality atoms :   28 (  49 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,B) = k1_xboole_0
      <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_38,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | ~ r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_49,plain,(
    ~ r1_tarski('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | k4_xboole_0('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_61,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_301,plain,(
    ! [D_58,A_59,B_60] :
      ( r2_hidden(D_58,k4_xboole_0(A_59,B_60))
      | r2_hidden(D_58,B_60)
      | ~ r2_hidden(D_58,A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_392,plain,(
    ! [D_66] :
      ( r2_hidden(D_66,k1_xboole_0)
      | r2_hidden(D_66,'#skF_9')
      | ~ r2_hidden(D_66,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_301])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_407,plain,(
    ! [D_66] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r2_hidden(D_66,'#skF_9')
      | ~ r2_hidden(D_66,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_392,c_2])).

tff(c_415,plain,(
    ! [D_67] :
      ( r2_hidden(D_67,'#skF_9')
      | ~ r2_hidden(D_67,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_407])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_465,plain,(
    ! [A_70] :
      ( r1_tarski(A_70,'#skF_9')
      | ~ r2_hidden('#skF_2'(A_70,'#skF_9'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_415,c_8])).

tff(c_469,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_10,c_465])).

tff(c_473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_49,c_469])).

tff(c_475,plain,(
    k4_xboole_0('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,
    ( k4_xboole_0('#skF_6','#skF_7') != k1_xboole_0
    | k4_xboole_0('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_487,plain,(
    k4_xboole_0('#skF_6','#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_475,c_40])).

tff(c_474,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_32,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_5'(A_16),A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_494,plain,(
    ! [D_78,A_79,B_80] :
      ( r2_hidden(D_78,A_79)
      | ~ r2_hidden(D_78,k4_xboole_0(A_79,B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_508,plain,(
    ! [A_79,B_80] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_79,B_80)),A_79)
      | k4_xboole_0(A_79,B_80) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_494])).

tff(c_510,plain,(
    ! [D_81,B_82,A_83] :
      ( ~ r2_hidden(D_81,B_82)
      | ~ r2_hidden(D_81,k4_xboole_0(A_83,B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_893,plain,(
    ! [A_127,B_128] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_127,B_128)),B_128)
      | k4_xboole_0(A_127,B_128) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_510])).

tff(c_913,plain,(
    ! [A_129] : k4_xboole_0(A_129,A_129) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_508,c_893])).

tff(c_34,plain,(
    ! [C_20,B_19,A_18] :
      ( r1_tarski(k4_xboole_0(C_20,B_19),k4_xboole_0(C_20,A_18))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_990,plain,(
    ! [A_132,B_133] :
      ( r1_tarski(k4_xboole_0(A_132,B_133),k1_xboole_0)
      | ~ r1_tarski(A_132,B_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_913,c_34])).

tff(c_526,plain,(
    ! [C_84,B_85,A_86] :
      ( r2_hidden(C_84,B_85)
      | ~ r2_hidden(C_84,A_86)
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_536,plain,(
    ! [A_87,B_88] :
      ( r2_hidden('#skF_5'(A_87),B_88)
      | ~ r1_tarski(A_87,B_88)
      | k1_xboole_0 = A_87 ) ),
    inference(resolution,[status(thm)],[c_32,c_526])).

tff(c_553,plain,(
    ! [B_88,A_87] :
      ( ~ v1_xboole_0(B_88)
      | ~ r1_tarski(A_87,B_88)
      | k1_xboole_0 = A_87 ) ),
    inference(resolution,[status(thm)],[c_536,c_2])).

tff(c_1002,plain,(
    ! [A_132,B_133] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | k4_xboole_0(A_132,B_133) = k1_xboole_0
      | ~ r1_tarski(A_132,B_133) ) ),
    inference(resolution,[status(thm)],[c_990,c_553])).

tff(c_1052,plain,(
    ! [A_139,B_140] :
      ( k4_xboole_0(A_139,B_140) = k1_xboole_0
      | ~ r1_tarski(A_139,B_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1002])).

tff(c_1070,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_474,c_1052])).

tff(c_1081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_487,c_1070])).

tff(c_1083,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_36,plain,
    ( k4_xboole_0('#skF_6','#skF_7') != k1_xboole_0
    | ~ r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1085,plain,(
    k4_xboole_0('#skF_6','#skF_7') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1083,c_36])).

tff(c_1082,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1099,plain,(
    ! [D_145,A_146,B_147] :
      ( r2_hidden(D_145,A_146)
      | ~ r2_hidden(D_145,k4_xboole_0(A_146,B_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1334,plain,(
    ! [A_184,B_185] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_184,B_185)),A_184)
      | v1_xboole_0(k4_xboole_0(A_184,B_185)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1099])).

tff(c_1110,plain,(
    ! [D_148,B_149,A_150] :
      ( ~ r2_hidden(D_148,B_149)
      | ~ r2_hidden(D_148,k4_xboole_0(A_150,B_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1120,plain,(
    ! [A_150,B_149] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_150,B_149)),B_149)
      | v1_xboole_0(k4_xboole_0(A_150,B_149)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1110])).

tff(c_1357,plain,(
    ! [A_186] : v1_xboole_0(k4_xboole_0(A_186,A_186)) ),
    inference(resolution,[status(thm)],[c_1334,c_1120])).

tff(c_1086,plain,(
    ! [A_141] :
      ( r2_hidden('#skF_5'(A_141),A_141)
      | k1_xboole_0 = A_141 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1090,plain,(
    ! [A_141] :
      ( ~ v1_xboole_0(A_141)
      | k1_xboole_0 = A_141 ) ),
    inference(resolution,[status(thm)],[c_1086,c_2])).

tff(c_1364,plain,(
    ! [A_187] : k4_xboole_0(A_187,A_187) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1357,c_1090])).

tff(c_1771,plain,(
    ! [A_220,B_221] :
      ( r1_tarski(k4_xboole_0(A_220,B_221),k1_xboole_0)
      | ~ r1_tarski(A_220,B_221) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1364,c_34])).

tff(c_1142,plain,(
    ! [C_154,B_155,A_156] :
      ( r2_hidden(C_154,B_155)
      | ~ r2_hidden(C_154,A_156)
      | ~ r1_tarski(A_156,B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1153,plain,(
    ! [A_159,B_160] :
      ( r2_hidden('#skF_5'(A_159),B_160)
      | ~ r1_tarski(A_159,B_160)
      | k1_xboole_0 = A_159 ) ),
    inference(resolution,[status(thm)],[c_32,c_1142])).

tff(c_1170,plain,(
    ! [B_160,A_159] :
      ( ~ v1_xboole_0(B_160)
      | ~ r1_tarski(A_159,B_160)
      | k1_xboole_0 = A_159 ) ),
    inference(resolution,[status(thm)],[c_1153,c_2])).

tff(c_1791,plain,(
    ! [A_220,B_221] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | k4_xboole_0(A_220,B_221) = k1_xboole_0
      | ~ r1_tarski(A_220,B_221) ) ),
    inference(resolution,[status(thm)],[c_1771,c_1170])).

tff(c_1895,plain,(
    ! [A_229,B_230] :
      ( k4_xboole_0(A_229,B_230) = k1_xboole_0
      | ~ r1_tarski(A_229,B_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1791])).

tff(c_1916,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1082,c_1895])).

tff(c_1928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1085,c_1916])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n002.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 13:31:22 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.58  
% 3.14/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.58  %$ r2_hidden > r1_tarski > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2
% 3.14/1.58  
% 3.14/1.58  %Foreground sorts:
% 3.14/1.58  
% 3.14/1.58  
% 3.14/1.58  %Background operators:
% 3.14/1.58  
% 3.14/1.58  
% 3.14/1.58  %Foreground operators:
% 3.14/1.58  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.14/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.14/1.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.14/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.58  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.14/1.58  tff('#skF_7', type, '#skF_7': $i).
% 3.14/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.14/1.58  tff('#skF_9', type, '#skF_9': $i).
% 3.14/1.58  tff('#skF_8', type, '#skF_8': $i).
% 3.14/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.14/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.14/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.58  
% 3.14/1.60  tff(f_66, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 3.14/1.60  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.14/1.60  tff(f_49, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.14/1.60  tff(f_48, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.14/1.60  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.14/1.60  tff(f_57, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.14/1.60  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 3.14/1.60  tff(c_38, plain, (r1_tarski('#skF_6', '#skF_7') | ~r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.14/1.60  tff(c_49, plain, (~r1_tarski('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_38])).
% 3.14/1.60  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.14/1.60  tff(c_30, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.14/1.60  tff(c_42, plain, (r1_tarski('#skF_6', '#skF_7') | k4_xboole_0('#skF_8', '#skF_9')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.14/1.60  tff(c_61, plain, (k4_xboole_0('#skF_8', '#skF_9')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 3.14/1.60  tff(c_301, plain, (![D_58, A_59, B_60]: (r2_hidden(D_58, k4_xboole_0(A_59, B_60)) | r2_hidden(D_58, B_60) | ~r2_hidden(D_58, A_59))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.14/1.60  tff(c_392, plain, (![D_66]: (r2_hidden(D_66, k1_xboole_0) | r2_hidden(D_66, '#skF_9') | ~r2_hidden(D_66, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_301])).
% 3.14/1.60  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.14/1.60  tff(c_407, plain, (![D_66]: (~v1_xboole_0(k1_xboole_0) | r2_hidden(D_66, '#skF_9') | ~r2_hidden(D_66, '#skF_8'))), inference(resolution, [status(thm)], [c_392, c_2])).
% 3.14/1.60  tff(c_415, plain, (![D_67]: (r2_hidden(D_67, '#skF_9') | ~r2_hidden(D_67, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_407])).
% 3.14/1.60  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.14/1.60  tff(c_465, plain, (![A_70]: (r1_tarski(A_70, '#skF_9') | ~r2_hidden('#skF_2'(A_70, '#skF_9'), '#skF_8'))), inference(resolution, [status(thm)], [c_415, c_8])).
% 3.14/1.60  tff(c_469, plain, (r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_10, c_465])).
% 3.14/1.60  tff(c_473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_49, c_469])).
% 3.14/1.60  tff(c_475, plain, (k4_xboole_0('#skF_8', '#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 3.14/1.60  tff(c_40, plain, (k4_xboole_0('#skF_6', '#skF_7')!=k1_xboole_0 | k4_xboole_0('#skF_8', '#skF_9')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.14/1.60  tff(c_487, plain, (k4_xboole_0('#skF_6', '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_475, c_40])).
% 3.14/1.60  tff(c_474, plain, (r1_tarski('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_42])).
% 3.14/1.60  tff(c_32, plain, (![A_16]: (r2_hidden('#skF_5'(A_16), A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.14/1.60  tff(c_494, plain, (![D_78, A_79, B_80]: (r2_hidden(D_78, A_79) | ~r2_hidden(D_78, k4_xboole_0(A_79, B_80)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.14/1.60  tff(c_508, plain, (![A_79, B_80]: (r2_hidden('#skF_5'(k4_xboole_0(A_79, B_80)), A_79) | k4_xboole_0(A_79, B_80)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_494])).
% 3.14/1.60  tff(c_510, plain, (![D_81, B_82, A_83]: (~r2_hidden(D_81, B_82) | ~r2_hidden(D_81, k4_xboole_0(A_83, B_82)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.14/1.60  tff(c_893, plain, (![A_127, B_128]: (~r2_hidden('#skF_5'(k4_xboole_0(A_127, B_128)), B_128) | k4_xboole_0(A_127, B_128)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_510])).
% 3.14/1.60  tff(c_913, plain, (![A_129]: (k4_xboole_0(A_129, A_129)=k1_xboole_0)), inference(resolution, [status(thm)], [c_508, c_893])).
% 3.14/1.60  tff(c_34, plain, (![C_20, B_19, A_18]: (r1_tarski(k4_xboole_0(C_20, B_19), k4_xboole_0(C_20, A_18)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.14/1.60  tff(c_990, plain, (![A_132, B_133]: (r1_tarski(k4_xboole_0(A_132, B_133), k1_xboole_0) | ~r1_tarski(A_132, B_133))), inference(superposition, [status(thm), theory('equality')], [c_913, c_34])).
% 3.14/1.60  tff(c_526, plain, (![C_84, B_85, A_86]: (r2_hidden(C_84, B_85) | ~r2_hidden(C_84, A_86) | ~r1_tarski(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.14/1.60  tff(c_536, plain, (![A_87, B_88]: (r2_hidden('#skF_5'(A_87), B_88) | ~r1_tarski(A_87, B_88) | k1_xboole_0=A_87)), inference(resolution, [status(thm)], [c_32, c_526])).
% 3.14/1.60  tff(c_553, plain, (![B_88, A_87]: (~v1_xboole_0(B_88) | ~r1_tarski(A_87, B_88) | k1_xboole_0=A_87)), inference(resolution, [status(thm)], [c_536, c_2])).
% 3.14/1.60  tff(c_1002, plain, (![A_132, B_133]: (~v1_xboole_0(k1_xboole_0) | k4_xboole_0(A_132, B_133)=k1_xboole_0 | ~r1_tarski(A_132, B_133))), inference(resolution, [status(thm)], [c_990, c_553])).
% 3.14/1.60  tff(c_1052, plain, (![A_139, B_140]: (k4_xboole_0(A_139, B_140)=k1_xboole_0 | ~r1_tarski(A_139, B_140))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1002])).
% 3.14/1.60  tff(c_1070, plain, (k4_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_474, c_1052])).
% 3.14/1.60  tff(c_1081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_487, c_1070])).
% 3.14/1.60  tff(c_1083, plain, (r1_tarski('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_38])).
% 3.14/1.60  tff(c_36, plain, (k4_xboole_0('#skF_6', '#skF_7')!=k1_xboole_0 | ~r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.14/1.60  tff(c_1085, plain, (k4_xboole_0('#skF_6', '#skF_7')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1083, c_36])).
% 3.14/1.60  tff(c_1082, plain, (r1_tarski('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_38])).
% 3.14/1.60  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.14/1.60  tff(c_1099, plain, (![D_145, A_146, B_147]: (r2_hidden(D_145, A_146) | ~r2_hidden(D_145, k4_xboole_0(A_146, B_147)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.14/1.60  tff(c_1334, plain, (![A_184, B_185]: (r2_hidden('#skF_1'(k4_xboole_0(A_184, B_185)), A_184) | v1_xboole_0(k4_xboole_0(A_184, B_185)))), inference(resolution, [status(thm)], [c_4, c_1099])).
% 3.14/1.60  tff(c_1110, plain, (![D_148, B_149, A_150]: (~r2_hidden(D_148, B_149) | ~r2_hidden(D_148, k4_xboole_0(A_150, B_149)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.14/1.60  tff(c_1120, plain, (![A_150, B_149]: (~r2_hidden('#skF_1'(k4_xboole_0(A_150, B_149)), B_149) | v1_xboole_0(k4_xboole_0(A_150, B_149)))), inference(resolution, [status(thm)], [c_4, c_1110])).
% 3.14/1.60  tff(c_1357, plain, (![A_186]: (v1_xboole_0(k4_xboole_0(A_186, A_186)))), inference(resolution, [status(thm)], [c_1334, c_1120])).
% 3.14/1.60  tff(c_1086, plain, (![A_141]: (r2_hidden('#skF_5'(A_141), A_141) | k1_xboole_0=A_141)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.14/1.60  tff(c_1090, plain, (![A_141]: (~v1_xboole_0(A_141) | k1_xboole_0=A_141)), inference(resolution, [status(thm)], [c_1086, c_2])).
% 3.14/1.60  tff(c_1364, plain, (![A_187]: (k4_xboole_0(A_187, A_187)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1357, c_1090])).
% 3.14/1.60  tff(c_1771, plain, (![A_220, B_221]: (r1_tarski(k4_xboole_0(A_220, B_221), k1_xboole_0) | ~r1_tarski(A_220, B_221))), inference(superposition, [status(thm), theory('equality')], [c_1364, c_34])).
% 3.14/1.60  tff(c_1142, plain, (![C_154, B_155, A_156]: (r2_hidden(C_154, B_155) | ~r2_hidden(C_154, A_156) | ~r1_tarski(A_156, B_155))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.14/1.60  tff(c_1153, plain, (![A_159, B_160]: (r2_hidden('#skF_5'(A_159), B_160) | ~r1_tarski(A_159, B_160) | k1_xboole_0=A_159)), inference(resolution, [status(thm)], [c_32, c_1142])).
% 3.14/1.60  tff(c_1170, plain, (![B_160, A_159]: (~v1_xboole_0(B_160) | ~r1_tarski(A_159, B_160) | k1_xboole_0=A_159)), inference(resolution, [status(thm)], [c_1153, c_2])).
% 3.14/1.60  tff(c_1791, plain, (![A_220, B_221]: (~v1_xboole_0(k1_xboole_0) | k4_xboole_0(A_220, B_221)=k1_xboole_0 | ~r1_tarski(A_220, B_221))), inference(resolution, [status(thm)], [c_1771, c_1170])).
% 3.14/1.60  tff(c_1895, plain, (![A_229, B_230]: (k4_xboole_0(A_229, B_230)=k1_xboole_0 | ~r1_tarski(A_229, B_230))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1791])).
% 3.14/1.60  tff(c_1916, plain, (k4_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_1082, c_1895])).
% 3.14/1.60  tff(c_1928, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1085, c_1916])).
% 3.14/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.60  
% 3.14/1.60  Inference rules
% 3.14/1.60  ----------------------
% 3.14/1.60  #Ref     : 0
% 3.14/1.60  #Sup     : 411
% 3.14/1.60  #Fact    : 0
% 3.14/1.60  #Define  : 0
% 3.14/1.60  #Split   : 6
% 3.14/1.60  #Chain   : 0
% 3.14/1.60  #Close   : 0
% 3.14/1.60  
% 3.14/1.60  Ordering : KBO
% 3.14/1.60  
% 3.14/1.60  Simplification rules
% 3.14/1.60  ----------------------
% 3.14/1.60  #Subsume      : 48
% 3.14/1.60  #Demod        : 124
% 3.14/1.60  #Tautology    : 143
% 3.14/1.60  #SimpNegUnit  : 4
% 3.14/1.60  #BackRed      : 1
% 3.14/1.60  
% 3.14/1.60  #Partial instantiations: 0
% 3.14/1.60  #Strategies tried      : 1
% 3.14/1.60  
% 3.14/1.60  Timing (in seconds)
% 3.14/1.60  ----------------------
% 3.14/1.60  Preprocessing        : 0.30
% 3.14/1.60  Parsing              : 0.16
% 3.14/1.60  CNF conversion       : 0.03
% 3.14/1.60  Main loop            : 0.50
% 3.14/1.60  Inferencing          : 0.20
% 3.14/1.60  Reduction            : 0.12
% 3.14/1.60  Demodulation         : 0.08
% 3.14/1.60  BG Simplification    : 0.03
% 3.14/1.60  Subsumption          : 0.11
% 3.14/1.60  Abstraction          : 0.03
% 3.14/1.60  MUC search           : 0.00
% 3.14/1.60  Cooper               : 0.00
% 3.14/1.60  Total                : 0.84
% 3.14/1.60  Index Insertion      : 0.00
% 3.14/1.60  Index Deletion       : 0.00
% 3.14/1.60  Index Matching       : 0.00
% 3.14/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
