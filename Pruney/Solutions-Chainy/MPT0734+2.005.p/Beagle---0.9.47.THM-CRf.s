%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:03 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 278 expanded)
%              Number of leaves         :   20 ( 103 expanded)
%              Depth                    :   13
%              Number of atoms          :  154 ( 799 expanded)
%              Number of equality atoms :   15 (  50 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( v1_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ! [C] :
                ( v3_ordinal1(C)
               => ( ( r1_tarski(A,B)
                    & r2_hidden(B,C) )
                 => r2_hidden(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_ordinal1)).

tff(f_45,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,(
    ! [A_31,B_32] :
      ( ~ r2_hidden('#skF_1'(A_31,B_32),B_32)
      | r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_30,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_38,plain,(
    ! [A_21] :
      ( v1_ordinal1(A_21)
      | ~ v3_ordinal1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_45,plain,(
    v1_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_38])).

tff(c_28,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_60,plain,(
    ! [B_29,A_30] :
      ( r1_tarski(B_29,A_30)
      | ~ r2_hidden(B_29,A_30)
      | ~ v1_ordinal1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_69,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ v1_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_60])).

tff(c_74,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_69])).

tff(c_95,plain,(
    ! [C_36,B_37,A_38] :
      ( r2_hidden(C_36,B_37)
      | ~ r2_hidden(C_36,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_150,plain,(
    ! [A_49,B_50,B_51] :
      ( r2_hidden('#skF_1'(A_49,B_50),B_51)
      | ~ r1_tarski(A_49,B_51)
      | r1_tarski(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_6,c_95])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_331,plain,(
    ! [A_79,B_80,B_81,B_82] :
      ( r2_hidden('#skF_1'(A_79,B_80),B_81)
      | ~ r1_tarski(B_82,B_81)
      | ~ r1_tarski(A_79,B_82)
      | r1_tarski(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_150,c_2])).

tff(c_356,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_1'(A_83,B_84),'#skF_5')
      | ~ r1_tarski(A_83,'#skF_4')
      | r1_tarski(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_74,c_331])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_371,plain,(
    ! [A_85] :
      ( ~ r1_tarski(A_85,'#skF_4')
      | r1_tarski(A_85,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_356,c_4])).

tff(c_36,plain,(
    v1_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_121,plain,(
    ! [A_41,B_42] :
      ( r2_hidden(A_41,B_42)
      | ~ r2_xboole_0(A_41,B_42)
      | ~ v3_ordinal1(B_42)
      | ~ v1_ordinal1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_174,plain,(
    ! [A_54,B_55] :
      ( r2_hidden(A_54,B_55)
      | ~ v3_ordinal1(B_55)
      | ~ v1_ordinal1(A_54)
      | B_55 = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_8,c_121])).

tff(c_26,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_186,plain,
    ( ~ v3_ordinal1('#skF_5')
    | ~ v1_ordinal1('#skF_3')
    | '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_174,c_26])).

tff(c_192,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_186])).

tff(c_193,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_380,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_371,c_193])).

tff(c_398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_380])).

tff(c_399,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_105,plain,(
    ! [B_39] :
      ( r2_hidden('#skF_4',B_39)
      | ~ r1_tarski('#skF_5',B_39) ) ),
    inference(resolution,[status(thm)],[c_28,c_95])).

tff(c_134,plain,(
    ! [B_45,B_46] :
      ( r2_hidden('#skF_4',B_45)
      | ~ r1_tarski(B_46,B_45)
      | ~ r1_tarski('#skF_5',B_46) ) ),
    inference(resolution,[status(thm)],[c_105,c_2])).

tff(c_144,plain,
    ( r2_hidden('#skF_4','#skF_4')
    | ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_134])).

tff(c_145,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_401,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_145])).

tff(c_413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_401])).

tff(c_414,plain,(
    r2_hidden('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_34,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_415,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_18,plain,(
    ! [B_12,A_9] :
      ( r1_tarski(B_12,A_9)
      | ~ r2_hidden(B_12,A_9)
      | ~ v1_ordinal1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_112,plain,(
    ! [B_39] :
      ( r1_tarski('#skF_4',B_39)
      | ~ v1_ordinal1(B_39)
      | ~ r1_tarski('#skF_5',B_39) ) ),
    inference(resolution,[status(thm)],[c_105,c_18])).

tff(c_433,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_415,c_112])).

tff(c_439,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_433])).

tff(c_567,plain,(
    ! [A_100,B_101] :
      ( r2_hidden(A_100,B_101)
      | ~ v3_ordinal1(B_101)
      | ~ v1_ordinal1(A_100)
      | B_101 = A_100
      | ~ r1_tarski(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_8,c_121])).

tff(c_1212,plain,(
    ! [A_168,B_169,B_170] :
      ( r2_hidden(A_168,B_169)
      | ~ r1_tarski(B_170,B_169)
      | ~ v3_ordinal1(B_170)
      | ~ v1_ordinal1(A_168)
      | B_170 = A_168
      | ~ r1_tarski(A_168,B_170) ) ),
    inference(resolution,[status(thm)],[c_567,c_2])).

tff(c_1230,plain,(
    ! [A_168] :
      ( r2_hidden(A_168,'#skF_3')
      | ~ v3_ordinal1('#skF_4')
      | ~ v1_ordinal1(A_168)
      | A_168 = '#skF_4'
      | ~ r1_tarski(A_168,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_439,c_1212])).

tff(c_1268,plain,(
    ! [A_172] :
      ( r2_hidden(A_172,'#skF_3')
      | ~ v1_ordinal1(A_172)
      | A_172 = '#skF_4'
      | ~ r1_tarski(A_172,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1230])).

tff(c_511,plain,(
    ! [A_93,B_94,B_95] :
      ( r2_hidden('#skF_1'(A_93,B_94),B_95)
      | ~ r1_tarski(A_93,B_95)
      | r1_tarski(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_6,c_95])).

tff(c_784,plain,(
    ! [A_124,B_125,B_126,B_127] :
      ( r2_hidden('#skF_1'(A_124,B_125),B_126)
      | ~ r1_tarski(B_127,B_126)
      | ~ r1_tarski(A_124,B_127)
      | r1_tarski(A_124,B_125) ) ),
    inference(resolution,[status(thm)],[c_511,c_2])).

tff(c_821,plain,(
    ! [A_128,B_129] :
      ( r2_hidden('#skF_1'(A_128,B_129),'#skF_5')
      | ~ r1_tarski(A_128,'#skF_4')
      | r1_tarski(A_128,B_129) ) ),
    inference(resolution,[status(thm)],[c_74,c_784])).

tff(c_836,plain,(
    ! [A_130] :
      ( ~ r1_tarski(A_130,'#skF_4')
      | r1_tarski(A_130,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_821,c_4])).

tff(c_579,plain,
    ( ~ v3_ordinal1('#skF_5')
    | ~ v1_ordinal1('#skF_3')
    | '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_567,c_26])).

tff(c_585,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_579])).

tff(c_586,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_585])).

tff(c_843,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_836,c_586])).

tff(c_867,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_843])).

tff(c_868,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_585])).

tff(c_877,plain,(
    ~ r2_hidden('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_868,c_26])).

tff(c_1271,plain,
    ( ~ v1_ordinal1('#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1268,c_877])).

tff(c_1283,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_36,c_1271])).

tff(c_1306,plain,(
    ~ r2_hidden('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1283,c_1283,c_877])).

tff(c_1319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_1306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:38:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.59  
% 3.49/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.60  %$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 3.49/1.60  
% 3.49/1.60  %Foreground sorts:
% 3.49/1.60  
% 3.49/1.60  
% 3.49/1.60  %Background operators:
% 3.49/1.60  
% 3.49/1.60  
% 3.49/1.60  %Foreground operators:
% 3.49/1.60  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.49/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.60  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 3.49/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.49/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.60  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.49/1.60  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 3.49/1.60  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.49/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.49/1.60  
% 3.86/1.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.86/1.61  tff(f_76, negated_conjecture, ~(![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (![C]: (v3_ordinal1(C) => ((r1_tarski(A, B) & r2_hidden(B, C)) => r2_hidden(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_ordinal1)).
% 3.86/1.61  tff(f_45, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 3.86/1.61  tff(f_52, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 3.86/1.61  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.86/1.61  tff(f_61, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 3.86/1.61  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.86/1.61  tff(c_75, plain, (![A_31, B_32]: (~r2_hidden('#skF_1'(A_31, B_32), B_32) | r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.86/1.61  tff(c_80, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_75])).
% 3.86/1.61  tff(c_30, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.86/1.61  tff(c_32, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.86/1.61  tff(c_38, plain, (![A_21]: (v1_ordinal1(A_21) | ~v3_ordinal1(A_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.86/1.61  tff(c_45, plain, (v1_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_38])).
% 3.86/1.61  tff(c_28, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.86/1.61  tff(c_60, plain, (![B_29, A_30]: (r1_tarski(B_29, A_30) | ~r2_hidden(B_29, A_30) | ~v1_ordinal1(A_30))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.86/1.61  tff(c_69, plain, (r1_tarski('#skF_4', '#skF_5') | ~v1_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_60])).
% 3.86/1.61  tff(c_74, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_69])).
% 3.86/1.61  tff(c_95, plain, (![C_36, B_37, A_38]: (r2_hidden(C_36, B_37) | ~r2_hidden(C_36, A_38) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.86/1.61  tff(c_150, plain, (![A_49, B_50, B_51]: (r2_hidden('#skF_1'(A_49, B_50), B_51) | ~r1_tarski(A_49, B_51) | r1_tarski(A_49, B_50))), inference(resolution, [status(thm)], [c_6, c_95])).
% 3.86/1.61  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.86/1.61  tff(c_331, plain, (![A_79, B_80, B_81, B_82]: (r2_hidden('#skF_1'(A_79, B_80), B_81) | ~r1_tarski(B_82, B_81) | ~r1_tarski(A_79, B_82) | r1_tarski(A_79, B_80))), inference(resolution, [status(thm)], [c_150, c_2])).
% 3.86/1.61  tff(c_356, plain, (![A_83, B_84]: (r2_hidden('#skF_1'(A_83, B_84), '#skF_5') | ~r1_tarski(A_83, '#skF_4') | r1_tarski(A_83, B_84))), inference(resolution, [status(thm)], [c_74, c_331])).
% 3.86/1.61  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.86/1.61  tff(c_371, plain, (![A_85]: (~r1_tarski(A_85, '#skF_4') | r1_tarski(A_85, '#skF_5'))), inference(resolution, [status(thm)], [c_356, c_4])).
% 3.86/1.61  tff(c_36, plain, (v1_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.86/1.61  tff(c_8, plain, (![A_6, B_7]: (r2_xboole_0(A_6, B_7) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.86/1.61  tff(c_121, plain, (![A_41, B_42]: (r2_hidden(A_41, B_42) | ~r2_xboole_0(A_41, B_42) | ~v3_ordinal1(B_42) | ~v1_ordinal1(A_41))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.86/1.61  tff(c_174, plain, (![A_54, B_55]: (r2_hidden(A_54, B_55) | ~v3_ordinal1(B_55) | ~v1_ordinal1(A_54) | B_55=A_54 | ~r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_8, c_121])).
% 3.86/1.61  tff(c_26, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.86/1.61  tff(c_186, plain, (~v3_ordinal1('#skF_5') | ~v1_ordinal1('#skF_3') | '#skF_5'='#skF_3' | ~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_174, c_26])).
% 3.86/1.61  tff(c_192, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_186])).
% 3.86/1.61  tff(c_193, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_192])).
% 3.86/1.61  tff(c_380, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_371, c_193])).
% 3.86/1.61  tff(c_398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_380])).
% 3.86/1.61  tff(c_399, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_192])).
% 3.86/1.61  tff(c_105, plain, (![B_39]: (r2_hidden('#skF_4', B_39) | ~r1_tarski('#skF_5', B_39))), inference(resolution, [status(thm)], [c_28, c_95])).
% 3.86/1.61  tff(c_134, plain, (![B_45, B_46]: (r2_hidden('#skF_4', B_45) | ~r1_tarski(B_46, B_45) | ~r1_tarski('#skF_5', B_46))), inference(resolution, [status(thm)], [c_105, c_2])).
% 3.86/1.61  tff(c_144, plain, (r2_hidden('#skF_4', '#skF_4') | ~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_134])).
% 3.86/1.61  tff(c_145, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_144])).
% 3.86/1.61  tff(c_401, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_399, c_145])).
% 3.86/1.61  tff(c_413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_401])).
% 3.86/1.61  tff(c_414, plain, (r2_hidden('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_144])).
% 3.86/1.61  tff(c_34, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.86/1.61  tff(c_415, plain, (r1_tarski('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_144])).
% 3.86/1.61  tff(c_18, plain, (![B_12, A_9]: (r1_tarski(B_12, A_9) | ~r2_hidden(B_12, A_9) | ~v1_ordinal1(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.86/1.61  tff(c_112, plain, (![B_39]: (r1_tarski('#skF_4', B_39) | ~v1_ordinal1(B_39) | ~r1_tarski('#skF_5', B_39))), inference(resolution, [status(thm)], [c_105, c_18])).
% 3.86/1.61  tff(c_433, plain, (r1_tarski('#skF_4', '#skF_3') | ~v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_415, c_112])).
% 3.86/1.61  tff(c_439, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_433])).
% 3.86/1.61  tff(c_567, plain, (![A_100, B_101]: (r2_hidden(A_100, B_101) | ~v3_ordinal1(B_101) | ~v1_ordinal1(A_100) | B_101=A_100 | ~r1_tarski(A_100, B_101))), inference(resolution, [status(thm)], [c_8, c_121])).
% 3.86/1.61  tff(c_1212, plain, (![A_168, B_169, B_170]: (r2_hidden(A_168, B_169) | ~r1_tarski(B_170, B_169) | ~v3_ordinal1(B_170) | ~v1_ordinal1(A_168) | B_170=A_168 | ~r1_tarski(A_168, B_170))), inference(resolution, [status(thm)], [c_567, c_2])).
% 3.86/1.61  tff(c_1230, plain, (![A_168]: (r2_hidden(A_168, '#skF_3') | ~v3_ordinal1('#skF_4') | ~v1_ordinal1(A_168) | A_168='#skF_4' | ~r1_tarski(A_168, '#skF_4'))), inference(resolution, [status(thm)], [c_439, c_1212])).
% 3.86/1.61  tff(c_1268, plain, (![A_172]: (r2_hidden(A_172, '#skF_3') | ~v1_ordinal1(A_172) | A_172='#skF_4' | ~r1_tarski(A_172, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1230])).
% 3.86/1.61  tff(c_511, plain, (![A_93, B_94, B_95]: (r2_hidden('#skF_1'(A_93, B_94), B_95) | ~r1_tarski(A_93, B_95) | r1_tarski(A_93, B_94))), inference(resolution, [status(thm)], [c_6, c_95])).
% 3.86/1.61  tff(c_784, plain, (![A_124, B_125, B_126, B_127]: (r2_hidden('#skF_1'(A_124, B_125), B_126) | ~r1_tarski(B_127, B_126) | ~r1_tarski(A_124, B_127) | r1_tarski(A_124, B_125))), inference(resolution, [status(thm)], [c_511, c_2])).
% 3.86/1.61  tff(c_821, plain, (![A_128, B_129]: (r2_hidden('#skF_1'(A_128, B_129), '#skF_5') | ~r1_tarski(A_128, '#skF_4') | r1_tarski(A_128, B_129))), inference(resolution, [status(thm)], [c_74, c_784])).
% 3.86/1.61  tff(c_836, plain, (![A_130]: (~r1_tarski(A_130, '#skF_4') | r1_tarski(A_130, '#skF_5'))), inference(resolution, [status(thm)], [c_821, c_4])).
% 3.86/1.61  tff(c_579, plain, (~v3_ordinal1('#skF_5') | ~v1_ordinal1('#skF_3') | '#skF_5'='#skF_3' | ~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_567, c_26])).
% 3.86/1.61  tff(c_585, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_579])).
% 3.86/1.61  tff(c_586, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_585])).
% 3.86/1.61  tff(c_843, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_836, c_586])).
% 3.86/1.61  tff(c_867, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_843])).
% 3.86/1.61  tff(c_868, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_585])).
% 3.86/1.61  tff(c_877, plain, (~r2_hidden('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_868, c_26])).
% 3.86/1.61  tff(c_1271, plain, (~v1_ordinal1('#skF_3') | '#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1268, c_877])).
% 3.86/1.61  tff(c_1283, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_36, c_1271])).
% 3.86/1.61  tff(c_1306, plain, (~r2_hidden('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1283, c_1283, c_877])).
% 3.86/1.61  tff(c_1319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_414, c_1306])).
% 3.86/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.61  
% 3.86/1.61  Inference rules
% 3.86/1.61  ----------------------
% 3.86/1.61  #Ref     : 0
% 3.86/1.61  #Sup     : 285
% 3.86/1.61  #Fact    : 0
% 3.86/1.61  #Define  : 0
% 3.86/1.62  #Split   : 4
% 3.86/1.62  #Chain   : 0
% 3.86/1.62  #Close   : 0
% 3.86/1.62  
% 3.86/1.62  Ordering : KBO
% 3.86/1.62  
% 3.86/1.62  Simplification rules
% 3.86/1.62  ----------------------
% 3.86/1.62  #Subsume      : 30
% 3.86/1.62  #Demod        : 179
% 3.86/1.62  #Tautology    : 85
% 3.86/1.62  #SimpNegUnit  : 0
% 3.86/1.62  #BackRed      : 45
% 3.86/1.62  
% 3.86/1.62  #Partial instantiations: 0
% 3.86/1.62  #Strategies tried      : 1
% 3.86/1.62  
% 3.86/1.62  Timing (in seconds)
% 3.86/1.62  ----------------------
% 3.86/1.62  Preprocessing        : 0.28
% 3.86/1.62  Parsing              : 0.15
% 3.86/1.62  CNF conversion       : 0.02
% 3.86/1.62  Main loop            : 0.56
% 3.86/1.62  Inferencing          : 0.21
% 3.86/1.62  Reduction            : 0.14
% 3.86/1.62  Demodulation         : 0.10
% 3.86/1.62  BG Simplification    : 0.03
% 3.86/1.62  Subsumption          : 0.15
% 3.86/1.62  Abstraction          : 0.02
% 3.86/1.62  MUC search           : 0.00
% 3.86/1.62  Cooper               : 0.00
% 3.86/1.62  Total                : 0.88
% 3.86/1.62  Index Insertion      : 0.00
% 3.86/1.62  Index Deletion       : 0.00
% 3.86/1.62  Index Matching       : 0.00
% 3.86/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
