%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:56 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 119 expanded)
%              Number of leaves         :   28 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :   92 ( 204 expanded)
%              Number of equality atoms :   14 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_xboole_0 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_10 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_82,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_46,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_142,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_22,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_2'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_3'(A_14),A_14)
      | v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_212,plain,(
    ! [A_81,B_82,C_83] :
      ( r2_hidden(A_81,B_82)
      | ~ r2_hidden(A_81,C_83)
      | r2_hidden(A_81,k5_xboole_0(B_82,C_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_242,plain,(
    ! [A_84,A_85] :
      ( r2_hidden(A_84,A_85)
      | ~ r2_hidden(A_84,k1_xboole_0)
      | r2_hidden(A_84,A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_212])).

tff(c_263,plain,(
    ! [A_85] :
      ( r2_hidden('#skF_3'(k1_xboole_0),A_85)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_30,c_242])).

tff(c_264,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_44,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_10'(A_51,B_52),k2_relat_1(B_52))
      | ~ r2_hidden(A_51,k1_relat_1(B_52))
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ! [A_32,C_47] :
      ( r2_hidden(k4_tarski('#skF_9'(A_32,k2_relat_1(A_32),C_47),C_47),A_32)
      | ~ r2_hidden(C_47,k2_relat_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_469,plain,(
    ! [A_106,C_107] :
      ( r2_hidden(k4_tarski('#skF_9'(A_106,k2_relat_1(A_106),C_107),C_107),A_106)
      | ~ r2_hidden(C_107,k2_relat_1(A_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_341,plain,(
    ! [A_96,C_97,B_98] :
      ( ~ r2_hidden(A_96,C_97)
      | ~ r2_hidden(A_96,B_98)
      | ~ r2_hidden(A_96,k5_xboole_0(B_98,C_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_387,plain,(
    ! [A_96,A_13] :
      ( ~ r2_hidden(A_96,k1_xboole_0)
      | ~ r2_hidden(A_96,A_13)
      | ~ r2_hidden(A_96,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_341])).

tff(c_848,plain,(
    ! [C_150,A_151] :
      ( ~ r2_hidden(k4_tarski('#skF_9'(k1_xboole_0,k2_relat_1(k1_xboole_0),C_150),C_150),A_151)
      | ~ r2_hidden(C_150,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_469,c_387])).

tff(c_868,plain,(
    ! [C_155] : ~ r2_hidden(C_155,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_32,c_848])).

tff(c_888,plain,(
    ! [A_51] :
      ( ~ r2_hidden(A_51,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_44,c_868])).

tff(c_986,plain,(
    ! [A_157] : ~ r2_hidden(A_157,k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_888])).

tff(c_1014,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_986])).

tff(c_1028,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_1014])).

tff(c_1029,plain,(
    ! [A_85] : r2_hidden('#skF_3'(k1_xboole_0),A_85) ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_1123,plain,(
    ! [A_169,C_170,B_171] :
      ( ~ r2_hidden(A_169,C_170)
      | ~ r2_hidden(A_169,B_171)
      | ~ r2_hidden(A_169,k5_xboole_0(B_171,C_170)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1138,plain,(
    ! [C_170,B_171] :
      ( ~ r2_hidden('#skF_3'(k1_xboole_0),C_170)
      | ~ r2_hidden('#skF_3'(k1_xboole_0),B_171) ) ),
    inference(resolution,[status(thm)],[c_1029,c_1123])).

tff(c_1180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1029,c_1029,c_1138])).

tff(c_1181,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1518,plain,(
    ! [A_219,C_220] :
      ( r2_hidden(k4_tarski('#skF_9'(A_219,k2_relat_1(A_219),C_220),C_220),A_219)
      | ~ r2_hidden(C_220,k2_relat_1(A_219)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1256,plain,(
    ! [A_194,B_195,C_196] :
      ( r2_hidden(A_194,B_195)
      | ~ r2_hidden(A_194,C_196)
      | r2_hidden(A_194,k5_xboole_0(B_195,C_196)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1281,plain,(
    ! [A_194,A_13] :
      ( r2_hidden(A_194,A_13)
      | ~ r2_hidden(A_194,k1_xboole_0)
      | r2_hidden(A_194,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1256])).

tff(c_1879,plain,(
    ! [C_263,A_264] :
      ( r2_hidden(k4_tarski('#skF_9'(k1_xboole_0,k2_relat_1(k1_xboole_0),C_263),C_263),A_264)
      | ~ r2_hidden(C_263,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1518,c_1281])).

tff(c_34,plain,(
    ! [C_47,A_32,D_50] :
      ( r2_hidden(C_47,k2_relat_1(A_32))
      | ~ r2_hidden(k4_tarski(D_50,C_47),A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1919,plain,(
    ! [C_265,A_266] :
      ( r2_hidden(C_265,k2_relat_1(A_266))
      | ~ r2_hidden(C_265,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1879,c_34])).

tff(c_1946,plain,(
    ! [A_266] :
      ( r2_hidden('#skF_2'(k2_relat_1(k1_xboole_0)),k2_relat_1(A_266))
      | k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_1919])).

tff(c_1962,plain,(
    ! [A_266] : r2_hidden('#skF_2'(k2_relat_1(k1_xboole_0)),k2_relat_1(A_266)) ),
    inference(negUnitSimplification,[status(thm)],[c_1181,c_1946])).

tff(c_1539,plain,(
    ! [C_220,A_13] :
      ( r2_hidden(k4_tarski('#skF_9'(k1_xboole_0,k2_relat_1(k1_xboole_0),C_220),C_220),A_13)
      | ~ r2_hidden(C_220,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1518,c_1281])).

tff(c_1286,plain,(
    ! [A_197,C_198,B_199] :
      ( ~ r2_hidden(A_197,C_198)
      | ~ r2_hidden(A_197,B_199)
      | ~ r2_hidden(A_197,k5_xboole_0(B_199,C_198)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1321,plain,(
    ! [A_197,A_13] :
      ( ~ r2_hidden(A_197,k1_xboole_0)
      | ~ r2_hidden(A_197,A_13)
      | ~ r2_hidden(A_197,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1286])).

tff(c_2209,plain,(
    ! [C_296,A_297] :
      ( ~ r2_hidden(k4_tarski('#skF_9'(k1_xboole_0,k2_relat_1(k1_xboole_0),C_296),C_296),A_297)
      | ~ r2_hidden(C_296,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1518,c_1321])).

tff(c_2229,plain,(
    ! [C_298] : ~ r2_hidden(C_298,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1539,c_2209])).

tff(c_2287,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_1962,c_2229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:07:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.69  
% 3.96/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.70  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_xboole_0 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_10 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 3.96/1.70  
% 3.96/1.70  %Foreground sorts:
% 3.96/1.70  
% 3.96/1.70  
% 3.96/1.70  %Background operators:
% 3.96/1.70  
% 3.96/1.70  
% 3.96/1.70  %Foreground operators:
% 3.96/1.70  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.96/1.70  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.96/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.96/1.70  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.96/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.96/1.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.96/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.96/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.96/1.70  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 3.96/1.70  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.96/1.70  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 3.96/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.96/1.70  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.96/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/1.70  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.96/1.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.96/1.70  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.96/1.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.96/1.70  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.96/1.70  
% 3.96/1.71  tff(f_82, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.96/1.71  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.96/1.71  tff(f_61, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 3.96/1.71  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.96/1.71  tff(f_41, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.96/1.71  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_relat_1)).
% 3.96/1.71  tff(f_69, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 3.96/1.71  tff(c_46, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.96/1.71  tff(c_142, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 3.96/1.71  tff(c_22, plain, (![A_11]: (r2_hidden('#skF_2'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.96/1.71  tff(c_30, plain, (![A_14]: (r2_hidden('#skF_3'(A_14), A_14) | v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.96/1.71  tff(c_24, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.96/1.71  tff(c_212, plain, (![A_81, B_82, C_83]: (r2_hidden(A_81, B_82) | ~r2_hidden(A_81, C_83) | r2_hidden(A_81, k5_xboole_0(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.96/1.71  tff(c_242, plain, (![A_84, A_85]: (r2_hidden(A_84, A_85) | ~r2_hidden(A_84, k1_xboole_0) | r2_hidden(A_84, A_85))), inference(superposition, [status(thm), theory('equality')], [c_24, c_212])).
% 3.96/1.71  tff(c_263, plain, (![A_85]: (r2_hidden('#skF_3'(k1_xboole_0), A_85) | v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_242])).
% 3.96/1.71  tff(c_264, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_263])).
% 3.96/1.71  tff(c_44, plain, (![A_51, B_52]: (r2_hidden('#skF_10'(A_51, B_52), k2_relat_1(B_52)) | ~r2_hidden(A_51, k1_relat_1(B_52)) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.96/1.71  tff(c_32, plain, (![A_32, C_47]: (r2_hidden(k4_tarski('#skF_9'(A_32, k2_relat_1(A_32), C_47), C_47), A_32) | ~r2_hidden(C_47, k2_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.96/1.71  tff(c_469, plain, (![A_106, C_107]: (r2_hidden(k4_tarski('#skF_9'(A_106, k2_relat_1(A_106), C_107), C_107), A_106) | ~r2_hidden(C_107, k2_relat_1(A_106)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.96/1.71  tff(c_341, plain, (![A_96, C_97, B_98]: (~r2_hidden(A_96, C_97) | ~r2_hidden(A_96, B_98) | ~r2_hidden(A_96, k5_xboole_0(B_98, C_97)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.96/1.71  tff(c_387, plain, (![A_96, A_13]: (~r2_hidden(A_96, k1_xboole_0) | ~r2_hidden(A_96, A_13) | ~r2_hidden(A_96, A_13))), inference(superposition, [status(thm), theory('equality')], [c_24, c_341])).
% 3.96/1.71  tff(c_848, plain, (![C_150, A_151]: (~r2_hidden(k4_tarski('#skF_9'(k1_xboole_0, k2_relat_1(k1_xboole_0), C_150), C_150), A_151) | ~r2_hidden(C_150, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_469, c_387])).
% 3.96/1.71  tff(c_868, plain, (![C_155]: (~r2_hidden(C_155, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_32, c_848])).
% 3.96/1.71  tff(c_888, plain, (![A_51]: (~r2_hidden(A_51, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_44, c_868])).
% 3.96/1.71  tff(c_986, plain, (![A_157]: (~r2_hidden(A_157, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_888])).
% 3.96/1.71  tff(c_1014, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_986])).
% 3.96/1.71  tff(c_1028, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_1014])).
% 3.96/1.71  tff(c_1029, plain, (![A_85]: (r2_hidden('#skF_3'(k1_xboole_0), A_85))), inference(splitRight, [status(thm)], [c_263])).
% 3.96/1.71  tff(c_1123, plain, (![A_169, C_170, B_171]: (~r2_hidden(A_169, C_170) | ~r2_hidden(A_169, B_171) | ~r2_hidden(A_169, k5_xboole_0(B_171, C_170)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.96/1.71  tff(c_1138, plain, (![C_170, B_171]: (~r2_hidden('#skF_3'(k1_xboole_0), C_170) | ~r2_hidden('#skF_3'(k1_xboole_0), B_171))), inference(resolution, [status(thm)], [c_1029, c_1123])).
% 3.96/1.71  tff(c_1180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1029, c_1029, c_1138])).
% 3.96/1.71  tff(c_1181, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 3.96/1.71  tff(c_1518, plain, (![A_219, C_220]: (r2_hidden(k4_tarski('#skF_9'(A_219, k2_relat_1(A_219), C_220), C_220), A_219) | ~r2_hidden(C_220, k2_relat_1(A_219)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.96/1.71  tff(c_1256, plain, (![A_194, B_195, C_196]: (r2_hidden(A_194, B_195) | ~r2_hidden(A_194, C_196) | r2_hidden(A_194, k5_xboole_0(B_195, C_196)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.96/1.71  tff(c_1281, plain, (![A_194, A_13]: (r2_hidden(A_194, A_13) | ~r2_hidden(A_194, k1_xboole_0) | r2_hidden(A_194, A_13))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1256])).
% 3.96/1.71  tff(c_1879, plain, (![C_263, A_264]: (r2_hidden(k4_tarski('#skF_9'(k1_xboole_0, k2_relat_1(k1_xboole_0), C_263), C_263), A_264) | ~r2_hidden(C_263, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_1518, c_1281])).
% 3.96/1.71  tff(c_34, plain, (![C_47, A_32, D_50]: (r2_hidden(C_47, k2_relat_1(A_32)) | ~r2_hidden(k4_tarski(D_50, C_47), A_32))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.96/1.71  tff(c_1919, plain, (![C_265, A_266]: (r2_hidden(C_265, k2_relat_1(A_266)) | ~r2_hidden(C_265, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_1879, c_34])).
% 3.96/1.71  tff(c_1946, plain, (![A_266]: (r2_hidden('#skF_2'(k2_relat_1(k1_xboole_0)), k2_relat_1(A_266)) | k2_relat_1(k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_1919])).
% 3.96/1.71  tff(c_1962, plain, (![A_266]: (r2_hidden('#skF_2'(k2_relat_1(k1_xboole_0)), k2_relat_1(A_266)))), inference(negUnitSimplification, [status(thm)], [c_1181, c_1946])).
% 3.96/1.71  tff(c_1539, plain, (![C_220, A_13]: (r2_hidden(k4_tarski('#skF_9'(k1_xboole_0, k2_relat_1(k1_xboole_0), C_220), C_220), A_13) | ~r2_hidden(C_220, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_1518, c_1281])).
% 3.96/1.71  tff(c_1286, plain, (![A_197, C_198, B_199]: (~r2_hidden(A_197, C_198) | ~r2_hidden(A_197, B_199) | ~r2_hidden(A_197, k5_xboole_0(B_199, C_198)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.96/1.71  tff(c_1321, plain, (![A_197, A_13]: (~r2_hidden(A_197, k1_xboole_0) | ~r2_hidden(A_197, A_13) | ~r2_hidden(A_197, A_13))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1286])).
% 3.96/1.71  tff(c_2209, plain, (![C_296, A_297]: (~r2_hidden(k4_tarski('#skF_9'(k1_xboole_0, k2_relat_1(k1_xboole_0), C_296), C_296), A_297) | ~r2_hidden(C_296, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_1518, c_1321])).
% 3.96/1.71  tff(c_2229, plain, (![C_298]: (~r2_hidden(C_298, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_1539, c_2209])).
% 3.96/1.71  tff(c_2287, plain, $false, inference(resolution, [status(thm)], [c_1962, c_2229])).
% 3.96/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.71  
% 3.96/1.71  Inference rules
% 3.96/1.71  ----------------------
% 3.96/1.71  #Ref     : 2
% 3.96/1.71  #Sup     : 503
% 3.96/1.71  #Fact    : 0
% 3.96/1.71  #Define  : 0
% 3.96/1.71  #Split   : 5
% 3.96/1.71  #Chain   : 0
% 3.96/1.71  #Close   : 0
% 3.96/1.71  
% 3.96/1.71  Ordering : KBO
% 3.96/1.71  
% 3.96/1.71  Simplification rules
% 3.96/1.71  ----------------------
% 3.96/1.71  #Subsume      : 141
% 3.96/1.71  #Demod        : 53
% 3.96/1.71  #Tautology    : 122
% 3.96/1.71  #SimpNegUnit  : 3
% 3.96/1.71  #BackRed      : 2
% 3.96/1.71  
% 3.96/1.71  #Partial instantiations: 0
% 3.96/1.71  #Strategies tried      : 1
% 3.96/1.71  
% 3.96/1.71  Timing (in seconds)
% 3.96/1.71  ----------------------
% 3.96/1.71  Preprocessing        : 0.31
% 3.96/1.71  Parsing              : 0.17
% 3.96/1.71  CNF conversion       : 0.02
% 3.96/1.71  Main loop            : 0.61
% 3.96/1.71  Inferencing          : 0.22
% 3.96/1.71  Reduction            : 0.17
% 3.96/1.71  Demodulation         : 0.12
% 3.96/1.71  BG Simplification    : 0.03
% 3.96/1.71  Subsumption          : 0.14
% 3.96/1.71  Abstraction          : 0.03
% 3.96/1.71  MUC search           : 0.00
% 3.96/1.71  Cooper               : 0.00
% 3.96/1.71  Total                : 0.95
% 3.96/1.71  Index Insertion      : 0.00
% 3.96/1.71  Index Deletion       : 0.00
% 3.96/1.71  Index Matching       : 0.00
% 3.96/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
