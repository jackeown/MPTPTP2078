%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:16 EST 2020

% Result     : Theorem 7.02s
% Output     : CNFRefutation 7.02s
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
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_57,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_1'(A_38,B_39),A_38)
      | r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_109,plain,(
    ! [A_55,B_56,B_57] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_55,B_56),B_57),A_55)
      | r1_tarski(k3_xboole_0(A_55,B_56),B_57) ) ),
    inference(resolution,[status(thm)],[c_45,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_125,plain,(
    ! [A_55,B_56] : r1_tarski(k3_xboole_0(A_55,B_56),A_55) ),
    inference(resolution,[status(thm)],[c_109,c_4])).

tff(c_163,plain,(
    ! [C_67,A_68] :
      ( r2_hidden(k4_tarski(C_67,'#skF_7'(A_68,k1_relat_1(A_68),C_67)),A_68)
      | ~ r2_hidden(C_67,k1_relat_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_573,plain,(
    ! [C_151,A_152,B_153] :
      ( r2_hidden(k4_tarski(C_151,'#skF_7'(A_152,k1_relat_1(A_152),C_151)),B_153)
      | ~ r1_tarski(A_152,B_153)
      | ~ r2_hidden(C_151,k1_relat_1(A_152)) ) ),
    inference(resolution,[status(thm)],[c_163,c_2])).

tff(c_28,plain,(
    ! [C_27,A_12,D_30] :
      ( r2_hidden(C_27,k1_relat_1(A_12))
      | ~ r2_hidden(k4_tarski(C_27,D_30),A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_598,plain,(
    ! [C_154,B_155,A_156] :
      ( r2_hidden(C_154,k1_relat_1(B_155))
      | ~ r1_tarski(A_156,B_155)
      | ~ r2_hidden(C_154,k1_relat_1(A_156)) ) ),
    inference(resolution,[status(thm)],[c_573,c_28])).

tff(c_728,plain,(
    ! [C_163,A_164,B_165] :
      ( r2_hidden(C_163,k1_relat_1(A_164))
      | ~ r2_hidden(C_163,k1_relat_1(k3_xboole_0(A_164,B_165))) ) ),
    inference(resolution,[status(thm)],[c_125,c_598])).

tff(c_1018,plain,(
    ! [A_177,B_178,B_179] :
      ( r2_hidden('#skF_1'(k1_relat_1(k3_xboole_0(A_177,B_178)),B_179),k1_relat_1(A_177))
      | r1_tarski(k1_relat_1(k3_xboole_0(A_177,B_178)),B_179) ) ),
    inference(resolution,[status(thm)],[c_6,c_728])).

tff(c_1044,plain,(
    ! [A_177,B_178] : r1_tarski(k1_relat_1(k3_xboole_0(A_177,B_178)),k1_relat_1(A_177)) ),
    inference(resolution,[status(thm)],[c_1018,c_4])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

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
      ( r2_hidden(C_160,k1_relat_1(B_161))
      | ~ r2_hidden(C_160,k1_relat_1(k3_xboole_0(A_162,B_161))) ) ),
    inference(resolution,[status(thm)],[c_145,c_598])).

tff(c_1235,plain,(
    ! [A_196,B_197,B_198] :
      ( r2_hidden('#skF_1'(k1_relat_1(k3_xboole_0(A_196,B_197)),B_198),k1_relat_1(B_197))
      | r1_tarski(k1_relat_1(k3_xboole_0(A_196,B_197)),B_198) ) ),
    inference(resolution,[status(thm)],[c_6,c_627])).

tff(c_1266,plain,(
    ! [A_196,B_197] : r1_tarski(k1_relat_1(k3_xboole_0(A_196,B_197)),k1_relat_1(B_197)) ),
    inference(resolution,[status(thm)],[c_1235,c_4])).

tff(c_63,plain,(
    ! [C_43,B_44,A_45] :
      ( r2_hidden(C_43,B_44)
      | ~ r2_hidden(C_43,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

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
    inference(cnfTransformation,[status(thm)],[f_41])).

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
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_8','#skF_9')),k3_xboole_0(k1_relat_1('#skF_8'),k1_relat_1('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5372,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_8','#skF_9')),k1_relat_1('#skF_9'))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_8','#skF_9')),k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_5332,c_38])).

tff(c_5395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1044,c_1266,c_5372])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.02/2.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.02/2.48  
% 7.02/2.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.02/2.49  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 7.02/2.49  
% 7.02/2.49  %Foreground sorts:
% 7.02/2.49  
% 7.02/2.49  
% 7.02/2.49  %Background operators:
% 7.02/2.49  
% 7.02/2.49  
% 7.02/2.49  %Foreground operators:
% 7.02/2.49  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.02/2.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.02/2.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.02/2.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.02/2.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.02/2.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.02/2.49  tff('#skF_9', type, '#skF_9': $i).
% 7.02/2.49  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 7.02/2.49  tff('#skF_8', type, '#skF_8': $i).
% 7.02/2.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.02/2.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.02/2.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.02/2.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.02/2.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.02/2.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.02/2.49  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.02/2.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.02/2.49  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.02/2.49  
% 7.02/2.50  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.02/2.50  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.02/2.50  tff(f_49, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 7.02/2.50  tff(f_57, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relat_1)).
% 7.02/2.50  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.02/2.50  tff(c_45, plain, (![A_38, B_39]: (r2_hidden('#skF_1'(A_38, B_39), A_38) | r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.02/2.50  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.02/2.50  tff(c_109, plain, (![A_55, B_56, B_57]: (r2_hidden('#skF_1'(k3_xboole_0(A_55, B_56), B_57), A_55) | r1_tarski(k3_xboole_0(A_55, B_56), B_57))), inference(resolution, [status(thm)], [c_45, c_12])).
% 7.02/2.50  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.02/2.50  tff(c_125, plain, (![A_55, B_56]: (r1_tarski(k3_xboole_0(A_55, B_56), A_55))), inference(resolution, [status(thm)], [c_109, c_4])).
% 7.02/2.50  tff(c_163, plain, (![C_67, A_68]: (r2_hidden(k4_tarski(C_67, '#skF_7'(A_68, k1_relat_1(A_68), C_67)), A_68) | ~r2_hidden(C_67, k1_relat_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.02/2.50  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.02/2.50  tff(c_573, plain, (![C_151, A_152, B_153]: (r2_hidden(k4_tarski(C_151, '#skF_7'(A_152, k1_relat_1(A_152), C_151)), B_153) | ~r1_tarski(A_152, B_153) | ~r2_hidden(C_151, k1_relat_1(A_152)))), inference(resolution, [status(thm)], [c_163, c_2])).
% 7.02/2.50  tff(c_28, plain, (![C_27, A_12, D_30]: (r2_hidden(C_27, k1_relat_1(A_12)) | ~r2_hidden(k4_tarski(C_27, D_30), A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.02/2.50  tff(c_598, plain, (![C_154, B_155, A_156]: (r2_hidden(C_154, k1_relat_1(B_155)) | ~r1_tarski(A_156, B_155) | ~r2_hidden(C_154, k1_relat_1(A_156)))), inference(resolution, [status(thm)], [c_573, c_28])).
% 7.02/2.50  tff(c_728, plain, (![C_163, A_164, B_165]: (r2_hidden(C_163, k1_relat_1(A_164)) | ~r2_hidden(C_163, k1_relat_1(k3_xboole_0(A_164, B_165))))), inference(resolution, [status(thm)], [c_125, c_598])).
% 7.02/2.50  tff(c_1018, plain, (![A_177, B_178, B_179]: (r2_hidden('#skF_1'(k1_relat_1(k3_xboole_0(A_177, B_178)), B_179), k1_relat_1(A_177)) | r1_tarski(k1_relat_1(k3_xboole_0(A_177, B_178)), B_179))), inference(resolution, [status(thm)], [c_6, c_728])).
% 7.02/2.50  tff(c_1044, plain, (![A_177, B_178]: (r1_tarski(k1_relat_1(k3_xboole_0(A_177, B_178)), k1_relat_1(A_177)))), inference(resolution, [status(thm)], [c_1018, c_4])).
% 7.02/2.50  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.02/2.50  tff(c_129, plain, (![A_60, B_61, B_62]: (r2_hidden('#skF_1'(k3_xboole_0(A_60, B_61), B_62), B_61) | r1_tarski(k3_xboole_0(A_60, B_61), B_62))), inference(resolution, [status(thm)], [c_45, c_10])).
% 7.02/2.50  tff(c_145, plain, (![A_60, B_61]: (r1_tarski(k3_xboole_0(A_60, B_61), B_61))), inference(resolution, [status(thm)], [c_129, c_4])).
% 7.02/2.50  tff(c_627, plain, (![C_160, B_161, A_162]: (r2_hidden(C_160, k1_relat_1(B_161)) | ~r2_hidden(C_160, k1_relat_1(k3_xboole_0(A_162, B_161))))), inference(resolution, [status(thm)], [c_145, c_598])).
% 7.02/2.50  tff(c_1235, plain, (![A_196, B_197, B_198]: (r2_hidden('#skF_1'(k1_relat_1(k3_xboole_0(A_196, B_197)), B_198), k1_relat_1(B_197)) | r1_tarski(k1_relat_1(k3_xboole_0(A_196, B_197)), B_198))), inference(resolution, [status(thm)], [c_6, c_627])).
% 7.02/2.50  tff(c_1266, plain, (![A_196, B_197]: (r1_tarski(k1_relat_1(k3_xboole_0(A_196, B_197)), k1_relat_1(B_197)))), inference(resolution, [status(thm)], [c_1235, c_4])).
% 7.02/2.50  tff(c_63, plain, (![C_43, B_44, A_45]: (r2_hidden(C_43, B_44) | ~r2_hidden(C_43, A_45) | ~r1_tarski(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.02/2.50  tff(c_66, plain, (![A_1, B_2, B_44]: (r2_hidden('#skF_1'(A_1, B_2), B_44) | ~r1_tarski(A_1, B_44) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_63])).
% 7.02/2.50  tff(c_68, plain, (![D_49, A_50, B_51]: (r2_hidden(D_49, k3_xboole_0(A_50, B_51)) | ~r2_hidden(D_49, B_51) | ~r2_hidden(D_49, A_50))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.02/2.50  tff(c_3076, plain, (![A_286, A_287, B_288]: (r1_tarski(A_286, k3_xboole_0(A_287, B_288)) | ~r2_hidden('#skF_1'(A_286, k3_xboole_0(A_287, B_288)), B_288) | ~r2_hidden('#skF_1'(A_286, k3_xboole_0(A_287, B_288)), A_287))), inference(resolution, [status(thm)], [c_68, c_4])).
% 7.02/2.50  tff(c_5178, plain, (![A_367, A_368, B_369]: (~r2_hidden('#skF_1'(A_367, k3_xboole_0(A_368, B_369)), A_368) | ~r1_tarski(A_367, B_369) | r1_tarski(A_367, k3_xboole_0(A_368, B_369)))), inference(resolution, [status(thm)], [c_66, c_3076])).
% 7.02/2.50  tff(c_5332, plain, (![A_372, B_373, B_374]: (~r1_tarski(A_372, B_373) | ~r1_tarski(A_372, B_374) | r1_tarski(A_372, k3_xboole_0(B_374, B_373)))), inference(resolution, [status(thm)], [c_66, c_5178])).
% 7.02/2.50  tff(c_38, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_8', '#skF_9')), k3_xboole_0(k1_relat_1('#skF_8'), k1_relat_1('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.02/2.50  tff(c_5372, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_8', '#skF_9')), k1_relat_1('#skF_9')) | ~r1_tarski(k1_relat_1(k3_xboole_0('#skF_8', '#skF_9')), k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_5332, c_38])).
% 7.02/2.50  tff(c_5395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1044, c_1266, c_5372])).
% 7.02/2.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.02/2.50  
% 7.02/2.50  Inference rules
% 7.02/2.50  ----------------------
% 7.02/2.50  #Ref     : 0
% 7.02/2.50  #Sup     : 1267
% 7.02/2.50  #Fact    : 0
% 7.02/2.50  #Define  : 0
% 7.02/2.50  #Split   : 0
% 7.02/2.50  #Chain   : 0
% 7.02/2.50  #Close   : 0
% 7.02/2.50  
% 7.02/2.50  Ordering : KBO
% 7.02/2.50  
% 7.02/2.50  Simplification rules
% 7.02/2.50  ----------------------
% 7.02/2.50  #Subsume      : 203
% 7.02/2.50  #Demod        : 121
% 7.02/2.50  #Tautology    : 81
% 7.02/2.50  #SimpNegUnit  : 0
% 7.02/2.50  #BackRed      : 0
% 7.02/2.50  
% 7.02/2.50  #Partial instantiations: 0
% 7.02/2.50  #Strategies tried      : 1
% 7.02/2.50  
% 7.02/2.50  Timing (in seconds)
% 7.02/2.50  ----------------------
% 7.02/2.50  Preprocessing        : 0.31
% 7.02/2.50  Parsing              : 0.17
% 7.02/2.50  CNF conversion       : 0.03
% 7.02/2.50  Main loop            : 1.37
% 7.02/2.50  Inferencing          : 0.41
% 7.02/2.50  Reduction            : 0.30
% 7.02/2.50  Demodulation         : 0.21
% 7.02/2.50  BG Simplification    : 0.05
% 7.02/2.50  Subsumption          : 0.49
% 7.02/2.50  Abstraction          : 0.07
% 7.02/2.50  MUC search           : 0.00
% 7.02/2.50  Cooper               : 0.00
% 7.02/2.50  Total                : 1.71
% 7.02/2.50  Index Insertion      : 0.00
% 7.02/2.50  Index Deletion       : 0.00
% 7.02/2.50  Index Matching       : 0.00
% 7.02/2.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
