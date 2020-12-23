%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:35 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   69 (  86 expanded)
%              Number of leaves         :   35 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 119 expanded)
%              Number of equality atoms :   25 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_66,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(c_62,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_60,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_48,plain,(
    ! [A_51,B_52] :
      ( r1_xboole_0(k1_tarski(A_51),B_52)
      | r2_hidden(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_243,plain,(
    ! [A_93,B_94,C_95] :
      ( ~ r1_xboole_0(A_93,B_94)
      | ~ r2_hidden(C_95,k3_xboole_0(A_93,B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_264,plain,(
    ! [A_96,B_97] :
      ( ~ r1_xboole_0(A_96,B_97)
      | v1_xboole_0(k3_xboole_0(A_96,B_97)) ) ),
    inference(resolution,[status(thm)],[c_6,c_243])).

tff(c_276,plain,(
    ! [A_1,B_2] :
      ( ~ r1_xboole_0(A_1,B_2)
      | v1_xboole_0(k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_264])).

tff(c_415,plain,(
    ! [A_118,B_119] :
      ( r2_hidden('#skF_2'(A_118,B_119),k3_xboole_0(A_118,B_119))
      | r1_xboole_0(A_118,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_456,plain,(
    ! [A_122,B_123] :
      ( ~ v1_xboole_0(k3_xboole_0(A_122,B_123))
      | r1_xboole_0(A_122,B_123) ) ),
    inference(resolution,[status(thm)],[c_415,c_4])).

tff(c_491,plain,(
    ! [B_124,A_125] :
      ( r1_xboole_0(B_124,A_125)
      | ~ r1_xboole_0(A_125,B_124) ) ),
    inference(resolution,[status(thm)],[c_276,c_456])).

tff(c_494,plain,(
    ! [B_52,A_51] :
      ( r1_xboole_0(B_52,k1_tarski(A_51))
      | r2_hidden(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_48,c_491])).

tff(c_34,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_78,plain,(
    ! [D_60,B_61] : r2_hidden(D_60,k2_tarski(D_60,B_61)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_81,plain,(
    ! [A_23] : r2_hidden(A_23,k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_78])).

tff(c_83,plain,(
    ! [B_63,A_64] :
      ( ~ r2_hidden(B_63,A_64)
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_90,plain,(
    ! [A_23] : ~ v1_xboole_0(k1_tarski(A_23)) ),
    inference(resolution,[status(thm)],[c_81,c_83])).

tff(c_56,plain,(
    ! [B_54,C_55] : r1_tarski(k1_tarski(B_54),k2_tarski(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_64,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_162,plain,(
    ! [A_80,B_81] :
      ( k3_xboole_0(A_80,B_81) = A_80
      | ~ r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_188,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_162])).

tff(c_227,plain,(
    ! [A_90,B_91,C_92] :
      ( r1_tarski(A_90,B_91)
      | ~ r1_tarski(A_90,k3_xboole_0(B_91,C_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_596,plain,(
    ! [A_137,B_138,A_139] :
      ( r1_tarski(A_137,B_138)
      | ~ r1_tarski(A_137,k3_xboole_0(A_139,B_138)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_227])).

tff(c_739,plain,(
    ! [A_156] :
      ( r1_tarski(A_156,k2_tarski('#skF_7','#skF_8'))
      | ~ r1_tarski(A_156,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_596])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_936,plain,(
    ! [A_172] :
      ( k3_xboole_0(A_172,k2_tarski('#skF_7','#skF_8')) = A_172
      | ~ r1_tarski(A_172,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_739,c_14])).

tff(c_961,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_936])).

tff(c_1194,plain,
    ( ~ r1_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_5'))
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_961,c_276])).

tff(c_1209,plain,(
    ~ r1_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1194])).

tff(c_1221,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_494,c_1209])).

tff(c_16,plain,(
    ! [D_22,B_18,A_17] :
      ( D_22 = B_18
      | D_22 = A_17
      | ~ r2_hidden(D_22,k2_tarski(A_17,B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1224,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1221,c_16])).

tff(c_1231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_60,c_1224])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.58  
% 3.55/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.59  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2
% 3.55/1.59  
% 3.55/1.59  %Foreground sorts:
% 3.55/1.59  
% 3.55/1.59  
% 3.55/1.59  %Background operators:
% 3.55/1.59  
% 3.55/1.59  
% 3.55/1.59  %Foreground operators:
% 3.55/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.55/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.55/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.55/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.55/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.55/1.59  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.55/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.55/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.55/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.55/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.55/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.55/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.55/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.55/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.55/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.55/1.59  tff('#skF_8', type, '#skF_8': $i).
% 3.55/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.55/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.55/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.55/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.55/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.55/1.59  
% 3.55/1.60  tff(f_108, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.55/1.60  tff(f_83, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.55/1.60  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.55/1.60  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.55/1.60  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.55/1.60  tff(f_66, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.55/1.60  tff(f_64, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.55/1.60  tff(f_98, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.55/1.60  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.55/1.60  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.55/1.60  tff(c_62, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.55/1.60  tff(c_60, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.55/1.60  tff(c_48, plain, (![A_51, B_52]: (r1_xboole_0(k1_tarski(A_51), B_52) | r2_hidden(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.55/1.60  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.55/1.60  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.55/1.60  tff(c_243, plain, (![A_93, B_94, C_95]: (~r1_xboole_0(A_93, B_94) | ~r2_hidden(C_95, k3_xboole_0(A_93, B_94)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.55/1.60  tff(c_264, plain, (![A_96, B_97]: (~r1_xboole_0(A_96, B_97) | v1_xboole_0(k3_xboole_0(A_96, B_97)))), inference(resolution, [status(thm)], [c_6, c_243])).
% 3.55/1.60  tff(c_276, plain, (![A_1, B_2]: (~r1_xboole_0(A_1, B_2) | v1_xboole_0(k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_264])).
% 3.55/1.60  tff(c_415, plain, (![A_118, B_119]: (r2_hidden('#skF_2'(A_118, B_119), k3_xboole_0(A_118, B_119)) | r1_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.55/1.60  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.55/1.60  tff(c_456, plain, (![A_122, B_123]: (~v1_xboole_0(k3_xboole_0(A_122, B_123)) | r1_xboole_0(A_122, B_123))), inference(resolution, [status(thm)], [c_415, c_4])).
% 3.55/1.60  tff(c_491, plain, (![B_124, A_125]: (r1_xboole_0(B_124, A_125) | ~r1_xboole_0(A_125, B_124))), inference(resolution, [status(thm)], [c_276, c_456])).
% 3.55/1.60  tff(c_494, plain, (![B_52, A_51]: (r1_xboole_0(B_52, k1_tarski(A_51)) | r2_hidden(A_51, B_52))), inference(resolution, [status(thm)], [c_48, c_491])).
% 3.55/1.60  tff(c_34, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.55/1.60  tff(c_78, plain, (![D_60, B_61]: (r2_hidden(D_60, k2_tarski(D_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.55/1.60  tff(c_81, plain, (![A_23]: (r2_hidden(A_23, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_78])).
% 3.55/1.60  tff(c_83, plain, (![B_63, A_64]: (~r2_hidden(B_63, A_64) | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.55/1.60  tff(c_90, plain, (![A_23]: (~v1_xboole_0(k1_tarski(A_23)))), inference(resolution, [status(thm)], [c_81, c_83])).
% 3.55/1.60  tff(c_56, plain, (![B_54, C_55]: (r1_tarski(k1_tarski(B_54), k2_tarski(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.55/1.60  tff(c_64, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.55/1.60  tff(c_162, plain, (![A_80, B_81]: (k3_xboole_0(A_80, B_81)=A_80 | ~r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.55/1.60  tff(c_188, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_162])).
% 3.55/1.60  tff(c_227, plain, (![A_90, B_91, C_92]: (r1_tarski(A_90, B_91) | ~r1_tarski(A_90, k3_xboole_0(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.55/1.60  tff(c_596, plain, (![A_137, B_138, A_139]: (r1_tarski(A_137, B_138) | ~r1_tarski(A_137, k3_xboole_0(A_139, B_138)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_227])).
% 3.55/1.60  tff(c_739, plain, (![A_156]: (r1_tarski(A_156, k2_tarski('#skF_7', '#skF_8')) | ~r1_tarski(A_156, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_188, c_596])).
% 3.55/1.60  tff(c_14, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.55/1.60  tff(c_936, plain, (![A_172]: (k3_xboole_0(A_172, k2_tarski('#skF_7', '#skF_8'))=A_172 | ~r1_tarski(A_172, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_739, c_14])).
% 3.55/1.60  tff(c_961, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_56, c_936])).
% 3.55/1.60  tff(c_1194, plain, (~r1_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_5')) | v1_xboole_0(k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_961, c_276])).
% 3.55/1.60  tff(c_1209, plain, (~r1_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_90, c_1194])).
% 3.55/1.60  tff(c_1221, plain, (r2_hidden('#skF_5', k2_tarski('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_494, c_1209])).
% 3.55/1.60  tff(c_16, plain, (![D_22, B_18, A_17]: (D_22=B_18 | D_22=A_17 | ~r2_hidden(D_22, k2_tarski(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.55/1.60  tff(c_1224, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_1221, c_16])).
% 3.55/1.60  tff(c_1231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_60, c_1224])).
% 3.55/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.60  
% 3.55/1.60  Inference rules
% 3.55/1.60  ----------------------
% 3.55/1.60  #Ref     : 0
% 3.55/1.60  #Sup     : 293
% 3.55/1.60  #Fact    : 0
% 3.55/1.60  #Define  : 0
% 3.55/1.60  #Split   : 4
% 3.55/1.60  #Chain   : 0
% 3.55/1.60  #Close   : 0
% 3.55/1.60  
% 3.55/1.60  Ordering : KBO
% 3.55/1.60  
% 3.55/1.60  Simplification rules
% 3.55/1.60  ----------------------
% 3.55/1.60  #Subsume      : 69
% 3.55/1.60  #Demod        : 61
% 3.55/1.60  #Tautology    : 105
% 3.55/1.60  #SimpNegUnit  : 39
% 3.55/1.60  #BackRed      : 22
% 3.55/1.60  
% 3.55/1.60  #Partial instantiations: 0
% 3.55/1.60  #Strategies tried      : 1
% 3.55/1.60  
% 3.55/1.60  Timing (in seconds)
% 3.55/1.60  ----------------------
% 3.55/1.61  Preprocessing        : 0.36
% 3.55/1.61  Parsing              : 0.18
% 3.55/1.61  CNF conversion       : 0.03
% 3.55/1.61  Main loop            : 0.48
% 3.55/1.61  Inferencing          : 0.17
% 3.55/1.61  Reduction            : 0.17
% 3.55/1.61  Demodulation         : 0.12
% 3.55/1.61  BG Simplification    : 0.03
% 3.55/1.61  Subsumption          : 0.09
% 3.55/1.61  Abstraction          : 0.02
% 3.55/1.61  MUC search           : 0.00
% 3.55/1.61  Cooper               : 0.00
% 3.55/1.61  Total                : 0.87
% 3.55/1.61  Index Insertion      : 0.00
% 3.55/1.61  Index Deletion       : 0.00
% 3.55/1.61  Index Matching       : 0.00
% 3.55/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
