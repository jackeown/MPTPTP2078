%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:44 EST 2020

% Result     : Theorem 4.89s
% Output     : CNFRefutation 4.89s
% Verified   : 
% Statistics : Number of formulae       :   60 (  98 expanded)
%              Number of leaves         :   30 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :   69 ( 147 expanded)
%              Number of equality atoms :   27 (  60 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_67,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_77,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_88,plain,(
    k1_tarski('#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_133,plain,(
    ! [B_55,A_56] : k2_xboole_0(B_55,A_56) = k2_xboole_0(A_56,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_54,plain,(
    ! [A_25] : k2_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_149,plain,(
    ! [A_56] : k2_xboole_0(k1_xboole_0,A_56) = A_56 ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_54])).

tff(c_220,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k2_xboole_0(A_58,B_59)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_227,plain,(
    ! [A_56] : k4_xboole_0(k1_xboole_0,A_56) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_220])).

tff(c_573,plain,(
    ! [B_87,A_88] :
      ( ~ r2_hidden(B_87,A_88)
      | k4_xboole_0(A_88,k1_tarski(B_87)) != A_88 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_589,plain,(
    ! [B_87] : ~ r2_hidden(B_87,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_573])).

tff(c_92,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3057,plain,(
    ! [D_174,A_175,B_176] :
      ( r2_hidden(D_174,k4_xboole_0(A_175,B_176))
      | r2_hidden(D_174,B_176)
      | ~ r2_hidden(D_174,A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3105,plain,(
    ! [D_174] :
      ( r2_hidden(D_174,k1_xboole_0)
      | r2_hidden(D_174,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_174,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_3057])).

tff(c_3124,plain,(
    ! [D_177] :
      ( r2_hidden(D_177,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_177,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_589,c_3105])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5253,plain,(
    ! [A_225] :
      ( r1_tarski(A_225,k1_tarski('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_225,k1_tarski('#skF_7')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3124,c_6])).

tff(c_5271,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_8,c_5253])).

tff(c_42,plain,(
    ! [B_20,A_19] :
      ( B_20 = A_19
      | ~ r1_tarski(B_20,A_19)
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5278,plain,
    ( k1_tarski('#skF_7') = '#skF_6'
    | ~ r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_5271,c_42])).

tff(c_5289,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_5278])).

tff(c_90,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_525,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(A_85,k1_tarski(B_86)) = A_85
      | r2_hidden(B_86,A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_548,plain,
    ( k1_xboole_0 = '#skF_6'
    | r2_hidden('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_525,c_92])).

tff(c_567,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_548])).

tff(c_788,plain,(
    ! [A_103,B_104] :
      ( r2_hidden('#skF_1'(A_103,B_104),A_103)
      | r1_tarski(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_66,plain,(
    ! [C_39,A_35] :
      ( C_39 = A_35
      | ~ r2_hidden(C_39,k1_tarski(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_5596,plain,(
    ! [A_241,B_242] :
      ( '#skF_1'(k1_tarski(A_241),B_242) = A_241
      | r1_tarski(k1_tarski(A_241),B_242) ) ),
    inference(resolution,[status(thm)],[c_788,c_66])).

tff(c_5625,plain,(
    '#skF_1'(k1_tarski('#skF_7'),'#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_5596,c_5289])).

tff(c_5696,plain,
    ( ~ r2_hidden('#skF_7','#skF_6')
    | r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5625,c_6])).

tff(c_5702,plain,(
    r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_5696])).

tff(c_5704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5289,c_5702])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.89/1.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.89/1.94  
% 4.89/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.89/1.95  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 4.89/1.95  
% 4.89/1.95  %Foreground sorts:
% 4.89/1.95  
% 4.89/1.95  
% 4.89/1.95  %Background operators:
% 4.89/1.95  
% 4.89/1.95  
% 4.89/1.95  %Foreground operators:
% 4.89/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.89/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.89/1.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.89/1.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.89/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.89/1.95  tff('#skF_7', type, '#skF_7': $i).
% 4.89/1.95  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.89/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.89/1.95  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.89/1.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.89/1.95  tff('#skF_6', type, '#skF_6': $i).
% 4.89/1.95  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.89/1.95  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.89/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.89/1.95  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.89/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.89/1.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.89/1.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.89/1.95  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.89/1.95  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.89/1.95  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.89/1.95  
% 4.89/1.96  tff(f_107, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 4.89/1.96  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.89/1.96  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.89/1.96  tff(f_67, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.89/1.96  tff(f_77, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.89/1.96  tff(f_97, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.89/1.96  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.89/1.96  tff(f_59, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.89/1.96  tff(f_86, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.89/1.96  tff(c_88, plain, (k1_tarski('#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.89/1.96  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.89/1.96  tff(c_133, plain, (![B_55, A_56]: (k2_xboole_0(B_55, A_56)=k2_xboole_0(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.89/1.96  tff(c_54, plain, (![A_25]: (k2_xboole_0(A_25, k1_xboole_0)=A_25)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.89/1.96  tff(c_149, plain, (![A_56]: (k2_xboole_0(k1_xboole_0, A_56)=A_56)), inference(superposition, [status(thm), theory('equality')], [c_133, c_54])).
% 4.89/1.96  tff(c_220, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k2_xboole_0(A_58, B_59))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.89/1.96  tff(c_227, plain, (![A_56]: (k4_xboole_0(k1_xboole_0, A_56)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_149, c_220])).
% 4.89/1.96  tff(c_573, plain, (![B_87, A_88]: (~r2_hidden(B_87, A_88) | k4_xboole_0(A_88, k1_tarski(B_87))!=A_88)), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.89/1.96  tff(c_589, plain, (![B_87]: (~r2_hidden(B_87, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_227, c_573])).
% 4.89/1.96  tff(c_92, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.89/1.96  tff(c_3057, plain, (![D_174, A_175, B_176]: (r2_hidden(D_174, k4_xboole_0(A_175, B_176)) | r2_hidden(D_174, B_176) | ~r2_hidden(D_174, A_175))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.89/1.96  tff(c_3105, plain, (![D_174]: (r2_hidden(D_174, k1_xboole_0) | r2_hidden(D_174, k1_tarski('#skF_7')) | ~r2_hidden(D_174, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_3057])).
% 4.89/1.96  tff(c_3124, plain, (![D_177]: (r2_hidden(D_177, k1_tarski('#skF_7')) | ~r2_hidden(D_177, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_589, c_3105])).
% 4.89/1.96  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.89/1.96  tff(c_5253, plain, (![A_225]: (r1_tarski(A_225, k1_tarski('#skF_7')) | ~r2_hidden('#skF_1'(A_225, k1_tarski('#skF_7')), '#skF_6'))), inference(resolution, [status(thm)], [c_3124, c_6])).
% 4.89/1.96  tff(c_5271, plain, (r1_tarski('#skF_6', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_8, c_5253])).
% 4.89/1.96  tff(c_42, plain, (![B_20, A_19]: (B_20=A_19 | ~r1_tarski(B_20, A_19) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.89/1.96  tff(c_5278, plain, (k1_tarski('#skF_7')='#skF_6' | ~r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_5271, c_42])).
% 4.89/1.96  tff(c_5289, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_88, c_5278])).
% 4.89/1.96  tff(c_90, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.89/1.96  tff(c_525, plain, (![A_85, B_86]: (k4_xboole_0(A_85, k1_tarski(B_86))=A_85 | r2_hidden(B_86, A_85))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.89/1.96  tff(c_548, plain, (k1_xboole_0='#skF_6' | r2_hidden('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_525, c_92])).
% 4.89/1.96  tff(c_567, plain, (r2_hidden('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_90, c_548])).
% 4.89/1.96  tff(c_788, plain, (![A_103, B_104]: (r2_hidden('#skF_1'(A_103, B_104), A_103) | r1_tarski(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.89/1.96  tff(c_66, plain, (![C_39, A_35]: (C_39=A_35 | ~r2_hidden(C_39, k1_tarski(A_35)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.89/1.96  tff(c_5596, plain, (![A_241, B_242]: ('#skF_1'(k1_tarski(A_241), B_242)=A_241 | r1_tarski(k1_tarski(A_241), B_242))), inference(resolution, [status(thm)], [c_788, c_66])).
% 4.89/1.96  tff(c_5625, plain, ('#skF_1'(k1_tarski('#skF_7'), '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_5596, c_5289])).
% 4.89/1.96  tff(c_5696, plain, (~r2_hidden('#skF_7', '#skF_6') | r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5625, c_6])).
% 4.89/1.96  tff(c_5702, plain, (r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_567, c_5696])).
% 4.89/1.96  tff(c_5704, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5289, c_5702])).
% 4.89/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.89/1.96  
% 4.89/1.96  Inference rules
% 4.89/1.96  ----------------------
% 4.89/1.96  #Ref     : 0
% 4.89/1.96  #Sup     : 1358
% 4.89/1.96  #Fact    : 0
% 4.89/1.96  #Define  : 0
% 4.89/1.96  #Split   : 0
% 4.89/1.96  #Chain   : 0
% 4.89/1.96  #Close   : 0
% 4.89/1.96  
% 4.89/1.96  Ordering : KBO
% 4.89/1.96  
% 4.89/1.96  Simplification rules
% 4.89/1.96  ----------------------
% 4.89/1.96  #Subsume      : 191
% 4.89/1.96  #Demod        : 1007
% 4.89/1.96  #Tautology    : 810
% 4.89/1.96  #SimpNegUnit  : 83
% 4.89/1.96  #BackRed      : 0
% 4.89/1.96  
% 4.89/1.96  #Partial instantiations: 0
% 4.89/1.96  #Strategies tried      : 1
% 4.89/1.96  
% 4.89/1.96  Timing (in seconds)
% 4.89/1.96  ----------------------
% 4.89/1.96  Preprocessing        : 0.33
% 4.89/1.96  Parsing              : 0.17
% 4.89/1.96  CNF conversion       : 0.03
% 4.89/1.96  Main loop            : 0.87
% 4.89/1.96  Inferencing          : 0.26
% 4.89/1.96  Reduction            : 0.37
% 4.89/1.96  Demodulation         : 0.29
% 4.89/1.96  BG Simplification    : 0.03
% 4.89/1.96  Subsumption          : 0.16
% 4.89/1.96  Abstraction          : 0.04
% 4.89/1.96  MUC search           : 0.00
% 4.89/1.96  Cooper               : 0.00
% 4.89/1.96  Total                : 1.23
% 4.89/1.96  Index Insertion      : 0.00
% 4.89/1.96  Index Deletion       : 0.00
% 4.89/1.96  Index Matching       : 0.00
% 4.89/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
