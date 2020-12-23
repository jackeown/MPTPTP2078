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
% DateTime   : Thu Dec  3 09:42:32 EST 2020

% Result     : Theorem 18.69s
% Output     : CNFRefutation 18.80s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 109 expanded)
%              Number of leaves         :   18 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   94 ( 203 expanded)
%              Number of equality atoms :   22 (  45 expanded)
%              Maximal formula depth    :   11 (   4 average)
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

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B)
          & ! [D] :
              ( ( r1_tarski(A,D)
                & r1_tarski(C,D) )
             => r1_tarski(B,D) ) )
       => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_32,plain,(
    k2_xboole_0('#skF_4','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_79,plain,(
    ! [A_24,B_25] :
      ( k2_xboole_0(A_24,B_25) = B_25
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_90,plain,(
    k2_xboole_0('#skF_6','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_36,c_79])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_596,plain,(
    ! [D_57,B_58,A_59] :
      ( r2_hidden(D_57,B_58)
      | r2_hidden(D_57,A_59)
      | ~ r2_hidden(D_57,k2_xboole_0(A_59,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10948,plain,(
    ! [A_244,B_245,B_246] :
      ( r2_hidden('#skF_1'(k2_xboole_0(A_244,B_245),B_246),B_245)
      | r2_hidden('#skF_1'(k2_xboole_0(A_244,B_245),B_246),A_244)
      | r1_tarski(k2_xboole_0(A_244,B_245),B_246) ) ),
    inference(resolution,[status(thm)],[c_8,c_596])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( ~ r2_hidden(D_13,A_8)
      | r2_hidden(D_13,k2_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_202,plain,(
    ! [A_40,B_41] :
      ( ~ r2_hidden('#skF_1'(A_40,B_41),B_41)
      | r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_227,plain,(
    ! [A_40,A_8,B_9] :
      ( r1_tarski(A_40,k2_xboole_0(A_8,B_9))
      | ~ r2_hidden('#skF_1'(A_40,k2_xboole_0(A_8,B_9)),A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_202])).

tff(c_53798,plain,(
    ! [A_594,B_595,B_596] :
      ( r2_hidden('#skF_1'(k2_xboole_0(A_594,B_595),k2_xboole_0(B_595,B_596)),A_594)
      | r1_tarski(k2_xboole_0(A_594,B_595),k2_xboole_0(B_595,B_596)) ) ),
    inference(resolution,[status(thm)],[c_10948,c_227])).

tff(c_38,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_91,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_38,c_79])).

tff(c_40,plain,(
    ! [B_22,A_23] : k2_xboole_0(B_22,A_23) = k2_xboole_0(A_23,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_55,plain,(
    ! [A_23,B_22] : r1_tarski(A_23,k2_xboole_0(B_22,A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_30])).

tff(c_265,plain,(
    ! [C_44,B_45,A_46] :
      ( r2_hidden(C_44,B_45)
      | ~ r2_hidden(C_44,A_46)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2087,plain,(
    ! [D_97,B_98,A_99,B_100] :
      ( r2_hidden(D_97,B_98)
      | ~ r1_tarski(k2_xboole_0(A_99,B_100),B_98)
      | ~ r2_hidden(D_97,A_99) ) ),
    inference(resolution,[status(thm)],[c_14,c_265])).

tff(c_2133,plain,(
    ! [D_101,B_102,A_103,B_104] :
      ( r2_hidden(D_101,k2_xboole_0(B_102,k2_xboole_0(A_103,B_104)))
      | ~ r2_hidden(D_101,A_103) ) ),
    inference(resolution,[status(thm)],[c_55,c_2087])).

tff(c_2251,plain,(
    ! [D_105,B_106] :
      ( r2_hidden(D_105,k2_xboole_0(B_106,'#skF_5'))
      | ~ r2_hidden(D_105,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_2133])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2303,plain,(
    ! [A_3,B_106] :
      ( r1_tarski(A_3,k2_xboole_0(B_106,'#skF_5'))
      | ~ r2_hidden('#skF_1'(A_3,k2_xboole_0(B_106,'#skF_5')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2251,c_6])).

tff(c_54283,plain,(
    ! [B_597] : r1_tarski(k2_xboole_0('#skF_4',B_597),k2_xboole_0(B_597,'#skF_5')) ),
    inference(resolution,[status(thm)],[c_53798,c_2303])).

tff(c_54392,plain,(
    r1_tarski(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_54283])).

tff(c_229,plain,(
    ! [A_42] : r1_tarski(A_42,A_42) ),
    inference(resolution,[status(thm)],[c_8,c_202])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = B_15
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_239,plain,(
    ! [A_42] : k2_xboole_0(A_42,A_42) = A_42 ),
    inference(resolution,[status(thm)],[c_229,c_28])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_276,plain,(
    ! [A_3,B_4,B_45] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_45)
      | ~ r1_tarski(A_3,B_45)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_265])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | r2_hidden(D_13,k2_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4193,plain,(
    ! [A_170,A_171,B_172] :
      ( r1_tarski(A_170,k2_xboole_0(A_171,B_172))
      | ~ r2_hidden('#skF_1'(A_170,k2_xboole_0(A_171,B_172)),B_172) ) ),
    inference(resolution,[status(thm)],[c_12,c_202])).

tff(c_4342,plain,(
    ! [A_173,B_174,A_175] :
      ( ~ r1_tarski(A_173,B_174)
      | r1_tarski(A_173,k2_xboole_0(A_175,B_174)) ) ),
    inference(resolution,[status(thm)],[c_276,c_4193])).

tff(c_17070,plain,(
    ! [A_316,A_317,B_318] :
      ( k2_xboole_0(A_316,k2_xboole_0(A_317,B_318)) = k2_xboole_0(A_317,B_318)
      | ~ r1_tarski(A_316,B_318) ) ),
    inference(resolution,[status(thm)],[c_4342,c_28])).

tff(c_21618,plain,(
    ! [A_360,B_361,A_362] :
      ( k2_xboole_0(k2_xboole_0(A_360,B_361),A_362) = k2_xboole_0(A_360,B_361)
      | ~ r1_tarski(A_362,B_361) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_17070])).

tff(c_22245,plain,(
    ! [A_42,A_362] :
      ( k2_xboole_0(A_42,A_42) = k2_xboole_0(A_42,A_362)
      | ~ r1_tarski(A_362,A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_21618])).

tff(c_22351,plain,(
    ! [A_42,A_362] :
      ( k2_xboole_0(A_42,A_362) = A_42
      | ~ r1_tarski(A_362,A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_22245])).

tff(c_54481,plain,(
    k2_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_6')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_54392,c_22351])).

tff(c_127,plain,(
    ! [D_28] :
      ( r1_tarski('#skF_5',D_28)
      | ~ r1_tarski('#skF_6',D_28)
      | ~ r1_tarski('#skF_4',D_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_185,plain,(
    ! [D_39] :
      ( k2_xboole_0('#skF_5',D_39) = D_39
      | ~ r1_tarski('#skF_6',D_39)
      | ~ r1_tarski('#skF_4',D_39) ) ),
    inference(resolution,[status(thm)],[c_127,c_28])).

tff(c_330,plain,(
    ! [B_49] :
      ( k2_xboole_0('#skF_5',k2_xboole_0('#skF_6',B_49)) = k2_xboole_0('#skF_6',B_49)
      | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_6',B_49)) ) ),
    inference(resolution,[status(thm)],[c_30,c_185])).

tff(c_342,plain,(
    k2_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_4')) = k2_xboole_0('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_55,c_330])).

tff(c_357,plain,(
    k2_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_6')) = k2_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_342])).

tff(c_54485,plain,(
    k2_xboole_0('#skF_4','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54481,c_357])).

tff(c_54487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_54485])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.69/10.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.80/10.23  
% 18.80/10.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.80/10.24  %$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 18.80/10.24  
% 18.80/10.24  %Foreground sorts:
% 18.80/10.24  
% 18.80/10.24  
% 18.80/10.24  %Background operators:
% 18.80/10.24  
% 18.80/10.24  
% 18.80/10.24  %Foreground operators:
% 18.80/10.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.80/10.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.80/10.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.80/10.24  tff('#skF_5', type, '#skF_5': $i).
% 18.80/10.24  tff('#skF_6', type, '#skF_6': $i).
% 18.80/10.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 18.80/10.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.80/10.24  tff('#skF_4', type, '#skF_4': $i).
% 18.80/10.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 18.80/10.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.80/10.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.80/10.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 18.80/10.24  
% 18.80/10.25  tff(f_63, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 18.80/10.25  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 18.80/10.25  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 18.80/10.25  tff(f_43, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 18.80/10.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 18.80/10.25  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 18.80/10.25  tff(c_32, plain, (k2_xboole_0('#skF_4', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_63])).
% 18.80/10.25  tff(c_36, plain, (r1_tarski('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_63])).
% 18.80/10.25  tff(c_79, plain, (![A_24, B_25]: (k2_xboole_0(A_24, B_25)=B_25 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.80/10.25  tff(c_90, plain, (k2_xboole_0('#skF_6', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_36, c_79])).
% 18.80/10.25  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.80/10.25  tff(c_596, plain, (![D_57, B_58, A_59]: (r2_hidden(D_57, B_58) | r2_hidden(D_57, A_59) | ~r2_hidden(D_57, k2_xboole_0(A_59, B_58)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.80/10.25  tff(c_10948, plain, (![A_244, B_245, B_246]: (r2_hidden('#skF_1'(k2_xboole_0(A_244, B_245), B_246), B_245) | r2_hidden('#skF_1'(k2_xboole_0(A_244, B_245), B_246), A_244) | r1_tarski(k2_xboole_0(A_244, B_245), B_246))), inference(resolution, [status(thm)], [c_8, c_596])).
% 18.80/10.25  tff(c_14, plain, (![D_13, A_8, B_9]: (~r2_hidden(D_13, A_8) | r2_hidden(D_13, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.80/10.25  tff(c_202, plain, (![A_40, B_41]: (~r2_hidden('#skF_1'(A_40, B_41), B_41) | r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.80/10.25  tff(c_227, plain, (![A_40, A_8, B_9]: (r1_tarski(A_40, k2_xboole_0(A_8, B_9)) | ~r2_hidden('#skF_1'(A_40, k2_xboole_0(A_8, B_9)), A_8))), inference(resolution, [status(thm)], [c_14, c_202])).
% 18.80/10.25  tff(c_53798, plain, (![A_594, B_595, B_596]: (r2_hidden('#skF_1'(k2_xboole_0(A_594, B_595), k2_xboole_0(B_595, B_596)), A_594) | r1_tarski(k2_xboole_0(A_594, B_595), k2_xboole_0(B_595, B_596)))), inference(resolution, [status(thm)], [c_10948, c_227])).
% 18.80/10.25  tff(c_38, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_63])).
% 18.80/10.25  tff(c_91, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_38, c_79])).
% 18.80/10.25  tff(c_40, plain, (![B_22, A_23]: (k2_xboole_0(B_22, A_23)=k2_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.80/10.25  tff(c_30, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 18.80/10.25  tff(c_55, plain, (![A_23, B_22]: (r1_tarski(A_23, k2_xboole_0(B_22, A_23)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_30])).
% 18.80/10.25  tff(c_265, plain, (![C_44, B_45, A_46]: (r2_hidden(C_44, B_45) | ~r2_hidden(C_44, A_46) | ~r1_tarski(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.80/10.25  tff(c_2087, plain, (![D_97, B_98, A_99, B_100]: (r2_hidden(D_97, B_98) | ~r1_tarski(k2_xboole_0(A_99, B_100), B_98) | ~r2_hidden(D_97, A_99))), inference(resolution, [status(thm)], [c_14, c_265])).
% 18.80/10.25  tff(c_2133, plain, (![D_101, B_102, A_103, B_104]: (r2_hidden(D_101, k2_xboole_0(B_102, k2_xboole_0(A_103, B_104))) | ~r2_hidden(D_101, A_103))), inference(resolution, [status(thm)], [c_55, c_2087])).
% 18.80/10.25  tff(c_2251, plain, (![D_105, B_106]: (r2_hidden(D_105, k2_xboole_0(B_106, '#skF_5')) | ~r2_hidden(D_105, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_2133])).
% 18.80/10.25  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.80/10.25  tff(c_2303, plain, (![A_3, B_106]: (r1_tarski(A_3, k2_xboole_0(B_106, '#skF_5')) | ~r2_hidden('#skF_1'(A_3, k2_xboole_0(B_106, '#skF_5')), '#skF_4'))), inference(resolution, [status(thm)], [c_2251, c_6])).
% 18.80/10.25  tff(c_54283, plain, (![B_597]: (r1_tarski(k2_xboole_0('#skF_4', B_597), k2_xboole_0(B_597, '#skF_5')))), inference(resolution, [status(thm)], [c_53798, c_2303])).
% 18.80/10.25  tff(c_54392, plain, (r1_tarski(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_90, c_54283])).
% 18.80/10.25  tff(c_229, plain, (![A_42]: (r1_tarski(A_42, A_42))), inference(resolution, [status(thm)], [c_8, c_202])).
% 18.80/10.25  tff(c_28, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=B_15 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.80/10.25  tff(c_239, plain, (![A_42]: (k2_xboole_0(A_42, A_42)=A_42)), inference(resolution, [status(thm)], [c_229, c_28])).
% 18.80/10.25  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.80/10.25  tff(c_276, plain, (![A_3, B_4, B_45]: (r2_hidden('#skF_1'(A_3, B_4), B_45) | ~r1_tarski(A_3, B_45) | r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_265])).
% 18.80/10.25  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | r2_hidden(D_13, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.80/10.25  tff(c_4193, plain, (![A_170, A_171, B_172]: (r1_tarski(A_170, k2_xboole_0(A_171, B_172)) | ~r2_hidden('#skF_1'(A_170, k2_xboole_0(A_171, B_172)), B_172))), inference(resolution, [status(thm)], [c_12, c_202])).
% 18.80/10.25  tff(c_4342, plain, (![A_173, B_174, A_175]: (~r1_tarski(A_173, B_174) | r1_tarski(A_173, k2_xboole_0(A_175, B_174)))), inference(resolution, [status(thm)], [c_276, c_4193])).
% 18.80/10.25  tff(c_17070, plain, (![A_316, A_317, B_318]: (k2_xboole_0(A_316, k2_xboole_0(A_317, B_318))=k2_xboole_0(A_317, B_318) | ~r1_tarski(A_316, B_318))), inference(resolution, [status(thm)], [c_4342, c_28])).
% 18.80/10.25  tff(c_21618, plain, (![A_360, B_361, A_362]: (k2_xboole_0(k2_xboole_0(A_360, B_361), A_362)=k2_xboole_0(A_360, B_361) | ~r1_tarski(A_362, B_361))), inference(superposition, [status(thm), theory('equality')], [c_2, c_17070])).
% 18.80/10.25  tff(c_22245, plain, (![A_42, A_362]: (k2_xboole_0(A_42, A_42)=k2_xboole_0(A_42, A_362) | ~r1_tarski(A_362, A_42))), inference(superposition, [status(thm), theory('equality')], [c_239, c_21618])).
% 18.80/10.25  tff(c_22351, plain, (![A_42, A_362]: (k2_xboole_0(A_42, A_362)=A_42 | ~r1_tarski(A_362, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_22245])).
% 18.80/10.25  tff(c_54481, plain, (k2_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))='#skF_5'), inference(resolution, [status(thm)], [c_54392, c_22351])).
% 18.80/10.25  tff(c_127, plain, (![D_28]: (r1_tarski('#skF_5', D_28) | ~r1_tarski('#skF_6', D_28) | ~r1_tarski('#skF_4', D_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 18.80/10.25  tff(c_185, plain, (![D_39]: (k2_xboole_0('#skF_5', D_39)=D_39 | ~r1_tarski('#skF_6', D_39) | ~r1_tarski('#skF_4', D_39))), inference(resolution, [status(thm)], [c_127, c_28])).
% 18.80/10.25  tff(c_330, plain, (![B_49]: (k2_xboole_0('#skF_5', k2_xboole_0('#skF_6', B_49))=k2_xboole_0('#skF_6', B_49) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_6', B_49)))), inference(resolution, [status(thm)], [c_30, c_185])).
% 18.80/10.25  tff(c_342, plain, (k2_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_4'))=k2_xboole_0('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_55, c_330])).
% 18.80/10.25  tff(c_357, plain, (k2_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))=k2_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_342])).
% 18.80/10.25  tff(c_54485, plain, (k2_xboole_0('#skF_4', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_54481, c_357])).
% 18.80/10.25  tff(c_54487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_54485])).
% 18.80/10.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.80/10.25  
% 18.80/10.25  Inference rules
% 18.80/10.25  ----------------------
% 18.80/10.25  #Ref     : 0
% 18.80/10.25  #Sup     : 13082
% 18.80/10.25  #Fact    : 46
% 18.80/10.25  #Define  : 0
% 18.80/10.25  #Split   : 4
% 18.80/10.25  #Chain   : 0
% 18.80/10.25  #Close   : 0
% 18.80/10.25  
% 18.80/10.25  Ordering : KBO
% 18.80/10.25  
% 18.80/10.25  Simplification rules
% 18.80/10.25  ----------------------
% 18.80/10.25  #Subsume      : 3625
% 18.80/10.25  #Demod        : 17232
% 18.80/10.25  #Tautology    : 4592
% 18.80/10.25  #SimpNegUnit  : 7
% 18.80/10.25  #BackRed      : 1
% 18.80/10.25  
% 18.80/10.25  #Partial instantiations: 0
% 18.80/10.25  #Strategies tried      : 1
% 18.80/10.25  
% 18.80/10.25  Timing (in seconds)
% 18.80/10.25  ----------------------
% 18.80/10.25  Preprocessing        : 0.28
% 18.80/10.25  Parsing              : 0.15
% 18.80/10.25  CNF conversion       : 0.02
% 18.80/10.25  Main loop            : 9.18
% 18.80/10.25  Inferencing          : 1.24
% 18.80/10.25  Reduction            : 4.65
% 18.80/10.25  Demodulation         : 4.19
% 18.80/10.25  BG Simplification    : 0.15
% 18.80/10.25  Subsumption          : 2.77
% 18.80/10.25  Abstraction          : 0.24
% 18.80/10.25  MUC search           : 0.00
% 18.80/10.25  Cooper               : 0.00
% 18.80/10.25  Total                : 9.50
% 18.80/10.25  Index Insertion      : 0.00
% 18.80/10.26  Index Deletion       : 0.00
% 18.80/10.26  Index Matching       : 0.00
% 18.80/10.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
