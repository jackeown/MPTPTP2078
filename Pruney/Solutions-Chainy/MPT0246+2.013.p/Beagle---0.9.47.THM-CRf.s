%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:01 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   53 (  70 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 114 expanded)
%              Number of equality atoms :   38 (  63 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_66,plain,(
    ! [A_34] :
      ( r2_hidden('#skF_3'(A_34),A_34)
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_48,plain,(
    ! [C_28] :
      ( C_28 = '#skF_5'
      | ~ r2_hidden(C_28,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_70,plain,
    ( '#skF_3'('#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_48])).

tff(c_73,plain,(
    '#skF_3'('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_70])).

tff(c_22,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_3'(A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_77,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_22])).

tff(c_80,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_77])).

tff(c_46,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(k1_tarski(A_25),B_26) = k1_xboole_0
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_52,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_97,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_105,plain,(
    ! [B_12] : k4_xboole_0(B_12,B_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_97])).

tff(c_191,plain,(
    ! [A_55,B_56] :
      ( r2_hidden(A_55,B_56)
      | k4_xboole_0(k1_tarski(A_55),B_56) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_200,plain,(
    ! [A_55] : r2_hidden(A_55,k1_tarski(A_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_191])).

tff(c_224,plain,(
    ! [D_63,A_64,B_65] :
      ( r2_hidden(D_63,A_64)
      | ~ r2_hidden(D_63,k4_xboole_0(A_64,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_280,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_74,B_75)),A_74)
      | k4_xboole_0(A_74,B_75) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_224])).

tff(c_306,plain,(
    ! [B_75] :
      ( '#skF_3'(k4_xboole_0('#skF_4',B_75)) = '#skF_5'
      | k4_xboole_0('#skF_4',B_75) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_280,c_48])).

tff(c_212,plain,(
    ! [D_60,B_61,A_62] :
      ( ~ r2_hidden(D_60,B_61)
      | ~ r2_hidden(D_60,k4_xboole_0(A_62,B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_383,plain,(
    ! [A_81,B_82] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_81,B_82)),B_82)
      | k4_xboole_0(A_81,B_82) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_212])).

tff(c_490,plain,(
    ! [B_92] :
      ( ~ r2_hidden('#skF_5',B_92)
      | k4_xboole_0('#skF_4',B_92) = k1_xboole_0
      | k4_xboole_0('#skF_4',B_92) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_383])).

tff(c_503,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_200,c_490])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | k4_xboole_0(A_13,B_14) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_202,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_245,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | k4_xboole_0(A_70,B_69) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_202])).

tff(c_252,plain,(
    ! [B_14,A_13] :
      ( B_14 = A_13
      | k4_xboole_0(B_14,A_13) != k1_xboole_0
      | k4_xboole_0(A_13,B_14) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_245])).

tff(c_508,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_252])).

tff(c_540,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_508])).

tff(c_550,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_540])).

tff(c_554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_550])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.36  
% 2.30/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.30/1.37  
% 2.30/1.37  %Foreground sorts:
% 2.30/1.37  
% 2.30/1.37  
% 2.30/1.37  %Background operators:
% 2.30/1.37  
% 2.30/1.37  
% 2.30/1.37  %Foreground operators:
% 2.30/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.30/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.30/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.30/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.30/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.30/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.30/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.30/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.30/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.30/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.30/1.37  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.30/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.37  
% 2.30/1.38  tff(f_89, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.30/1.38  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.30/1.38  tff(f_74, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.30/1.38  tff(f_53, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.30/1.38  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.30/1.38  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.30/1.38  tff(c_50, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.30/1.38  tff(c_66, plain, (![A_34]: (r2_hidden('#skF_3'(A_34), A_34) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.30/1.38  tff(c_48, plain, (![C_28]: (C_28='#skF_5' | ~r2_hidden(C_28, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.30/1.38  tff(c_70, plain, ('#skF_3'('#skF_4')='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_66, c_48])).
% 2.30/1.38  tff(c_73, plain, ('#skF_3'('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_50, c_70])).
% 2.30/1.38  tff(c_22, plain, (![A_9]: (r2_hidden('#skF_3'(A_9), A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.30/1.38  tff(c_77, plain, (r2_hidden('#skF_5', '#skF_4') | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_73, c_22])).
% 2.30/1.38  tff(c_80, plain, (r2_hidden('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_77])).
% 2.30/1.38  tff(c_46, plain, (![A_25, B_26]: (k4_xboole_0(k1_tarski(A_25), B_26)=k1_xboole_0 | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.30/1.38  tff(c_52, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.30/1.38  tff(c_28, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.30/1.38  tff(c_97, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.30/1.38  tff(c_105, plain, (![B_12]: (k4_xboole_0(B_12, B_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_97])).
% 2.30/1.38  tff(c_191, plain, (![A_55, B_56]: (r2_hidden(A_55, B_56) | k4_xboole_0(k1_tarski(A_55), B_56)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.30/1.38  tff(c_200, plain, (![A_55]: (r2_hidden(A_55, k1_tarski(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_105, c_191])).
% 2.30/1.38  tff(c_224, plain, (![D_63, A_64, B_65]: (r2_hidden(D_63, A_64) | ~r2_hidden(D_63, k4_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.30/1.38  tff(c_280, plain, (![A_74, B_75]: (r2_hidden('#skF_3'(k4_xboole_0(A_74, B_75)), A_74) | k4_xboole_0(A_74, B_75)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_224])).
% 2.30/1.38  tff(c_306, plain, (![B_75]: ('#skF_3'(k4_xboole_0('#skF_4', B_75))='#skF_5' | k4_xboole_0('#skF_4', B_75)=k1_xboole_0)), inference(resolution, [status(thm)], [c_280, c_48])).
% 2.30/1.38  tff(c_212, plain, (![D_60, B_61, A_62]: (~r2_hidden(D_60, B_61) | ~r2_hidden(D_60, k4_xboole_0(A_62, B_61)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.30/1.38  tff(c_383, plain, (![A_81, B_82]: (~r2_hidden('#skF_3'(k4_xboole_0(A_81, B_82)), B_82) | k4_xboole_0(A_81, B_82)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_212])).
% 2.30/1.38  tff(c_490, plain, (![B_92]: (~r2_hidden('#skF_5', B_92) | k4_xboole_0('#skF_4', B_92)=k1_xboole_0 | k4_xboole_0('#skF_4', B_92)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_306, c_383])).
% 2.30/1.38  tff(c_503, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_200, c_490])).
% 2.30/1.38  tff(c_30, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | k4_xboole_0(A_13, B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.30/1.38  tff(c_202, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.30/1.38  tff(c_245, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | k4_xboole_0(A_70, B_69)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_202])).
% 2.30/1.38  tff(c_252, plain, (![B_14, A_13]: (B_14=A_13 | k4_xboole_0(B_14, A_13)!=k1_xboole_0 | k4_xboole_0(A_13, B_14)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_245])).
% 2.30/1.38  tff(c_508, plain, (k1_tarski('#skF_5')='#skF_4' | k4_xboole_0(k1_tarski('#skF_5'), '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_503, c_252])).
% 2.30/1.38  tff(c_540, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_52, c_508])).
% 2.30/1.38  tff(c_550, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_46, c_540])).
% 2.30/1.38  tff(c_554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_550])).
% 2.30/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.38  
% 2.30/1.38  Inference rules
% 2.30/1.38  ----------------------
% 2.30/1.38  #Ref     : 0
% 2.30/1.38  #Sup     : 113
% 2.30/1.38  #Fact    : 0
% 2.30/1.38  #Define  : 0
% 2.30/1.38  #Split   : 0
% 2.30/1.38  #Chain   : 0
% 2.30/1.38  #Close   : 0
% 2.30/1.38  
% 2.30/1.38  Ordering : KBO
% 2.30/1.38  
% 2.30/1.38  Simplification rules
% 2.30/1.38  ----------------------
% 2.30/1.38  #Subsume      : 17
% 2.30/1.38  #Demod        : 26
% 2.30/1.38  #Tautology    : 59
% 2.30/1.38  #SimpNegUnit  : 9
% 2.30/1.38  #BackRed      : 0
% 2.30/1.38  
% 2.30/1.38  #Partial instantiations: 0
% 2.30/1.38  #Strategies tried      : 1
% 2.30/1.38  
% 2.30/1.38  Timing (in seconds)
% 2.30/1.38  ----------------------
% 2.30/1.38  Preprocessing        : 0.31
% 2.30/1.38  Parsing              : 0.16
% 2.30/1.38  CNF conversion       : 0.02
% 2.30/1.38  Main loop            : 0.24
% 2.30/1.38  Inferencing          : 0.09
% 2.30/1.38  Reduction            : 0.07
% 2.30/1.38  Demodulation         : 0.05
% 2.30/1.38  BG Simplification    : 0.01
% 2.30/1.38  Subsumption          : 0.05
% 2.30/1.38  Abstraction          : 0.01
% 2.30/1.38  MUC search           : 0.00
% 2.30/1.38  Cooper               : 0.00
% 2.30/1.38  Total                : 0.58
% 2.30/1.38  Index Insertion      : 0.00
% 2.30/1.38  Index Deletion       : 0.00
% 2.30/1.38  Index Matching       : 0.00
% 2.30/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
