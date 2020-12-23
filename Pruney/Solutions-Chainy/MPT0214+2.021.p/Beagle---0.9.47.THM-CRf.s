%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:32 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 101 expanded)
%              Number of leaves         :   31 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 ( 150 expanded)
%              Number of equality atoms :   30 (  85 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_45,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_84,plain,(
    r1_tarski(k1_tarski('#skF_8'),k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_197,plain,(
    ! [B_88,A_89] :
      ( k1_tarski(B_88) = A_89
      | k1_xboole_0 = A_89
      | ~ r1_tarski(A_89,k1_tarski(B_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_209,plain,
    ( k1_tarski('#skF_9') = k1_tarski('#skF_8')
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_197])).

tff(c_212,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_52,plain,(
    ! [C_24] : r2_hidden(C_24,k1_tarski(C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_235,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_52])).

tff(c_22,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_3'(A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_170,plain,(
    ! [D_82,A_83,B_84] :
      ( r2_hidden(D_82,A_83)
      | ~ r2_hidden(D_82,k4_xboole_0(A_83,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_175,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_83,B_84)),A_83)
      | k4_xboole_0(A_83,B_84) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_170])).

tff(c_145,plain,(
    ! [D_76,B_77,A_78] :
      ( ~ r2_hidden(D_76,B_77)
      | ~ r2_hidden(D_76,k4_xboole_0(A_78,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_308,plain,(
    ! [A_98,B_99] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_98,B_99)),B_99)
      | k4_xboole_0(A_98,B_99) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_145])).

tff(c_318,plain,(
    ! [A_100] : k4_xboole_0(A_100,A_100) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_175,c_308])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_368,plain,(
    ! [D_105,A_106] :
      ( ~ r2_hidden(D_105,A_106)
      | ~ r2_hidden(D_105,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_4])).

tff(c_374,plain,(
    ~ r2_hidden('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_235,c_368])).

tff(c_394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_374])).

tff(c_396,plain,(
    k1_tarski('#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_82,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_395,plain,(
    k1_tarski('#skF_9') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_115,plain,(
    ! [A_71] :
      ( r2_hidden('#skF_3'(A_71),A_71)
      | k1_xboole_0 = A_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_50,plain,(
    ! [C_24,A_20] :
      ( C_24 = A_20
      | ~ r2_hidden(C_24,k1_tarski(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_120,plain,(
    ! [A_20] :
      ( '#skF_3'(k1_tarski(A_20)) = A_20
      | k1_tarski(A_20) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_115,c_50])).

tff(c_405,plain,
    ( '#skF_3'(k1_tarski('#skF_8')) = '#skF_9'
    | k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_120])).

tff(c_423,plain,
    ( '#skF_3'(k1_tarski('#skF_8')) = '#skF_9'
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_405])).

tff(c_424,plain,(
    '#skF_3'(k1_tarski('#skF_8')) = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_396,c_423])).

tff(c_432,plain,
    ( '#skF_9' = '#skF_8'
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_120])).

tff(c_442,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_396,c_82,c_432])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:08:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.37  
% 2.47/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.37  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_7
% 2.47/1.37  
% 2.47/1.37  %Foreground sorts:
% 2.47/1.37  
% 2.47/1.37  
% 2.47/1.37  %Background operators:
% 2.47/1.37  
% 2.47/1.37  
% 2.47/1.37  %Foreground operators:
% 2.47/1.37  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.47/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.47/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.47/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.47/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.47/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.37  tff('#skF_9', type, '#skF_9': $i).
% 2.47/1.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.47/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.37  tff('#skF_8', type, '#skF_8': $i).
% 2.47/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.37  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.47/1.37  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.47/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.37  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.47/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.37  
% 2.47/1.39  tff(f_94, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.47/1.39  tff(f_89, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.47/1.39  tff(f_69, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.47/1.39  tff(f_45, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.47/1.39  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.47/1.39  tff(c_84, plain, (r1_tarski(k1_tarski('#skF_8'), k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.47/1.39  tff(c_197, plain, (![B_88, A_89]: (k1_tarski(B_88)=A_89 | k1_xboole_0=A_89 | ~r1_tarski(A_89, k1_tarski(B_88)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.47/1.39  tff(c_209, plain, (k1_tarski('#skF_9')=k1_tarski('#skF_8') | k1_tarski('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_84, c_197])).
% 2.47/1.39  tff(c_212, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_209])).
% 2.47/1.39  tff(c_52, plain, (![C_24]: (r2_hidden(C_24, k1_tarski(C_24)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.47/1.39  tff(c_235, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_212, c_52])).
% 2.47/1.39  tff(c_22, plain, (![A_9]: (r2_hidden('#skF_3'(A_9), A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.47/1.39  tff(c_170, plain, (![D_82, A_83, B_84]: (r2_hidden(D_82, A_83) | ~r2_hidden(D_82, k4_xboole_0(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.39  tff(c_175, plain, (![A_83, B_84]: (r2_hidden('#skF_3'(k4_xboole_0(A_83, B_84)), A_83) | k4_xboole_0(A_83, B_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_170])).
% 2.47/1.39  tff(c_145, plain, (![D_76, B_77, A_78]: (~r2_hidden(D_76, B_77) | ~r2_hidden(D_76, k4_xboole_0(A_78, B_77)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.39  tff(c_308, plain, (![A_98, B_99]: (~r2_hidden('#skF_3'(k4_xboole_0(A_98, B_99)), B_99) | k4_xboole_0(A_98, B_99)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_145])).
% 2.47/1.39  tff(c_318, plain, (![A_100]: (k4_xboole_0(A_100, A_100)=k1_xboole_0)), inference(resolution, [status(thm)], [c_175, c_308])).
% 2.47/1.39  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.39  tff(c_368, plain, (![D_105, A_106]: (~r2_hidden(D_105, A_106) | ~r2_hidden(D_105, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_318, c_4])).
% 2.47/1.39  tff(c_374, plain, (~r2_hidden('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_235, c_368])).
% 2.47/1.39  tff(c_394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_235, c_374])).
% 2.47/1.39  tff(c_396, plain, (k1_tarski('#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_209])).
% 2.47/1.39  tff(c_82, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.47/1.39  tff(c_395, plain, (k1_tarski('#skF_9')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_209])).
% 2.47/1.39  tff(c_115, plain, (![A_71]: (r2_hidden('#skF_3'(A_71), A_71) | k1_xboole_0=A_71)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.47/1.39  tff(c_50, plain, (![C_24, A_20]: (C_24=A_20 | ~r2_hidden(C_24, k1_tarski(A_20)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.47/1.39  tff(c_120, plain, (![A_20]: ('#skF_3'(k1_tarski(A_20))=A_20 | k1_tarski(A_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_115, c_50])).
% 2.47/1.39  tff(c_405, plain, ('#skF_3'(k1_tarski('#skF_8'))='#skF_9' | k1_tarski('#skF_9')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_395, c_120])).
% 2.47/1.39  tff(c_423, plain, ('#skF_3'(k1_tarski('#skF_8'))='#skF_9' | k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_395, c_405])).
% 2.47/1.39  tff(c_424, plain, ('#skF_3'(k1_tarski('#skF_8'))='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_396, c_423])).
% 2.47/1.39  tff(c_432, plain, ('#skF_9'='#skF_8' | k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_424, c_120])).
% 2.47/1.39  tff(c_442, plain, $false, inference(negUnitSimplification, [status(thm)], [c_396, c_82, c_432])).
% 2.47/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.39  
% 2.47/1.39  Inference rules
% 2.47/1.39  ----------------------
% 2.47/1.39  #Ref     : 0
% 2.47/1.39  #Sup     : 87
% 2.47/1.39  #Fact    : 0
% 2.47/1.39  #Define  : 0
% 2.47/1.39  #Split   : 1
% 2.47/1.39  #Chain   : 0
% 2.47/1.39  #Close   : 0
% 2.47/1.39  
% 2.47/1.39  Ordering : KBO
% 2.47/1.39  
% 2.47/1.39  Simplification rules
% 2.47/1.39  ----------------------
% 2.47/1.39  #Subsume      : 1
% 2.47/1.39  #Demod        : 26
% 2.47/1.39  #Tautology    : 50
% 2.47/1.39  #SimpNegUnit  : 2
% 2.47/1.39  #BackRed      : 3
% 2.47/1.39  
% 2.47/1.39  #Partial instantiations: 0
% 2.47/1.39  #Strategies tried      : 1
% 2.47/1.39  
% 2.47/1.39  Timing (in seconds)
% 2.47/1.39  ----------------------
% 2.47/1.39  Preprocessing        : 0.42
% 2.47/1.39  Parsing              : 0.22
% 2.47/1.39  CNF conversion       : 0.03
% 2.47/1.39  Main loop            : 0.23
% 2.47/1.39  Inferencing          : 0.07
% 2.47/1.39  Reduction            : 0.08
% 2.47/1.39  Demodulation         : 0.06
% 2.47/1.39  BG Simplification    : 0.02
% 2.47/1.39  Subsumption          : 0.04
% 2.47/1.39  Abstraction          : 0.01
% 2.47/1.39  MUC search           : 0.00
% 2.47/1.39  Cooper               : 0.00
% 2.47/1.39  Total                : 0.67
% 2.47/1.39  Index Insertion      : 0.00
% 2.47/1.39  Index Deletion       : 0.00
% 2.47/1.39  Index Matching       : 0.00
% 2.47/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
