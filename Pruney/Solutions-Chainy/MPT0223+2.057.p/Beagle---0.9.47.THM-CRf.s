%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:24 EST 2020

% Result     : Theorem 4.28s
% Output     : CNFRefutation 4.28s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 171 expanded)
%              Number of leaves         :   25 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 326 expanded)
%              Number of equality atoms :   37 ( 155 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_74,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_84,plain,(
    ! [A_46,B_47] :
      ( r1_xboole_0(k1_tarski(A_46),B_47)
      | r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_214,plain,(
    ! [A_71,B_72] :
      ( k3_xboole_0(k1_tarski(A_71),B_72) = k1_xboole_0
      | r2_hidden(A_71,B_72) ) ),
    inference(resolution,[status(thm)],[c_84,c_2])).

tff(c_56,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_223,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | r2_hidden('#skF_4',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_56])).

tff(c_242,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_28,plain,(
    ! [E_22,B_17,C_18] : r2_hidden(E_22,k1_enumset1(E_22,B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_52,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(k1_tarski(A_29),B_30)
      | r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_243,plain,(
    ! [A_73,B_74,C_75] :
      ( ~ r1_xboole_0(A_73,B_74)
      | ~ r2_hidden(C_75,B_74)
      | ~ r2_hidden(C_75,A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_372,plain,(
    ! [C_83,B_84,A_85] :
      ( ~ r2_hidden(C_83,B_84)
      | ~ r2_hidden(C_83,k1_tarski(A_85))
      | r2_hidden(A_85,B_84) ) ),
    inference(resolution,[status(thm)],[c_52,c_243])).

tff(c_1584,plain,(
    ! [E_2127,A_2128,B_2129,C_2130] :
      ( ~ r2_hidden(E_2127,k1_tarski(A_2128))
      | r2_hidden(A_2128,k1_enumset1(E_2127,B_2129,C_2130)) ) ),
    inference(resolution,[status(thm)],[c_28,c_372])).

tff(c_1616,plain,(
    ! [B_2155,C_2156] : r2_hidden('#skF_5',k1_enumset1('#skF_4',B_2155,C_2156)) ),
    inference(resolution,[status(thm)],[c_242,c_1584])).

tff(c_22,plain,(
    ! [E_22,C_18,B_17,A_16] :
      ( E_22 = C_18
      | E_22 = B_17
      | E_22 = A_16
      | ~ r2_hidden(E_22,k1_enumset1(A_16,B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1623,plain,(
    ! [C_2156,B_2155] :
      ( C_2156 = '#skF_5'
      | B_2155 = '#skF_5'
      | '#skF_5' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_1616,c_22])).

tff(c_1680,plain,(
    ! [C_2156,B_2155] :
      ( C_2156 = '#skF_5'
      | B_2155 = '#skF_5' ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1623])).

tff(c_1685,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1680])).

tff(c_1683,plain,(
    ! [B_2155] : B_2155 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1680])).

tff(c_1954,plain,(
    ! [B_4174] : B_4174 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1685,c_1683])).

tff(c_2230,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1954,c_54])).

tff(c_2233,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1680])).

tff(c_2231,plain,(
    ! [C_2156] : C_2156 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1680])).

tff(c_2502,plain,(
    ! [C_8208] : C_8208 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2233,c_2231])).

tff(c_2778,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_2502,c_54])).

tff(c_2779,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_46,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_111,plain,(
    ! [A_52,B_53] : k1_enumset1(A_52,A_52,B_53) = k2_tarski(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_129,plain,(
    ! [A_54,B_55] : r2_hidden(A_54,k2_tarski(A_54,B_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_28])).

tff(c_132,plain,(
    ! [A_23] : r2_hidden(A_23,k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_129])).

tff(c_2788,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2779,c_132])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2795,plain,(
    ! [A_10249,B_10250,C_10251] :
      ( ~ r1_xboole_0(A_10249,B_10250)
      | ~ r2_hidden(C_10251,B_10250)
      | ~ r2_hidden(C_10251,A_10249) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3026,plain,(
    ! [C_10263,B_10264,A_10265] :
      ( ~ r2_hidden(C_10263,B_10264)
      | ~ r2_hidden(C_10263,A_10265)
      | k3_xboole_0(A_10265,B_10264) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_2795])).

tff(c_3063,plain,(
    ! [A_10266] :
      ( ~ r2_hidden('#skF_4',A_10266)
      | k3_xboole_0(A_10266,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2788,c_3026])).

tff(c_3075,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2788,c_3063])).

tff(c_3106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3075])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.28/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.28/1.70  
% 4.28/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.28/1.70  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.28/1.70  
% 4.28/1.70  %Foreground sorts:
% 4.28/1.70  
% 4.28/1.70  
% 4.28/1.70  %Background operators:
% 4.28/1.70  
% 4.28/1.70  
% 4.28/1.70  %Foreground operators:
% 4.28/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.28/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.28/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.28/1.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.28/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.28/1.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.28/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.28/1.70  tff('#skF_5', type, '#skF_5': $i).
% 4.28/1.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.28/1.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.28/1.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.28/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.28/1.70  tff('#skF_4', type, '#skF_4': $i).
% 4.28/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.28/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.28/1.70  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.28/1.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.28/1.70  
% 4.28/1.72  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.28/1.72  tff(f_88, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 4.28/1.72  tff(f_83, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.28/1.72  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.28/1.72  tff(f_72, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.28/1.72  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.28/1.72  tff(f_74, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.28/1.72  tff(f_76, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.28/1.72  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.28/1.72  tff(c_54, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.28/1.72  tff(c_84, plain, (![A_46, B_47]: (r1_xboole_0(k1_tarski(A_46), B_47) | r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.28/1.72  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.28/1.72  tff(c_214, plain, (![A_71, B_72]: (k3_xboole_0(k1_tarski(A_71), B_72)=k1_xboole_0 | r2_hidden(A_71, B_72))), inference(resolution, [status(thm)], [c_84, c_2])).
% 4.28/1.72  tff(c_56, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.28/1.72  tff(c_223, plain, (k1_tarski('#skF_4')=k1_xboole_0 | r2_hidden('#skF_4', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_214, c_56])).
% 4.28/1.72  tff(c_242, plain, (r2_hidden('#skF_4', k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_223])).
% 4.28/1.72  tff(c_28, plain, (![E_22, B_17, C_18]: (r2_hidden(E_22, k1_enumset1(E_22, B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.28/1.72  tff(c_52, plain, (![A_29, B_30]: (r1_xboole_0(k1_tarski(A_29), B_30) | r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.28/1.72  tff(c_243, plain, (![A_73, B_74, C_75]: (~r1_xboole_0(A_73, B_74) | ~r2_hidden(C_75, B_74) | ~r2_hidden(C_75, A_73))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.28/1.72  tff(c_372, plain, (![C_83, B_84, A_85]: (~r2_hidden(C_83, B_84) | ~r2_hidden(C_83, k1_tarski(A_85)) | r2_hidden(A_85, B_84))), inference(resolution, [status(thm)], [c_52, c_243])).
% 4.28/1.72  tff(c_1584, plain, (![E_2127, A_2128, B_2129, C_2130]: (~r2_hidden(E_2127, k1_tarski(A_2128)) | r2_hidden(A_2128, k1_enumset1(E_2127, B_2129, C_2130)))), inference(resolution, [status(thm)], [c_28, c_372])).
% 4.28/1.72  tff(c_1616, plain, (![B_2155, C_2156]: (r2_hidden('#skF_5', k1_enumset1('#skF_4', B_2155, C_2156)))), inference(resolution, [status(thm)], [c_242, c_1584])).
% 4.28/1.72  tff(c_22, plain, (![E_22, C_18, B_17, A_16]: (E_22=C_18 | E_22=B_17 | E_22=A_16 | ~r2_hidden(E_22, k1_enumset1(A_16, B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.28/1.72  tff(c_1623, plain, (![C_2156, B_2155]: (C_2156='#skF_5' | B_2155='#skF_5' | '#skF_5'='#skF_4')), inference(resolution, [status(thm)], [c_1616, c_22])).
% 4.28/1.72  tff(c_1680, plain, (![C_2156, B_2155]: (C_2156='#skF_5' | B_2155='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_1623])).
% 4.28/1.72  tff(c_1685, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_1680])).
% 4.28/1.72  tff(c_1683, plain, (![B_2155]: (B_2155='#skF_5')), inference(splitLeft, [status(thm)], [c_1680])).
% 4.28/1.72  tff(c_1954, plain, (![B_4174]: (B_4174='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1685, c_1683])).
% 4.28/1.72  tff(c_2230, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1954, c_54])).
% 4.28/1.72  tff(c_2233, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_1680])).
% 4.28/1.72  tff(c_2231, plain, (![C_2156]: (C_2156='#skF_5')), inference(splitRight, [status(thm)], [c_1680])).
% 4.28/1.72  tff(c_2502, plain, (![C_8208]: (C_8208='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2233, c_2231])).
% 4.28/1.72  tff(c_2778, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_2502, c_54])).
% 4.28/1.72  tff(c_2779, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_223])).
% 4.28/1.72  tff(c_46, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.28/1.72  tff(c_111, plain, (![A_52, B_53]: (k1_enumset1(A_52, A_52, B_53)=k2_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.28/1.72  tff(c_129, plain, (![A_54, B_55]: (r2_hidden(A_54, k2_tarski(A_54, B_55)))), inference(superposition, [status(thm), theory('equality')], [c_111, c_28])).
% 4.28/1.72  tff(c_132, plain, (![A_23]: (r2_hidden(A_23, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_129])).
% 4.28/1.72  tff(c_2788, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2779, c_132])).
% 4.28/1.72  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.28/1.72  tff(c_2795, plain, (![A_10249, B_10250, C_10251]: (~r1_xboole_0(A_10249, B_10250) | ~r2_hidden(C_10251, B_10250) | ~r2_hidden(C_10251, A_10249))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.28/1.72  tff(c_3026, plain, (![C_10263, B_10264, A_10265]: (~r2_hidden(C_10263, B_10264) | ~r2_hidden(C_10263, A_10265) | k3_xboole_0(A_10265, B_10264)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_2795])).
% 4.28/1.72  tff(c_3063, plain, (![A_10266]: (~r2_hidden('#skF_4', A_10266) | k3_xboole_0(A_10266, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2788, c_3026])).
% 4.28/1.72  tff(c_3075, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_2788, c_3063])).
% 4.28/1.72  tff(c_3106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3075])).
% 4.28/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.28/1.72  
% 4.28/1.72  Inference rules
% 4.28/1.72  ----------------------
% 4.28/1.72  #Ref     : 0
% 4.28/1.72  #Sup     : 912
% 4.28/1.72  #Fact    : 6
% 4.28/1.72  #Define  : 0
% 4.28/1.72  #Split   : 3
% 4.28/1.72  #Chain   : 0
% 4.28/1.72  #Close   : 0
% 4.28/1.72  
% 4.28/1.72  Ordering : KBO
% 4.28/1.72  
% 4.28/1.72  Simplification rules
% 4.28/1.72  ----------------------
% 4.28/1.72  #Subsume      : 163
% 4.28/1.72  #Demod        : 152
% 4.28/1.72  #Tautology    : 156
% 4.28/1.72  #SimpNegUnit  : 5
% 4.28/1.72  #BackRed      : 1
% 4.28/1.72  
% 4.28/1.72  #Partial instantiations: 1186
% 4.28/1.72  #Strategies tried      : 1
% 4.28/1.72  
% 4.28/1.72  Timing (in seconds)
% 4.28/1.72  ----------------------
% 4.28/1.72  Preprocessing        : 0.29
% 4.28/1.72  Parsing              : 0.15
% 4.28/1.72  CNF conversion       : 0.02
% 4.28/1.72  Main loop            : 0.71
% 4.28/1.72  Inferencing          : 0.32
% 4.28/1.72  Reduction            : 0.20
% 4.28/1.72  Demodulation         : 0.14
% 4.28/1.72  BG Simplification    : 0.03
% 4.28/1.72  Subsumption          : 0.11
% 4.28/1.72  Abstraction          : 0.04
% 4.28/1.72  MUC search           : 0.00
% 4.28/1.72  Cooper               : 0.00
% 4.28/1.72  Total                : 1.02
% 4.28/1.72  Index Insertion      : 0.00
% 4.28/1.72  Index Deletion       : 0.00
% 4.28/1.72  Index Matching       : 0.00
% 4.28/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
