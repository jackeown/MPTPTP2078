%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:14 EST 2020

% Result     : Theorem 7.01s
% Output     : CNFRefutation 7.01s
% Verified   : 
% Statistics : Number of formulae       :   55 (  72 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 (  87 expanded)
%              Number of equality atoms :   24 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_8 > #skF_9 > #skF_5 > #skF_7 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_59,axiom,(
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

tff(f_107,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_77,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_81,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_96,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_9'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_280,plain,(
    ! [A_83,B_84] :
      ( k4_xboole_0(k1_tarski(A_83),B_84) = k1_xboole_0
      | ~ r2_hidden(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_256,plain,(
    ! [A_77,B_78] :
      ( r1_xboole_0(A_77,B_78)
      | k4_xboole_0(A_77,B_78) != A_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_264,plain,(
    k4_xboole_0(k1_tarski('#skF_9'),'#skF_10') != k1_tarski('#skF_9') ),
    inference(resolution,[status(thm)],[c_256,c_96])).

tff(c_286,plain,
    ( k1_tarski('#skF_9') != k1_xboole_0
    | ~ r2_hidden('#skF_9','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_264])).

tff(c_306,plain,(
    ~ r2_hidden('#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_286])).

tff(c_274,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_3'(A_81,B_82),A_81)
      | r1_xboole_0(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_72,plain,(
    ! [C_40,A_36] :
      ( C_40 = A_36
      | ~ r2_hidden(C_40,k1_tarski(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4108,plain,(
    ! [A_292,B_293] :
      ( '#skF_3'(k1_tarski(A_292),B_293) = A_292
      | r1_xboole_0(k1_tarski(A_292),B_293) ) ),
    inference(resolution,[status(thm)],[c_274,c_72])).

tff(c_4142,plain,(
    '#skF_3'(k1_tarski('#skF_9'),'#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_4108,c_96])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),B_12)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4146,plain,
    ( r2_hidden('#skF_9','#skF_10')
    | r1_xboole_0(k1_tarski('#skF_9'),'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_4142,c_28])).

tff(c_4153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_306,c_4146])).

tff(c_4155,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_286])).

tff(c_38,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_92,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(k1_tarski(A_47),B_48) = k1_xboole_0
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4345,plain,(
    ! [A_316,B_317] : k4_xboole_0(A_316,k4_xboole_0(A_316,B_317)) = k3_xboole_0(A_316,B_317) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4388,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(k1_tarski(A_47),k1_xboole_0) = k3_xboole_0(k1_tarski(A_47),B_48)
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_4345])).

tff(c_9136,plain,(
    ! [A_512,B_513] :
      ( k3_xboole_0(k1_tarski(A_512),B_513) = k1_tarski(A_512)
      | ~ r2_hidden(A_512,B_513) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4388])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_9767,plain,(
    ! [B_524,A_525] :
      ( k3_xboole_0(B_524,k1_tarski(A_525)) = k1_tarski(A_525)
      | ~ r2_hidden(A_525,B_524) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9136,c_2])).

tff(c_94,plain,(
    k3_xboole_0(k1_tarski('#skF_9'),'#skF_10') != k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_97,plain,(
    k3_xboole_0('#skF_10',k1_tarski('#skF_9')) != k1_tarski('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_94])).

tff(c_9906,plain,(
    ~ r2_hidden('#skF_9','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_9767,c_97])).

tff(c_9986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4155,c_9906])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.01/2.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.01/2.40  
% 7.01/2.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.01/2.40  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_8 > #skF_9 > #skF_5 > #skF_7 > #skF_4
% 7.01/2.40  
% 7.01/2.40  %Foreground sorts:
% 7.01/2.40  
% 7.01/2.40  
% 7.01/2.40  %Background operators:
% 7.01/2.40  
% 7.01/2.40  
% 7.01/2.40  %Foreground operators:
% 7.01/2.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.01/2.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.01/2.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.01/2.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.01/2.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.01/2.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.01/2.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.01/2.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.01/2.40  tff('#skF_10', type, '#skF_10': $i).
% 7.01/2.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.01/2.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.01/2.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.01/2.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.01/2.40  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 7.01/2.40  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 7.01/2.40  tff('#skF_9', type, '#skF_9': $i).
% 7.01/2.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.01/2.40  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 7.01/2.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.01/2.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.01/2.40  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 7.01/2.40  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.01/2.40  
% 7.01/2.41  tff(f_122, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 7.01/2.41  tff(f_117, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 7.01/2.41  tff(f_85, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.01/2.41  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.01/2.41  tff(f_107, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 7.01/2.41  tff(f_77, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.01/2.41  tff(f_81, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.01/2.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.01/2.41  tff(c_96, plain, (~r1_xboole_0(k1_tarski('#skF_9'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.01/2.41  tff(c_280, plain, (![A_83, B_84]: (k4_xboole_0(k1_tarski(A_83), B_84)=k1_xboole_0 | ~r2_hidden(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.01/2.41  tff(c_256, plain, (![A_77, B_78]: (r1_xboole_0(A_77, B_78) | k4_xboole_0(A_77, B_78)!=A_77)), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.01/2.41  tff(c_264, plain, (k4_xboole_0(k1_tarski('#skF_9'), '#skF_10')!=k1_tarski('#skF_9')), inference(resolution, [status(thm)], [c_256, c_96])).
% 7.01/2.41  tff(c_286, plain, (k1_tarski('#skF_9')!=k1_xboole_0 | ~r2_hidden('#skF_9', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_280, c_264])).
% 7.01/2.41  tff(c_306, plain, (~r2_hidden('#skF_9', '#skF_10')), inference(splitLeft, [status(thm)], [c_286])).
% 7.01/2.41  tff(c_274, plain, (![A_81, B_82]: (r2_hidden('#skF_3'(A_81, B_82), A_81) | r1_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.01/2.41  tff(c_72, plain, (![C_40, A_36]: (C_40=A_36 | ~r2_hidden(C_40, k1_tarski(A_36)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.01/2.41  tff(c_4108, plain, (![A_292, B_293]: ('#skF_3'(k1_tarski(A_292), B_293)=A_292 | r1_xboole_0(k1_tarski(A_292), B_293))), inference(resolution, [status(thm)], [c_274, c_72])).
% 7.01/2.41  tff(c_4142, plain, ('#skF_3'(k1_tarski('#skF_9'), '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_4108, c_96])).
% 7.01/2.41  tff(c_28, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), B_12) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.01/2.41  tff(c_4146, plain, (r2_hidden('#skF_9', '#skF_10') | r1_xboole_0(k1_tarski('#skF_9'), '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_4142, c_28])).
% 7.01/2.41  tff(c_4153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_306, c_4146])).
% 7.01/2.41  tff(c_4155, plain, (r2_hidden('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_286])).
% 7.01/2.41  tff(c_38, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.01/2.41  tff(c_92, plain, (![A_47, B_48]: (k4_xboole_0(k1_tarski(A_47), B_48)=k1_xboole_0 | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.01/2.41  tff(c_4345, plain, (![A_316, B_317]: (k4_xboole_0(A_316, k4_xboole_0(A_316, B_317))=k3_xboole_0(A_316, B_317))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.01/2.41  tff(c_4388, plain, (![A_47, B_48]: (k4_xboole_0(k1_tarski(A_47), k1_xboole_0)=k3_xboole_0(k1_tarski(A_47), B_48) | ~r2_hidden(A_47, B_48))), inference(superposition, [status(thm), theory('equality')], [c_92, c_4345])).
% 7.01/2.41  tff(c_9136, plain, (![A_512, B_513]: (k3_xboole_0(k1_tarski(A_512), B_513)=k1_tarski(A_512) | ~r2_hidden(A_512, B_513))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4388])).
% 7.01/2.41  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.01/2.41  tff(c_9767, plain, (![B_524, A_525]: (k3_xboole_0(B_524, k1_tarski(A_525))=k1_tarski(A_525) | ~r2_hidden(A_525, B_524))), inference(superposition, [status(thm), theory('equality')], [c_9136, c_2])).
% 7.01/2.41  tff(c_94, plain, (k3_xboole_0(k1_tarski('#skF_9'), '#skF_10')!=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.01/2.41  tff(c_97, plain, (k3_xboole_0('#skF_10', k1_tarski('#skF_9'))!=k1_tarski('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_94])).
% 7.01/2.41  tff(c_9906, plain, (~r2_hidden('#skF_9', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_9767, c_97])).
% 7.01/2.41  tff(c_9986, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4155, c_9906])).
% 7.01/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.01/2.41  
% 7.01/2.41  Inference rules
% 7.01/2.41  ----------------------
% 7.01/2.41  #Ref     : 2
% 7.01/2.41  #Sup     : 2464
% 7.01/2.41  #Fact    : 0
% 7.01/2.41  #Define  : 0
% 7.01/2.41  #Split   : 3
% 7.01/2.41  #Chain   : 0
% 7.01/2.41  #Close   : 0
% 7.01/2.41  
% 7.01/2.41  Ordering : KBO
% 7.01/2.41  
% 7.01/2.41  Simplification rules
% 7.01/2.41  ----------------------
% 7.01/2.41  #Subsume      : 863
% 7.01/2.41  #Demod        : 1035
% 7.01/2.41  #Tautology    : 925
% 7.01/2.41  #SimpNegUnit  : 75
% 7.01/2.41  #BackRed      : 0
% 7.01/2.41  
% 7.01/2.41  #Partial instantiations: 0
% 7.01/2.41  #Strategies tried      : 1
% 7.01/2.41  
% 7.01/2.41  Timing (in seconds)
% 7.01/2.41  ----------------------
% 7.01/2.42  Preprocessing        : 0.35
% 7.01/2.42  Parsing              : 0.17
% 7.01/2.42  CNF conversion       : 0.03
% 7.01/2.42  Main loop            : 1.31
% 7.01/2.42  Inferencing          : 0.42
% 7.01/2.42  Reduction            : 0.49
% 7.01/2.42  Demodulation         : 0.37
% 7.01/2.42  BG Simplification    : 0.05
% 7.01/2.42  Subsumption          : 0.26
% 7.01/2.42  Abstraction          : 0.07
% 7.01/2.42  MUC search           : 0.00
% 7.01/2.42  Cooper               : 0.00
% 7.01/2.42  Total                : 1.69
% 7.01/2.42  Index Insertion      : 0.00
% 7.01/2.42  Index Deletion       : 0.00
% 7.01/2.42  Index Matching       : 0.00
% 7.01/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
