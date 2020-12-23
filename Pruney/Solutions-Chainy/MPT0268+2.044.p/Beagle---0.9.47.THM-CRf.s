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
% DateTime   : Thu Dec  3 09:52:39 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   72 (  94 expanded)
%              Number of leaves         :   30 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :   83 ( 129 expanded)
%              Number of equality atoms :   24 (  44 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r2_hidden(C,A)
        | r1_tarski(A,k4_xboole_0(B,k1_tarski(C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l2_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_72,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_74,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_55,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_43,axiom,(
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

tff(c_56,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_77,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_163,plain,(
    ! [A_79,B_80,C_81] :
      ( r1_tarski(A_79,k4_xboole_0(B_80,k1_tarski(C_81)))
      | r2_hidden(C_81,A_79)
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_118,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_tarski(B_60,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_123,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,k4_xboole_0(A_10,B_11)) ) ),
    inference(resolution,[status(thm)],[c_16,c_118])).

tff(c_167,plain,(
    ! [B_80,C_81] :
      ( k4_xboole_0(B_80,k1_tarski(C_81)) = B_80
      | r2_hidden(C_81,B_80)
      | ~ r1_tarski(B_80,B_80) ) ),
    inference(resolution,[status(thm)],[c_163,c_123])).

tff(c_174,plain,(
    ! [B_82,C_83] :
      ( k4_xboole_0(B_82,k1_tarski(C_83)) = B_82
      | r2_hidden(C_83,B_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_167])).

tff(c_54,plain,
    ( k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4'
    | r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_116,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_189,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_116])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_189])).

tff(c_206,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_44,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_78,plain,(
    ! [A_49,B_50] : k1_enumset1(A_49,A_49,B_50) = k2_tarski(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    ! [E_20,A_14,B_15] : r2_hidden(E_20,k1_enumset1(A_14,B_15,E_20)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_96,plain,(
    ! [B_51,A_52] : r2_hidden(B_51,k2_tarski(A_52,B_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_22])).

tff(c_99,plain,(
    ! [A_21] : r2_hidden(A_21,k1_tarski(A_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_96])).

tff(c_207,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_58,plain,
    ( k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4'
    | k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_208,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_208])).

tff(c_222,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_18,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_242,plain,(
    r1_xboole_0('#skF_6',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_18])).

tff(c_268,plain,(
    ! [A_93,B_94,C_95] :
      ( ~ r1_xboole_0(A_93,B_94)
      | ~ r2_hidden(C_95,B_94)
      | ~ r2_hidden(C_95,A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_287,plain,(
    ! [C_100] :
      ( ~ r2_hidden(C_100,k1_tarski('#skF_7'))
      | ~ r2_hidden(C_100,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_242,c_268])).

tff(c_299,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_99,c_287])).

tff(c_305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_299])).

tff(c_306,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_321,plain,(
    ! [A_101,B_102] : k1_enumset1(A_101,A_101,B_102) = k2_tarski(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_339,plain,(
    ! [B_103,A_104] : r2_hidden(B_103,k2_tarski(A_104,B_103)) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_22])).

tff(c_342,plain,(
    ! [A_21] : r2_hidden(A_21,k1_tarski(A_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_339])).

tff(c_307,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_309,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_60])).

tff(c_316,plain,(
    r1_xboole_0('#skF_6',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_18])).

tff(c_372,plain,(
    ! [A_116,B_117,C_118] :
      ( ~ r1_xboole_0(A_116,B_117)
      | ~ r2_hidden(C_118,B_117)
      | ~ r2_hidden(C_118,A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_379,plain,(
    ! [C_119] :
      ( ~ r2_hidden(C_119,k1_tarski('#skF_7'))
      | ~ r2_hidden(C_119,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_316,c_372])).

tff(c_391,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_342,c_379])).

tff(c_397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_391])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.28  
% 2.26/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.26/1.28  
% 2.26/1.28  %Foreground sorts:
% 2.26/1.28  
% 2.26/1.28  
% 2.26/1.28  %Background operators:
% 2.26/1.28  
% 2.26/1.28  
% 2.26/1.28  %Foreground operators:
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.26/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.26/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.26/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.26/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.26/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.26/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.26/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.26/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.26/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.26/1.28  
% 2.26/1.30  tff(f_90, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.26/1.30  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.26/1.30  tff(f_84, axiom, (![A, B, C]: (r1_tarski(A, B) => (r2_hidden(C, A) | r1_tarski(A, k4_xboole_0(B, k1_tarski(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l2_zfmisc_1)).
% 2.26/1.30  tff(f_53, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.26/1.30  tff(f_72, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.26/1.30  tff(f_74, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.26/1.30  tff(f_70, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.26/1.30  tff(f_55, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.26/1.30  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.26/1.30  tff(c_56, plain, (~r2_hidden('#skF_5', '#skF_4') | r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.26/1.30  tff(c_77, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_56])).
% 2.26/1.30  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.26/1.30  tff(c_163, plain, (![A_79, B_80, C_81]: (r1_tarski(A_79, k4_xboole_0(B_80, k1_tarski(C_81))) | r2_hidden(C_81, A_79) | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.26/1.30  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.26/1.30  tff(c_118, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_tarski(B_60, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.26/1.30  tff(c_123, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, k4_xboole_0(A_10, B_11)))), inference(resolution, [status(thm)], [c_16, c_118])).
% 2.26/1.30  tff(c_167, plain, (![B_80, C_81]: (k4_xboole_0(B_80, k1_tarski(C_81))=B_80 | r2_hidden(C_81, B_80) | ~r1_tarski(B_80, B_80))), inference(resolution, [status(thm)], [c_163, c_123])).
% 2.26/1.30  tff(c_174, plain, (![B_82, C_83]: (k4_xboole_0(B_82, k1_tarski(C_83))=B_82 | r2_hidden(C_83, B_82))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_167])).
% 2.26/1.30  tff(c_54, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4' | r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.26/1.30  tff(c_116, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_54])).
% 2.26/1.30  tff(c_189, plain, (r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_174, c_116])).
% 2.26/1.30  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_189])).
% 2.26/1.30  tff(c_206, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_54])).
% 2.26/1.30  tff(c_44, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.26/1.30  tff(c_78, plain, (![A_49, B_50]: (k1_enumset1(A_49, A_49, B_50)=k2_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.26/1.30  tff(c_22, plain, (![E_20, A_14, B_15]: (r2_hidden(E_20, k1_enumset1(A_14, B_15, E_20)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.26/1.30  tff(c_96, plain, (![B_51, A_52]: (r2_hidden(B_51, k2_tarski(A_52, B_51)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_22])).
% 2.26/1.30  tff(c_99, plain, (![A_21]: (r2_hidden(A_21, k1_tarski(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_96])).
% 2.26/1.30  tff(c_207, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(splitRight, [status(thm)], [c_54])).
% 2.26/1.30  tff(c_58, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4' | k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.26/1.30  tff(c_208, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_58])).
% 2.26/1.30  tff(c_221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_207, c_208])).
% 2.26/1.30  tff(c_222, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(splitRight, [status(thm)], [c_58])).
% 2.26/1.30  tff(c_18, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.26/1.30  tff(c_242, plain, (r1_xboole_0('#skF_6', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_222, c_18])).
% 2.26/1.30  tff(c_268, plain, (![A_93, B_94, C_95]: (~r1_xboole_0(A_93, B_94) | ~r2_hidden(C_95, B_94) | ~r2_hidden(C_95, A_93))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.26/1.30  tff(c_287, plain, (![C_100]: (~r2_hidden(C_100, k1_tarski('#skF_7')) | ~r2_hidden(C_100, '#skF_6'))), inference(resolution, [status(thm)], [c_242, c_268])).
% 2.26/1.30  tff(c_299, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_99, c_287])).
% 2.26/1.30  tff(c_305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_206, c_299])).
% 2.26/1.30  tff(c_306, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_56])).
% 2.26/1.30  tff(c_321, plain, (![A_101, B_102]: (k1_enumset1(A_101, A_101, B_102)=k2_tarski(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.26/1.30  tff(c_339, plain, (![B_103, A_104]: (r2_hidden(B_103, k2_tarski(A_104, B_103)))), inference(superposition, [status(thm), theory('equality')], [c_321, c_22])).
% 2.26/1.30  tff(c_342, plain, (![A_21]: (r2_hidden(A_21, k1_tarski(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_339])).
% 2.26/1.30  tff(c_307, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 2.26/1.30  tff(c_60, plain, (~r2_hidden('#skF_5', '#skF_4') | k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.26/1.30  tff(c_309, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_307, c_60])).
% 2.26/1.30  tff(c_316, plain, (r1_xboole_0('#skF_6', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_309, c_18])).
% 2.26/1.30  tff(c_372, plain, (![A_116, B_117, C_118]: (~r1_xboole_0(A_116, B_117) | ~r2_hidden(C_118, B_117) | ~r2_hidden(C_118, A_116))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.26/1.30  tff(c_379, plain, (![C_119]: (~r2_hidden(C_119, k1_tarski('#skF_7')) | ~r2_hidden(C_119, '#skF_6'))), inference(resolution, [status(thm)], [c_316, c_372])).
% 2.26/1.30  tff(c_391, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_342, c_379])).
% 2.26/1.30  tff(c_397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_306, c_391])).
% 2.26/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.30  
% 2.26/1.30  Inference rules
% 2.26/1.30  ----------------------
% 2.26/1.30  #Ref     : 0
% 2.26/1.30  #Sup     : 74
% 2.26/1.30  #Fact    : 0
% 2.26/1.30  #Define  : 0
% 2.26/1.30  #Split   : 3
% 2.26/1.30  #Chain   : 0
% 2.26/1.30  #Close   : 0
% 2.26/1.30  
% 2.26/1.30  Ordering : KBO
% 2.26/1.30  
% 2.26/1.30  Simplification rules
% 2.26/1.30  ----------------------
% 2.26/1.30  #Subsume      : 3
% 2.26/1.30  #Demod        : 20
% 2.26/1.30  #Tautology    : 42
% 2.26/1.30  #SimpNegUnit  : 1
% 2.26/1.30  #BackRed      : 0
% 2.26/1.30  
% 2.26/1.30  #Partial instantiations: 0
% 2.26/1.30  #Strategies tried      : 1
% 2.26/1.30  
% 2.26/1.30  Timing (in seconds)
% 2.26/1.30  ----------------------
% 2.26/1.30  Preprocessing        : 0.33
% 2.26/1.30  Parsing              : 0.17
% 2.26/1.30  CNF conversion       : 0.02
% 2.26/1.30  Main loop            : 0.22
% 2.26/1.30  Inferencing          : 0.08
% 2.26/1.30  Reduction            : 0.07
% 2.26/1.30  Demodulation         : 0.05
% 2.26/1.30  BG Simplification    : 0.02
% 2.26/1.30  Subsumption          : 0.04
% 2.26/1.30  Abstraction          : 0.02
% 2.26/1.30  MUC search           : 0.00
% 2.26/1.30  Cooper               : 0.00
% 2.26/1.30  Total                : 0.58
% 2.26/1.30  Index Insertion      : 0.00
% 2.26/1.30  Index Deletion       : 0.00
% 2.26/1.30  Index Matching       : 0.00
% 2.26/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
