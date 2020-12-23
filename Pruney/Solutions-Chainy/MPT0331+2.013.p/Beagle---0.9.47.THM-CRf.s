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
% DateTime   : Thu Dec  3 09:54:46 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   48 (  55 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  68 expanded)
%              Number of equality atoms :   20 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_55,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_28,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_97,plain,(
    ! [A_35,B_36,C_37] :
      ( ~ r1_xboole_0(A_35,B_36)
      | ~ r2_hidden(C_37,k3_xboole_0(A_35,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_109,plain,(
    ! [A_38,B_39] :
      ( ~ r1_xboole_0(A_38,B_39)
      | k3_xboole_0(A_38,B_39) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_97])).

tff(c_114,plain,(
    ! [A_40] : k3_xboole_0(A_40,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_109])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_122,plain,(
    ! [A_40] : k5_xboole_0(A_40,k1_xboole_0) = k4_xboole_0(A_40,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_10])).

tff(c_142,plain,(
    ! [A_40] : k5_xboole_0(A_40,k1_xboole_0) = A_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_122])).

tff(c_346,plain,(
    ! [A_64,C_65,B_66] :
      ( r1_xboole_0(k2_tarski(A_64,C_65),B_66)
      | r2_hidden(C_65,B_66)
      | r2_hidden(A_64,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_108,plain,(
    ! [A_35,B_36] :
      ( ~ r1_xboole_0(A_35,B_36)
      | k3_xboole_0(A_35,B_36) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_97])).

tff(c_395,plain,(
    ! [A_72,C_73,B_74] :
      ( k3_xboole_0(k2_tarski(A_72,C_73),B_74) = k1_xboole_0
      | r2_hidden(C_73,B_74)
      | r2_hidden(A_72,B_74) ) ),
    inference(resolution,[status(thm)],[c_346,c_108])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_82,plain,(
    ! [A_33,B_34] : k5_xboole_0(A_33,k3_xboole_0(A_33,B_34)) = k4_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_94,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_82])).

tff(c_404,plain,(
    ! [B_74,A_72,C_73] :
      ( k4_xboole_0(B_74,k2_tarski(A_72,C_73)) = k5_xboole_0(B_74,k1_xboole_0)
      | r2_hidden(C_73,B_74)
      | r2_hidden(A_72,B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_94])).

tff(c_519,plain,(
    ! [B_78,A_79,C_80] :
      ( k4_xboole_0(B_78,k2_tarski(A_79,C_80)) = B_78
      | r2_hidden(C_80,B_78)
      | r2_hidden(A_79,B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_404])).

tff(c_24,plain,(
    k4_xboole_0('#skF_5',k2_tarski('#skF_3','#skF_4')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_529,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_24])).

tff(c_543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_529])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.39  
% 2.31/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.39  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.31/1.39  
% 2.31/1.39  %Foreground sorts:
% 2.31/1.39  
% 2.31/1.39  
% 2.31/1.39  %Background operators:
% 2.31/1.39  
% 2.31/1.39  
% 2.31/1.39  %Foreground operators:
% 2.31/1.39  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.31/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.31/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.31/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.31/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.31/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.31/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.31/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.31/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.31/1.39  
% 2.31/1.41  tff(f_82, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 2.31/1.41  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.31/1.41  tff(f_55, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.31/1.41  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.31/1.41  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.31/1.41  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.31/1.41  tff(f_71, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 2.31/1.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.31/1.41  tff(c_28, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.31/1.41  tff(c_26, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.31/1.41  tff(c_12, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.31/1.41  tff(c_14, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.31/1.41  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.31/1.41  tff(c_97, plain, (![A_35, B_36, C_37]: (~r1_xboole_0(A_35, B_36) | ~r2_hidden(C_37, k3_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.31/1.41  tff(c_109, plain, (![A_38, B_39]: (~r1_xboole_0(A_38, B_39) | k3_xboole_0(A_38, B_39)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_97])).
% 2.31/1.41  tff(c_114, plain, (![A_40]: (k3_xboole_0(A_40, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_109])).
% 2.31/1.41  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.31/1.41  tff(c_122, plain, (![A_40]: (k5_xboole_0(A_40, k1_xboole_0)=k4_xboole_0(A_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_114, c_10])).
% 2.31/1.41  tff(c_142, plain, (![A_40]: (k5_xboole_0(A_40, k1_xboole_0)=A_40)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_122])).
% 2.31/1.41  tff(c_346, plain, (![A_64, C_65, B_66]: (r1_xboole_0(k2_tarski(A_64, C_65), B_66) | r2_hidden(C_65, B_66) | r2_hidden(A_64, B_66))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.31/1.41  tff(c_108, plain, (![A_35, B_36]: (~r1_xboole_0(A_35, B_36) | k3_xboole_0(A_35, B_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_97])).
% 2.31/1.41  tff(c_395, plain, (![A_72, C_73, B_74]: (k3_xboole_0(k2_tarski(A_72, C_73), B_74)=k1_xboole_0 | r2_hidden(C_73, B_74) | r2_hidden(A_72, B_74))), inference(resolution, [status(thm)], [c_346, c_108])).
% 2.31/1.41  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.31/1.41  tff(c_82, plain, (![A_33, B_34]: (k5_xboole_0(A_33, k3_xboole_0(A_33, B_34))=k4_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.31/1.41  tff(c_94, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_82])).
% 2.31/1.41  tff(c_404, plain, (![B_74, A_72, C_73]: (k4_xboole_0(B_74, k2_tarski(A_72, C_73))=k5_xboole_0(B_74, k1_xboole_0) | r2_hidden(C_73, B_74) | r2_hidden(A_72, B_74))), inference(superposition, [status(thm), theory('equality')], [c_395, c_94])).
% 2.31/1.41  tff(c_519, plain, (![B_78, A_79, C_80]: (k4_xboole_0(B_78, k2_tarski(A_79, C_80))=B_78 | r2_hidden(C_80, B_78) | r2_hidden(A_79, B_78))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_404])).
% 2.31/1.41  tff(c_24, plain, (k4_xboole_0('#skF_5', k2_tarski('#skF_3', '#skF_4'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.31/1.41  tff(c_529, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_519, c_24])).
% 2.31/1.41  tff(c_543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_529])).
% 2.31/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.41  
% 2.31/1.41  Inference rules
% 2.31/1.41  ----------------------
% 2.31/1.41  #Ref     : 0
% 2.31/1.41  #Sup     : 120
% 2.31/1.41  #Fact    : 0
% 2.31/1.41  #Define  : 0
% 2.31/1.41  #Split   : 0
% 2.31/1.41  #Chain   : 0
% 2.31/1.41  #Close   : 0
% 2.31/1.41  
% 2.31/1.41  Ordering : KBO
% 2.31/1.41  
% 2.31/1.41  Simplification rules
% 2.31/1.41  ----------------------
% 2.31/1.41  #Subsume      : 26
% 2.31/1.41  #Demod        : 31
% 2.31/1.41  #Tautology    : 69
% 2.31/1.41  #SimpNegUnit  : 14
% 2.31/1.41  #BackRed      : 0
% 2.31/1.41  
% 2.31/1.41  #Partial instantiations: 0
% 2.31/1.41  #Strategies tried      : 1
% 2.31/1.41  
% 2.31/1.41  Timing (in seconds)
% 2.31/1.41  ----------------------
% 2.31/1.41  Preprocessing        : 0.33
% 2.31/1.41  Parsing              : 0.17
% 2.31/1.41  CNF conversion       : 0.02
% 2.31/1.41  Main loop            : 0.24
% 2.31/1.41  Inferencing          : 0.10
% 2.31/1.41  Reduction            : 0.08
% 2.31/1.41  Demodulation         : 0.06
% 2.31/1.41  BG Simplification    : 0.01
% 2.31/1.41  Subsumption          : 0.04
% 2.31/1.41  Abstraction          : 0.02
% 2.31/1.41  MUC search           : 0.00
% 2.31/1.41  Cooper               : 0.00
% 2.31/1.41  Total                : 0.60
% 2.31/1.41  Index Insertion      : 0.00
% 2.31/1.41  Index Deletion       : 0.00
% 2.31/1.41  Index Matching       : 0.00
% 2.31/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
