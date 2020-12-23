%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:31 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   67 (  88 expanded)
%              Number of leaves         :   35 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   70 ( 121 expanded)
%              Number of equality atoms :   31 (  51 expanded)
%              Maximal formula depth    :   12 (   4 average)
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

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_81,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_43,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_82,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_58,plain,(
    ! [C_26] : r2_hidden(C_26,k1_tarski(C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_112,plain,(
    ! [A_70,B_71] : k1_enumset1(A_70,A_70,B_71) = k2_tarski(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ! [E_21,A_15,B_16] : r2_hidden(E_21,k1_enumset1(A_15,B_16,E_21)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_124,plain,(
    ! [B_71,A_70] : r2_hidden(B_71,k2_tarski(A_70,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_34])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_150,plain,(
    ! [D_78,A_79,B_80] :
      ( r2_hidden(D_78,A_79)
      | ~ r2_hidden(D_78,k4_xboole_0(A_79,B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_243,plain,(
    ! [A_100,B_101] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_100,B_101)),A_100)
      | k4_xboole_0(A_100,B_101) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_150])).

tff(c_183,plain,(
    ! [D_83,B_84,A_85] :
      ( ~ r2_hidden(D_83,B_84)
      | ~ r2_hidden(D_83,k4_xboole_0(A_85,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_188,plain,(
    ! [A_85,B_84] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_85,B_84)),B_84)
      | k4_xboole_0(A_85,B_84) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_183])).

tff(c_285,plain,(
    ! [A_102] : k4_xboole_0(A_102,A_102) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_243,c_188])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_341,plain,(
    ! [D_106,A_107] :
      ( ~ r2_hidden(D_106,A_107)
      | ~ r2_hidden(D_106,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_4])).

tff(c_359,plain,(
    ! [B_71] : ~ r2_hidden(B_71,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_124,c_341])).

tff(c_260,plain,(
    ! [A_100] : k4_xboole_0(A_100,A_100) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_243,c_188])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_141,plain,(
    ! [A_76,B_77] :
      ( k3_xboole_0(A_76,B_77) = A_76
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_149,plain,(
    ! [B_10] : k3_xboole_0(B_10,B_10) = B_10 ),
    inference(resolution,[status(thm)],[c_26,c_141])).

tff(c_189,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k3_xboole_0(A_86,B_87)) = k4_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_201,plain,(
    ! [B_10] : k5_xboole_0(B_10,B_10) = k4_xboole_0(B_10,B_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_189])).

tff(c_84,plain,(
    r1_tarski(k1_tarski('#skF_8'),k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_148,plain,(
    k3_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_9')) = k1_tarski('#skF_8') ),
    inference(resolution,[status(thm)],[c_84,c_141])).

tff(c_198,plain,(
    k5_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_189])).

tff(c_264,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_9')) = k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_198])).

tff(c_283,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_9')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_264])).

tff(c_983,plain,(
    ! [D_2382,A_2383,B_2384] :
      ( r2_hidden(D_2382,k4_xboole_0(A_2383,B_2384))
      | r2_hidden(D_2382,B_2384)
      | ~ r2_hidden(D_2382,A_2383) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1000,plain,(
    ! [D_2382] :
      ( r2_hidden(D_2382,k1_xboole_0)
      | r2_hidden(D_2382,k1_tarski('#skF_9'))
      | ~ r2_hidden(D_2382,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_983])).

tff(c_1011,plain,(
    ! [D_2507] :
      ( r2_hidden(D_2507,k1_tarski('#skF_9'))
      | ~ r2_hidden(D_2507,k1_tarski('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_359,c_1000])).

tff(c_56,plain,(
    ! [C_26,A_22] :
      ( C_26 = A_22
      | ~ r2_hidden(C_26,k1_tarski(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1064,plain,(
    ! [D_2569] :
      ( D_2569 = '#skF_9'
      | ~ r2_hidden(D_2569,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_1011,c_56])).

tff(c_1080,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_58,c_1064])).

tff(c_1086,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1080])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.51  
% 3.01/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.51  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_7
% 3.01/1.51  
% 3.01/1.51  %Foreground sorts:
% 3.01/1.51  
% 3.01/1.51  
% 3.01/1.51  %Background operators:
% 3.01/1.51  
% 3.01/1.51  
% 3.01/1.51  %Foreground operators:
% 3.01/1.51  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.01/1.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.01/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.01/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.01/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.01/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.01/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.01/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.01/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.01/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.01/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.01/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.01/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.01/1.51  tff('#skF_9', type, '#skF_9': $i).
% 3.01/1.51  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.01/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.01/1.51  tff('#skF_8', type, '#skF_8': $i).
% 3.01/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.51  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.01/1.51  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.01/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.01/1.51  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.01/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.01/1.51  
% 3.21/1.52  tff(f_96, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 3.21/1.52  tff(f_77, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.21/1.52  tff(f_81, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.21/1.52  tff(f_70, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.21/1.52  tff(f_43, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.21/1.52  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.21/1.52  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.21/1.52  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.21/1.52  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.21/1.52  tff(c_82, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.21/1.52  tff(c_58, plain, (![C_26]: (r2_hidden(C_26, k1_tarski(C_26)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.21/1.52  tff(c_112, plain, (![A_70, B_71]: (k1_enumset1(A_70, A_70, B_71)=k2_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.21/1.52  tff(c_34, plain, (![E_21, A_15, B_16]: (r2_hidden(E_21, k1_enumset1(A_15, B_16, E_21)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.21/1.52  tff(c_124, plain, (![B_71, A_70]: (r2_hidden(B_71, k2_tarski(A_70, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_34])).
% 3.21/1.52  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.21/1.52  tff(c_150, plain, (![D_78, A_79, B_80]: (r2_hidden(D_78, A_79) | ~r2_hidden(D_78, k4_xboole_0(A_79, B_80)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.52  tff(c_243, plain, (![A_100, B_101]: (r2_hidden('#skF_3'(k4_xboole_0(A_100, B_101)), A_100) | k4_xboole_0(A_100, B_101)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_150])).
% 3.21/1.52  tff(c_183, plain, (![D_83, B_84, A_85]: (~r2_hidden(D_83, B_84) | ~r2_hidden(D_83, k4_xboole_0(A_85, B_84)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.52  tff(c_188, plain, (![A_85, B_84]: (~r2_hidden('#skF_3'(k4_xboole_0(A_85, B_84)), B_84) | k4_xboole_0(A_85, B_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_183])).
% 3.21/1.52  tff(c_285, plain, (![A_102]: (k4_xboole_0(A_102, A_102)=k1_xboole_0)), inference(resolution, [status(thm)], [c_243, c_188])).
% 3.21/1.52  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.52  tff(c_341, plain, (![D_106, A_107]: (~r2_hidden(D_106, A_107) | ~r2_hidden(D_106, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_285, c_4])).
% 3.21/1.52  tff(c_359, plain, (![B_71]: (~r2_hidden(B_71, k1_xboole_0))), inference(resolution, [status(thm)], [c_124, c_341])).
% 3.21/1.52  tff(c_260, plain, (![A_100]: (k4_xboole_0(A_100, A_100)=k1_xboole_0)), inference(resolution, [status(thm)], [c_243, c_188])).
% 3.21/1.52  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.21/1.52  tff(c_141, plain, (![A_76, B_77]: (k3_xboole_0(A_76, B_77)=A_76 | ~r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.21/1.52  tff(c_149, plain, (![B_10]: (k3_xboole_0(B_10, B_10)=B_10)), inference(resolution, [status(thm)], [c_26, c_141])).
% 3.21/1.52  tff(c_189, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k3_xboole_0(A_86, B_87))=k4_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.21/1.52  tff(c_201, plain, (![B_10]: (k5_xboole_0(B_10, B_10)=k4_xboole_0(B_10, B_10))), inference(superposition, [status(thm), theory('equality')], [c_149, c_189])).
% 3.21/1.52  tff(c_84, plain, (r1_tarski(k1_tarski('#skF_8'), k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.21/1.52  tff(c_148, plain, (k3_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_9'))=k1_tarski('#skF_8')), inference(resolution, [status(thm)], [c_84, c_141])).
% 3.21/1.52  tff(c_198, plain, (k5_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_189])).
% 3.21/1.52  tff(c_264, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_9'))=k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_198])).
% 3.21/1.52  tff(c_283, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_9'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_260, c_264])).
% 3.21/1.52  tff(c_983, plain, (![D_2382, A_2383, B_2384]: (r2_hidden(D_2382, k4_xboole_0(A_2383, B_2384)) | r2_hidden(D_2382, B_2384) | ~r2_hidden(D_2382, A_2383))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.52  tff(c_1000, plain, (![D_2382]: (r2_hidden(D_2382, k1_xboole_0) | r2_hidden(D_2382, k1_tarski('#skF_9')) | ~r2_hidden(D_2382, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_283, c_983])).
% 3.21/1.52  tff(c_1011, plain, (![D_2507]: (r2_hidden(D_2507, k1_tarski('#skF_9')) | ~r2_hidden(D_2507, k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_359, c_1000])).
% 3.21/1.52  tff(c_56, plain, (![C_26, A_22]: (C_26=A_22 | ~r2_hidden(C_26, k1_tarski(A_22)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.21/1.52  tff(c_1064, plain, (![D_2569]: (D_2569='#skF_9' | ~r2_hidden(D_2569, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_1011, c_56])).
% 3.21/1.52  tff(c_1080, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_58, c_1064])).
% 3.21/1.52  tff(c_1086, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_1080])).
% 3.21/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.52  
% 3.21/1.52  Inference rules
% 3.21/1.52  ----------------------
% 3.21/1.52  #Ref     : 0
% 3.21/1.52  #Sup     : 128
% 3.21/1.52  #Fact    : 0
% 3.21/1.52  #Define  : 0
% 3.21/1.52  #Split   : 3
% 3.21/1.52  #Chain   : 0
% 3.21/1.52  #Close   : 0
% 3.21/1.52  
% 3.21/1.52  Ordering : KBO
% 3.21/1.52  
% 3.21/1.53  Simplification rules
% 3.21/1.53  ----------------------
% 3.21/1.53  #Subsume      : 17
% 3.21/1.53  #Demod        : 17
% 3.21/1.53  #Tautology    : 50
% 3.21/1.53  #SimpNegUnit  : 7
% 3.21/1.53  #BackRed      : 2
% 3.21/1.53  
% 3.21/1.53  #Partial instantiations: 840
% 3.21/1.53  #Strategies tried      : 1
% 3.21/1.53  
% 3.21/1.53  Timing (in seconds)
% 3.21/1.53  ----------------------
% 3.21/1.53  Preprocessing        : 0.36
% 3.21/1.53  Parsing              : 0.18
% 3.21/1.53  CNF conversion       : 0.03
% 3.21/1.53  Main loop            : 0.35
% 3.21/1.53  Inferencing          : 0.17
% 3.21/1.53  Reduction            : 0.09
% 3.21/1.53  Demodulation         : 0.06
% 3.21/1.53  BG Simplification    : 0.02
% 3.21/1.53  Subsumption          : 0.06
% 3.21/1.53  Abstraction          : 0.02
% 3.21/1.53  MUC search           : 0.00
% 3.21/1.53  Cooper               : 0.00
% 3.21/1.53  Total                : 0.74
% 3.21/1.53  Index Insertion      : 0.00
% 3.21/1.53  Index Deletion       : 0.00
% 3.21/1.53  Index Matching       : 0.00
% 3.21/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
