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
% DateTime   : Thu Dec  3 09:48:16 EST 2020

% Result     : Theorem 4.72s
% Output     : CNFRefutation 4.72s
% Verified   : 
% Statistics : Number of formulae       :   47 (  71 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :   82 ( 135 expanded)
%              Number of equality atoms :   41 (  64 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_32,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_44,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | k3_xboole_0(A_20,B_21) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_48,plain,(
    k3_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_30])).

tff(c_26,plain,(
    ! [B_14] : r1_tarski(k1_xboole_0,k1_tarski(B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_221,plain,(
    ! [A_46,B_47,C_48] :
      ( ~ r1_tarski('#skF_1'(A_46,B_47,C_48),A_46)
      | k3_xboole_0(B_47,C_48) = A_46
      | ~ r1_tarski(A_46,C_48)
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_401,plain,(
    ! [B_64,C_65,B_66] :
      ( k3_xboole_0(B_64,C_65) = B_66
      | ~ r1_tarski(B_66,C_65)
      | ~ r1_tarski(B_66,B_64)
      | k4_xboole_0('#skF_1'(B_66,B_64,C_65),B_66) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_221])).

tff(c_1712,plain,(
    ! [B_116,C_117] :
      ( k3_xboole_0(B_116,C_117) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,C_117)
      | ~ r1_tarski(k1_xboole_0,B_116)
      | '#skF_1'(k1_xboole_0,B_116,C_117) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_401])).

tff(c_1765,plain,(
    ! [B_120,B_121] :
      ( k3_xboole_0(B_120,k1_tarski(B_121)) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_120)
      | '#skF_1'(k1_xboole_0,B_120,k1_tarski(B_121)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_1712])).

tff(c_1809,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski('#skF_2'))
    | '#skF_1'(k1_xboole_0,k1_tarski('#skF_2'),k1_tarski('#skF_3')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1765,c_48])).

tff(c_1848,plain,(
    '#skF_1'(k1_xboole_0,k1_tarski('#skF_2'),k1_tarski('#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1809])).

tff(c_180,plain,(
    ! [A_39,B_40,C_41] :
      ( r1_tarski('#skF_1'(A_39,B_40,C_41),C_41)
      | k3_xboole_0(B_40,C_41) = A_39
      | ~ r1_tarski(A_39,C_41)
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( k1_tarski(B_14) = A_13
      | k1_xboole_0 = A_13
      | ~ r1_tarski(A_13,k1_tarski(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1637,plain,(
    ! [A_107,B_108,B_109] :
      ( '#skF_1'(A_107,B_108,k1_tarski(B_109)) = k1_tarski(B_109)
      | '#skF_1'(A_107,B_108,k1_tarski(B_109)) = k1_xboole_0
      | k3_xboole_0(B_108,k1_tarski(B_109)) = A_107
      | ~ r1_tarski(A_107,k1_tarski(B_109))
      | ~ r1_tarski(A_107,B_108) ) ),
    inference(resolution,[status(thm)],[c_180,c_22])).

tff(c_3475,plain,(
    ! [B_157,B_158] :
      ( '#skF_1'(k1_xboole_0,B_157,k1_tarski(B_158)) = k1_tarski(B_158)
      | '#skF_1'(k1_xboole_0,B_157,k1_tarski(B_158)) = k1_xboole_0
      | k3_xboole_0(B_157,k1_tarski(B_158)) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_157) ) ),
    inference(resolution,[status(thm)],[c_26,c_1637])).

tff(c_3561,plain,
    ( '#skF_1'(k1_xboole_0,k1_tarski('#skF_2'),k1_tarski('#skF_3')) = k1_tarski('#skF_3')
    | '#skF_1'(k1_xboole_0,k1_tarski('#skF_2'),k1_tarski('#skF_3')) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3475,c_48])).

tff(c_3639,plain,
    ( '#skF_1'(k1_xboole_0,k1_tarski('#skF_2'),k1_tarski('#skF_3')) = k1_tarski('#skF_3')
    | '#skF_1'(k1_xboole_0,k1_tarski('#skF_2'),k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3561])).

tff(c_3640,plain,(
    '#skF_1'(k1_xboole_0,k1_tarski('#skF_2'),k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1848,c_3639])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski('#skF_1'(A_3,B_4,C_5),B_4)
      | k3_xboole_0(B_4,C_5) = A_3
      | ~ r1_tarski(A_3,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3676,plain,
    ( r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_2'))
    | k3_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_3')) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_tarski('#skF_3'))
    | ~ r1_tarski(k1_xboole_0,k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3640,c_10])).

tff(c_3701,plain,
    ( r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_2'))
    | k3_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_3676])).

tff(c_3702,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_3701])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | ~ r1_tarski(k1_tarski(A_15),k1_tarski(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3740,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3702,c_28])).

tff(c_3763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_3740])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:43:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.72/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.72/2.02  
% 4.72/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.72/2.02  %$ r1_xboole_0 > r1_tarski > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 4.72/2.02  
% 4.72/2.02  %Foreground sorts:
% 4.72/2.02  
% 4.72/2.02  
% 4.72/2.02  %Background operators:
% 4.72/2.02  
% 4.72/2.02  
% 4.72/2.02  %Foreground operators:
% 4.72/2.02  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.72/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.72/2.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.72/2.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.72/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.72/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.72/2.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.72/2.02  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.72/2.02  tff('#skF_2', type, '#skF_2': $i).
% 4.72/2.02  tff('#skF_3', type, '#skF_3': $i).
% 4.72/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.72/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.72/2.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.72/2.02  
% 4.72/2.03  tff(f_68, negated_conjecture, ~(![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 4.72/2.03  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.72/2.03  tff(f_58, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.72/2.03  tff(f_48, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.72/2.03  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 4.72/2.03  tff(f_42, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 4.72/2.03  tff(f_62, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 4.72/2.03  tff(c_32, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.72/2.03  tff(c_44, plain, (![A_20, B_21]: (r1_xboole_0(A_20, B_21) | k3_xboole_0(A_20, B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.72/2.03  tff(c_30, plain, (~r1_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.72/2.03  tff(c_48, plain, (k3_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_30])).
% 4.72/2.03  tff(c_26, plain, (![B_14]: (r1_tarski(k1_xboole_0, k1_tarski(B_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.72/2.03  tff(c_16, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.72/2.03  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.72/2.03  tff(c_221, plain, (![A_46, B_47, C_48]: (~r1_tarski('#skF_1'(A_46, B_47, C_48), A_46) | k3_xboole_0(B_47, C_48)=A_46 | ~r1_tarski(A_46, C_48) | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.72/2.03  tff(c_401, plain, (![B_64, C_65, B_66]: (k3_xboole_0(B_64, C_65)=B_66 | ~r1_tarski(B_66, C_65) | ~r1_tarski(B_66, B_64) | k4_xboole_0('#skF_1'(B_66, B_64, C_65), B_66)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_221])).
% 4.72/2.03  tff(c_1712, plain, (![B_116, C_117]: (k3_xboole_0(B_116, C_117)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, C_117) | ~r1_tarski(k1_xboole_0, B_116) | '#skF_1'(k1_xboole_0, B_116, C_117)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_401])).
% 4.72/2.03  tff(c_1765, plain, (![B_120, B_121]: (k3_xboole_0(B_120, k1_tarski(B_121))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_120) | '#skF_1'(k1_xboole_0, B_120, k1_tarski(B_121))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_1712])).
% 4.72/2.03  tff(c_1809, plain, (~r1_tarski(k1_xboole_0, k1_tarski('#skF_2')) | '#skF_1'(k1_xboole_0, k1_tarski('#skF_2'), k1_tarski('#skF_3'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1765, c_48])).
% 4.72/2.03  tff(c_1848, plain, ('#skF_1'(k1_xboole_0, k1_tarski('#skF_2'), k1_tarski('#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1809])).
% 4.72/2.03  tff(c_180, plain, (![A_39, B_40, C_41]: (r1_tarski('#skF_1'(A_39, B_40, C_41), C_41) | k3_xboole_0(B_40, C_41)=A_39 | ~r1_tarski(A_39, C_41) | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.72/2.03  tff(c_22, plain, (![B_14, A_13]: (k1_tarski(B_14)=A_13 | k1_xboole_0=A_13 | ~r1_tarski(A_13, k1_tarski(B_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.72/2.03  tff(c_1637, plain, (![A_107, B_108, B_109]: ('#skF_1'(A_107, B_108, k1_tarski(B_109))=k1_tarski(B_109) | '#skF_1'(A_107, B_108, k1_tarski(B_109))=k1_xboole_0 | k3_xboole_0(B_108, k1_tarski(B_109))=A_107 | ~r1_tarski(A_107, k1_tarski(B_109)) | ~r1_tarski(A_107, B_108))), inference(resolution, [status(thm)], [c_180, c_22])).
% 4.72/2.03  tff(c_3475, plain, (![B_157, B_158]: ('#skF_1'(k1_xboole_0, B_157, k1_tarski(B_158))=k1_tarski(B_158) | '#skF_1'(k1_xboole_0, B_157, k1_tarski(B_158))=k1_xboole_0 | k3_xboole_0(B_157, k1_tarski(B_158))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_157))), inference(resolution, [status(thm)], [c_26, c_1637])).
% 4.72/2.03  tff(c_3561, plain, ('#skF_1'(k1_xboole_0, k1_tarski('#skF_2'), k1_tarski('#skF_3'))=k1_tarski('#skF_3') | '#skF_1'(k1_xboole_0, k1_tarski('#skF_2'), k1_tarski('#skF_3'))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3475, c_48])).
% 4.72/2.03  tff(c_3639, plain, ('#skF_1'(k1_xboole_0, k1_tarski('#skF_2'), k1_tarski('#skF_3'))=k1_tarski('#skF_3') | '#skF_1'(k1_xboole_0, k1_tarski('#skF_2'), k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3561])).
% 4.72/2.03  tff(c_3640, plain, ('#skF_1'(k1_xboole_0, k1_tarski('#skF_2'), k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1848, c_3639])).
% 4.72/2.03  tff(c_10, plain, (![A_3, B_4, C_5]: (r1_tarski('#skF_1'(A_3, B_4, C_5), B_4) | k3_xboole_0(B_4, C_5)=A_3 | ~r1_tarski(A_3, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.72/2.03  tff(c_3676, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_2')) | k3_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3'))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_tarski('#skF_3')) | ~r1_tarski(k1_xboole_0, k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3640, c_10])).
% 4.72/2.03  tff(c_3701, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_2')) | k3_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_3676])).
% 4.72/2.03  tff(c_3702, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_3701])).
% 4.72/2.03  tff(c_28, plain, (![B_16, A_15]: (B_16=A_15 | ~r1_tarski(k1_tarski(A_15), k1_tarski(B_16)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.72/2.03  tff(c_3740, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_3702, c_28])).
% 4.72/2.03  tff(c_3763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_3740])).
% 4.72/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.72/2.03  
% 4.72/2.03  Inference rules
% 4.72/2.03  ----------------------
% 4.72/2.03  #Ref     : 0
% 4.72/2.03  #Sup     : 821
% 4.72/2.03  #Fact    : 0
% 4.72/2.03  #Define  : 0
% 4.72/2.03  #Split   : 0
% 4.72/2.03  #Chain   : 0
% 4.72/2.03  #Close   : 0
% 4.72/2.03  
% 4.72/2.03  Ordering : KBO
% 4.72/2.03  
% 4.72/2.03  Simplification rules
% 4.72/2.03  ----------------------
% 4.72/2.03  #Subsume      : 51
% 4.72/2.03  #Demod        : 1406
% 4.72/2.03  #Tautology    : 382
% 4.72/2.03  #SimpNegUnit  : 13
% 4.72/2.03  #BackRed      : 1
% 4.72/2.03  
% 4.72/2.03  #Partial instantiations: 0
% 4.72/2.03  #Strategies tried      : 1
% 4.72/2.03  
% 4.72/2.03  Timing (in seconds)
% 4.72/2.03  ----------------------
% 4.72/2.03  Preprocessing        : 0.38
% 4.72/2.03  Parsing              : 0.20
% 4.72/2.03  CNF conversion       : 0.02
% 4.72/2.03  Main loop            : 0.85
% 4.72/2.03  Inferencing          : 0.29
% 4.72/2.03  Reduction            : 0.31
% 4.72/2.03  Demodulation         : 0.24
% 4.72/2.03  BG Simplification    : 0.04
% 4.72/2.03  Subsumption          : 0.17
% 4.72/2.03  Abstraction          : 0.05
% 4.72/2.03  MUC search           : 0.00
% 4.72/2.03  Cooper               : 0.00
% 4.72/2.03  Total                : 1.26
% 4.72/2.03  Index Insertion      : 0.00
% 4.72/2.03  Index Deletion       : 0.00
% 4.72/2.03  Index Matching       : 0.00
% 4.72/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
