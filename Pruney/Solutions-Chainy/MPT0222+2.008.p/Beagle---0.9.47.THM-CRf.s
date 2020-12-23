%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:16 EST 2020

% Result     : Theorem 4.76s
% Output     : CNFRefutation 4.82s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

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

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_289,plain,(
    ! [A_52,B_53,C_54] :
      ( ~ r1_tarski('#skF_1'(A_52,B_53,C_54),A_52)
      | k3_xboole_0(B_53,C_54) = A_52
      | ~ r1_tarski(A_52,C_54)
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_401,plain,(
    ! [B_64,C_65,B_66] :
      ( k3_xboole_0(B_64,C_65) = B_66
      | ~ r1_tarski(B_66,C_65)
      | ~ r1_tarski(B_66,B_64)
      | k4_xboole_0('#skF_1'(B_66,B_64,C_65),B_66) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_289])).

tff(c_1776,plain,(
    ! [B_121,C_122] :
      ( k3_xboole_0(B_121,C_122) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,C_122)
      | ~ r1_tarski(k1_xboole_0,B_121)
      | '#skF_1'(k1_xboole_0,B_121,C_122) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_401])).

tff(c_1784,plain,(
    ! [B_123,B_124] :
      ( k3_xboole_0(B_123,k1_tarski(B_124)) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_123)
      | '#skF_1'(k1_xboole_0,B_123,k1_tarski(B_124)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_1776])).

tff(c_1828,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski('#skF_2'))
    | '#skF_1'(k1_xboole_0,k1_tarski('#skF_2'),k1_tarski('#skF_3')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1784,c_48])).

tff(c_1867,plain,(
    '#skF_1'(k1_xboole_0,k1_tarski('#skF_2'),k1_tarski('#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1828])).

tff(c_180,plain,(
    ! [A_39,B_40,C_41] :
      ( r1_tarski('#skF_1'(A_39,B_40,C_41),C_41)
      | k3_xboole_0(B_40,C_41) = A_39
      | ~ r1_tarski(A_39,C_41)
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

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

tff(c_3524,plain,(
    ! [B_157,B_158] :
      ( '#skF_1'(k1_xboole_0,B_157,k1_tarski(B_158)) = k1_tarski(B_158)
      | '#skF_1'(k1_xboole_0,B_157,k1_tarski(B_158)) = k1_xboole_0
      | k3_xboole_0(B_157,k1_tarski(B_158)) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_157) ) ),
    inference(resolution,[status(thm)],[c_26,c_1637])).

tff(c_3609,plain,
    ( '#skF_1'(k1_xboole_0,k1_tarski('#skF_2'),k1_tarski('#skF_3')) = k1_tarski('#skF_3')
    | '#skF_1'(k1_xboole_0,k1_tarski('#skF_2'),k1_tarski('#skF_3')) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3524,c_48])).

tff(c_3686,plain,
    ( '#skF_1'(k1_xboole_0,k1_tarski('#skF_2'),k1_tarski('#skF_3')) = k1_tarski('#skF_3')
    | '#skF_1'(k1_xboole_0,k1_tarski('#skF_2'),k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3609])).

tff(c_3687,plain,(
    '#skF_1'(k1_xboole_0,k1_tarski('#skF_2'),k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1867,c_3686])).

tff(c_14,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski('#skF_1'(A_5,B_6,C_7),B_6)
      | k3_xboole_0(B_6,C_7) = A_5
      | ~ r1_tarski(A_5,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3726,plain,
    ( r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_2'))
    | k3_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_3')) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_tarski('#skF_3'))
    | ~ r1_tarski(k1_xboole_0,k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3687,c_14])).

tff(c_3751,plain,
    ( r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_2'))
    | k3_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_3726])).

tff(c_3752,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_3751])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | ~ r1_tarski(k1_tarski(A_15),k1_tarski(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3784,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3752,c_28])).

tff(c_3809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_3784])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:10:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.76/1.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.95  
% 4.82/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.95  %$ r1_xboole_0 > r1_tarski > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 4.82/1.95  
% 4.82/1.95  %Foreground sorts:
% 4.82/1.95  
% 4.82/1.95  
% 4.82/1.95  %Background operators:
% 4.82/1.95  
% 4.82/1.95  
% 4.82/1.95  %Foreground operators:
% 4.82/1.95  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.82/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.82/1.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.82/1.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.82/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.82/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.82/1.95  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.82/1.95  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.82/1.95  tff('#skF_2', type, '#skF_2': $i).
% 4.82/1.95  tff('#skF_3', type, '#skF_3': $i).
% 4.82/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.82/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.82/1.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.82/1.95  
% 4.82/1.96  tff(f_68, negated_conjecture, ~(![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 4.82/1.96  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.82/1.96  tff(f_58, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.82/1.96  tff(f_48, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.82/1.96  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.82/1.96  tff(f_46, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_xboole_1)).
% 4.82/1.96  tff(f_62, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 4.82/1.96  tff(c_32, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.82/1.96  tff(c_44, plain, (![A_20, B_21]: (r1_xboole_0(A_20, B_21) | k3_xboole_0(A_20, B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.82/1.96  tff(c_30, plain, (~r1_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.82/1.96  tff(c_48, plain, (k3_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_30])).
% 4.82/1.96  tff(c_26, plain, (![B_14]: (r1_tarski(k1_xboole_0, k1_tarski(B_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.82/1.96  tff(c_16, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.82/1.96  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.82/1.96  tff(c_289, plain, (![A_52, B_53, C_54]: (~r1_tarski('#skF_1'(A_52, B_53, C_54), A_52) | k3_xboole_0(B_53, C_54)=A_52 | ~r1_tarski(A_52, C_54) | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.82/1.96  tff(c_401, plain, (![B_64, C_65, B_66]: (k3_xboole_0(B_64, C_65)=B_66 | ~r1_tarski(B_66, C_65) | ~r1_tarski(B_66, B_64) | k4_xboole_0('#skF_1'(B_66, B_64, C_65), B_66)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_289])).
% 4.82/1.96  tff(c_1776, plain, (![B_121, C_122]: (k3_xboole_0(B_121, C_122)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, C_122) | ~r1_tarski(k1_xboole_0, B_121) | '#skF_1'(k1_xboole_0, B_121, C_122)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_401])).
% 4.82/1.96  tff(c_1784, plain, (![B_123, B_124]: (k3_xboole_0(B_123, k1_tarski(B_124))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_123) | '#skF_1'(k1_xboole_0, B_123, k1_tarski(B_124))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_1776])).
% 4.82/1.96  tff(c_1828, plain, (~r1_tarski(k1_xboole_0, k1_tarski('#skF_2')) | '#skF_1'(k1_xboole_0, k1_tarski('#skF_2'), k1_tarski('#skF_3'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1784, c_48])).
% 4.82/1.96  tff(c_1867, plain, ('#skF_1'(k1_xboole_0, k1_tarski('#skF_2'), k1_tarski('#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1828])).
% 4.82/1.96  tff(c_180, plain, (![A_39, B_40, C_41]: (r1_tarski('#skF_1'(A_39, B_40, C_41), C_41) | k3_xboole_0(B_40, C_41)=A_39 | ~r1_tarski(A_39, C_41) | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.82/1.96  tff(c_22, plain, (![B_14, A_13]: (k1_tarski(B_14)=A_13 | k1_xboole_0=A_13 | ~r1_tarski(A_13, k1_tarski(B_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.82/1.96  tff(c_1637, plain, (![A_107, B_108, B_109]: ('#skF_1'(A_107, B_108, k1_tarski(B_109))=k1_tarski(B_109) | '#skF_1'(A_107, B_108, k1_tarski(B_109))=k1_xboole_0 | k3_xboole_0(B_108, k1_tarski(B_109))=A_107 | ~r1_tarski(A_107, k1_tarski(B_109)) | ~r1_tarski(A_107, B_108))), inference(resolution, [status(thm)], [c_180, c_22])).
% 4.82/1.96  tff(c_3524, plain, (![B_157, B_158]: ('#skF_1'(k1_xboole_0, B_157, k1_tarski(B_158))=k1_tarski(B_158) | '#skF_1'(k1_xboole_0, B_157, k1_tarski(B_158))=k1_xboole_0 | k3_xboole_0(B_157, k1_tarski(B_158))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_157))), inference(resolution, [status(thm)], [c_26, c_1637])).
% 4.82/1.96  tff(c_3609, plain, ('#skF_1'(k1_xboole_0, k1_tarski('#skF_2'), k1_tarski('#skF_3'))=k1_tarski('#skF_3') | '#skF_1'(k1_xboole_0, k1_tarski('#skF_2'), k1_tarski('#skF_3'))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3524, c_48])).
% 4.82/1.96  tff(c_3686, plain, ('#skF_1'(k1_xboole_0, k1_tarski('#skF_2'), k1_tarski('#skF_3'))=k1_tarski('#skF_3') | '#skF_1'(k1_xboole_0, k1_tarski('#skF_2'), k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3609])).
% 4.82/1.96  tff(c_3687, plain, ('#skF_1'(k1_xboole_0, k1_tarski('#skF_2'), k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1867, c_3686])).
% 4.82/1.96  tff(c_14, plain, (![A_5, B_6, C_7]: (r1_tarski('#skF_1'(A_5, B_6, C_7), B_6) | k3_xboole_0(B_6, C_7)=A_5 | ~r1_tarski(A_5, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.82/1.96  tff(c_3726, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_2')) | k3_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3'))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_tarski('#skF_3')) | ~r1_tarski(k1_xboole_0, k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3687, c_14])).
% 4.82/1.96  tff(c_3751, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_2')) | k3_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_3726])).
% 4.82/1.96  tff(c_3752, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_3751])).
% 4.82/1.96  tff(c_28, plain, (![B_16, A_15]: (B_16=A_15 | ~r1_tarski(k1_tarski(A_15), k1_tarski(B_16)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.82/1.96  tff(c_3784, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_3752, c_28])).
% 4.82/1.96  tff(c_3809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_3784])).
% 4.82/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.96  
% 4.82/1.96  Inference rules
% 4.82/1.96  ----------------------
% 4.82/1.96  #Ref     : 0
% 4.82/1.96  #Sup     : 832
% 4.82/1.96  #Fact    : 0
% 4.82/1.96  #Define  : 0
% 4.82/1.96  #Split   : 0
% 4.82/1.96  #Chain   : 0
% 4.82/1.96  #Close   : 0
% 4.82/1.96  
% 4.82/1.96  Ordering : KBO
% 4.82/1.96  
% 4.82/1.96  Simplification rules
% 4.82/1.96  ----------------------
% 4.82/1.96  #Subsume      : 52
% 4.82/1.96  #Demod        : 1397
% 4.82/1.96  #Tautology    : 381
% 4.82/1.96  #SimpNegUnit  : 13
% 4.82/1.96  #BackRed      : 1
% 4.82/1.96  
% 4.82/1.96  #Partial instantiations: 0
% 4.82/1.96  #Strategies tried      : 1
% 4.82/1.96  
% 4.82/1.96  Timing (in seconds)
% 4.82/1.96  ----------------------
% 4.82/1.96  Preprocessing        : 0.30
% 4.82/1.96  Parsing              : 0.16
% 4.82/1.96  CNF conversion       : 0.02
% 4.82/1.96  Main loop            : 0.84
% 4.82/1.96  Inferencing          : 0.29
% 4.82/1.96  Reduction            : 0.30
% 4.82/1.96  Demodulation         : 0.23
% 4.82/1.96  BG Simplification    : 0.04
% 4.82/1.96  Subsumption          : 0.16
% 4.82/1.96  Abstraction          : 0.05
% 4.82/1.96  MUC search           : 0.00
% 4.82/1.96  Cooper               : 0.00
% 4.82/1.96  Total                : 1.17
% 4.82/1.96  Index Insertion      : 0.00
% 4.82/1.96  Index Deletion       : 0.00
% 4.82/1.96  Index Matching       : 0.00
% 4.82/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
