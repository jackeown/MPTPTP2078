%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:19 EST 2020

% Result     : Theorem 6.59s
% Output     : CNFRefutation 6.59s
% Verified   : 
% Statistics : Number of formulae       :   53 (  62 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   55 (  70 expanded)
%              Number of equality atoms :   22 (  33 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_92,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(c_76,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_56,plain,(
    ! [C_31] : r2_hidden(C_31,k1_tarski(C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    ! [A_5,C_7,B_6] :
      ( r2_hidden(A_5,C_7)
      | ~ r2_hidden(A_5,B_6)
      | r2_hidden(A_5,k5_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    ! [A_18,B_19] : k3_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_248,plain,(
    ! [A_81,B_82,C_83] :
      ( ~ r1_xboole_0(A_81,B_82)
      | ~ r2_hidden(C_83,k3_xboole_0(A_81,B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_307,plain,(
    ! [A_90,B_91,C_92] :
      ( ~ r1_xboole_0(A_90,k2_xboole_0(A_90,B_91))
      | ~ r2_hidden(C_92,A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_248])).

tff(c_312,plain,(
    ! [C_92,A_3,B_91] :
      ( ~ r2_hidden(C_92,A_3)
      | k3_xboole_0(A_3,k2_xboole_0(A_3,B_91)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_307])).

tff(c_316,plain,(
    ! [C_93,A_94] :
      ( ~ r2_hidden(C_93,A_94)
      | k1_xboole_0 != A_94 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_312])).

tff(c_340,plain,(
    ! [C_31] : k1_tarski(C_31) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_316])).

tff(c_230,plain,(
    ! [A_79,B_80] :
      ( k2_xboole_0(k1_tarski(A_79),B_80) = B_80
      | ~ r2_hidden(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_7058,plain,(
    ! [A_14227,B_14228] :
      ( k3_xboole_0(k1_tarski(A_14227),B_14228) = k1_tarski(A_14227)
      | ~ r2_hidden(A_14227,B_14228) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_28])).

tff(c_78,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    ! [A_13,B_14] : r1_xboole_0(k3_xboole_0(A_13,B_14),k5_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_186,plain,(
    ! [A_71,B_72] :
      ( k3_xboole_0(A_71,B_72) = k1_xboole_0
      | ~ r1_xboole_0(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_261,plain,(
    ! [A_84,B_85] : k3_xboole_0(k3_xboole_0(A_84,B_85),k5_xboole_0(A_84,B_85)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_186])).

tff(c_283,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k5_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_261])).

tff(c_7120,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k5_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7058,c_283])).

tff(c_7234,plain,(
    ~ r2_hidden('#skF_6',k5_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_340,c_7120])).

tff(c_7257,plain,
    ( r2_hidden('#skF_6',k1_tarski('#skF_7'))
    | ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_18,c_7234])).

tff(c_7262,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_7257])).

tff(c_54,plain,(
    ! [C_31,A_27] :
      ( C_31 = A_27
      | ~ r2_hidden(C_31,k1_tarski(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_7280,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7262,c_54])).

tff(c_7293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_7280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:44:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.59/2.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.32  
% 6.59/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.32  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 6.59/2.32  
% 6.59/2.32  %Foreground sorts:
% 6.59/2.32  
% 6.59/2.32  
% 6.59/2.32  %Background operators:
% 6.59/2.32  
% 6.59/2.32  
% 6.59/2.32  %Foreground operators:
% 6.59/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.59/2.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.59/2.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.59/2.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.59/2.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.59/2.32  tff('#skF_7', type, '#skF_7': $i).
% 6.59/2.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.59/2.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.59/2.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.59/2.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.59/2.32  tff('#skF_6', type, '#skF_6': $i).
% 6.59/2.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.59/2.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.59/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.59/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.59/2.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.59/2.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.59/2.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.59/2.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.59/2.32  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.59/2.32  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.59/2.32  
% 6.59/2.33  tff(f_97, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 6.59/2.33  tff(f_80, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 6.59/2.33  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 6.59/2.33  tff(f_58, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 6.59/2.33  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.59/2.33  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.59/2.33  tff(f_92, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 6.59/2.33  tff(f_54, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 6.59/2.33  tff(c_76, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.59/2.33  tff(c_56, plain, (![C_31]: (r2_hidden(C_31, k1_tarski(C_31)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.59/2.33  tff(c_18, plain, (![A_5, C_7, B_6]: (r2_hidden(A_5, C_7) | ~r2_hidden(A_5, B_6) | r2_hidden(A_5, k5_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.59/2.33  tff(c_28, plain, (![A_18, B_19]: (k3_xboole_0(A_18, k2_xboole_0(A_18, B_19))=A_18)), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.59/2.33  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.59/2.33  tff(c_248, plain, (![A_81, B_82, C_83]: (~r1_xboole_0(A_81, B_82) | ~r2_hidden(C_83, k3_xboole_0(A_81, B_82)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.59/2.33  tff(c_307, plain, (![A_90, B_91, C_92]: (~r1_xboole_0(A_90, k2_xboole_0(A_90, B_91)) | ~r2_hidden(C_92, A_90))), inference(superposition, [status(thm), theory('equality')], [c_28, c_248])).
% 6.59/2.33  tff(c_312, plain, (![C_92, A_3, B_91]: (~r2_hidden(C_92, A_3) | k3_xboole_0(A_3, k2_xboole_0(A_3, B_91))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_307])).
% 6.59/2.33  tff(c_316, plain, (![C_93, A_94]: (~r2_hidden(C_93, A_94) | k1_xboole_0!=A_94)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_312])).
% 6.59/2.33  tff(c_340, plain, (![C_31]: (k1_tarski(C_31)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_316])).
% 6.59/2.33  tff(c_230, plain, (![A_79, B_80]: (k2_xboole_0(k1_tarski(A_79), B_80)=B_80 | ~r2_hidden(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.59/2.33  tff(c_7058, plain, (![A_14227, B_14228]: (k3_xboole_0(k1_tarski(A_14227), B_14228)=k1_tarski(A_14227) | ~r2_hidden(A_14227, B_14228))), inference(superposition, [status(thm), theory('equality')], [c_230, c_28])).
% 6.59/2.33  tff(c_78, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.59/2.33  tff(c_24, plain, (![A_13, B_14]: (r1_xboole_0(k3_xboole_0(A_13, B_14), k5_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.59/2.33  tff(c_186, plain, (![A_71, B_72]: (k3_xboole_0(A_71, B_72)=k1_xboole_0 | ~r1_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.59/2.33  tff(c_261, plain, (![A_84, B_85]: (k3_xboole_0(k3_xboole_0(A_84, B_85), k5_xboole_0(A_84, B_85))=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_186])).
% 6.59/2.33  tff(c_283, plain, (k3_xboole_0(k1_tarski('#skF_6'), k5_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_78, c_261])).
% 6.59/2.33  tff(c_7120, plain, (k1_tarski('#skF_6')=k1_xboole_0 | ~r2_hidden('#skF_6', k5_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_7058, c_283])).
% 6.59/2.33  tff(c_7234, plain, (~r2_hidden('#skF_6', k5_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_340, c_7120])).
% 6.59/2.33  tff(c_7257, plain, (r2_hidden('#skF_6', k1_tarski('#skF_7')) | ~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_18, c_7234])).
% 6.59/2.33  tff(c_7262, plain, (r2_hidden('#skF_6', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_7257])).
% 6.59/2.33  tff(c_54, plain, (![C_31, A_27]: (C_31=A_27 | ~r2_hidden(C_31, k1_tarski(A_27)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.59/2.33  tff(c_7280, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_7262, c_54])).
% 6.59/2.33  tff(c_7293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_7280])).
% 6.59/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.33  
% 6.59/2.33  Inference rules
% 6.59/2.33  ----------------------
% 6.59/2.33  #Ref     : 0
% 6.59/2.33  #Sup     : 1345
% 6.59/2.33  #Fact    : 18
% 6.59/2.33  #Define  : 0
% 6.59/2.33  #Split   : 2
% 6.59/2.33  #Chain   : 0
% 6.59/2.33  #Close   : 0
% 6.59/2.33  
% 6.59/2.33  Ordering : KBO
% 6.59/2.33  
% 6.59/2.33  Simplification rules
% 6.59/2.33  ----------------------
% 6.59/2.33  #Subsume      : 175
% 6.59/2.33  #Demod        : 429
% 6.59/2.33  #Tautology    : 478
% 6.59/2.33  #SimpNegUnit  : 69
% 6.59/2.33  #BackRed      : 1
% 6.59/2.33  
% 6.59/2.33  #Partial instantiations: 6496
% 6.59/2.33  #Strategies tried      : 1
% 6.59/2.33  
% 6.59/2.33  Timing (in seconds)
% 6.59/2.33  ----------------------
% 6.59/2.34  Preprocessing        : 0.32
% 6.59/2.34  Parsing              : 0.16
% 6.59/2.34  CNF conversion       : 0.03
% 6.59/2.34  Main loop            : 1.25
% 6.59/2.34  Inferencing          : 0.55
% 6.59/2.34  Reduction            : 0.42
% 6.59/2.34  Demodulation         : 0.33
% 6.59/2.34  BG Simplification    : 0.05
% 6.59/2.34  Subsumption          : 0.17
% 6.59/2.34  Abstraction          : 0.05
% 6.59/2.34  MUC search           : 0.00
% 6.59/2.34  Cooper               : 0.00
% 6.59/2.34  Total                : 1.60
% 6.59/2.34  Index Insertion      : 0.00
% 6.59/2.34  Index Deletion       : 0.00
% 6.59/2.34  Index Matching       : 0.00
% 6.59/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
