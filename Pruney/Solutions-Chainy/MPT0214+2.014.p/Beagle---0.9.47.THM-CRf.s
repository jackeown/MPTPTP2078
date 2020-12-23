%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:31 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 114 expanded)
%              Number of leaves         :   31 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   64 ( 155 expanded)
%              Number of equality atoms :   29 (  72 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_46,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_82,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_18,plain,(
    ! [B_5] : r1_tarski(B_5,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_84,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_275,plain,(
    ! [B_81,A_82] :
      ( k1_tarski(B_81) = A_82
      | k1_xboole_0 = A_82
      | ~ r1_tarski(A_82,k1_tarski(B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_291,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_6')
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_275])).

tff(c_303,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_54,plain,(
    ! [C_23] : r2_hidden(C_23,k1_tarski(C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_316,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_54])).

tff(c_22,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_157,plain,(
    ! [B_73,A_74] :
      ( B_73 = A_74
      | ~ r1_tarski(B_73,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_173,plain,(
    ! [A_75] :
      ( k1_xboole_0 = A_75
      | ~ r1_tarski(A_75,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_157])).

tff(c_192,plain,(
    ! [B_76] : k3_xboole_0(k1_xboole_0,B_76) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_173])).

tff(c_20,plain,(
    ! [A_6,B_7] : k5_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_206,plain,(
    ! [B_77] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_20])).

tff(c_197,plain,(
    ! [B_76] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_20])).

tff(c_215,plain,(
    ! [B_79,B_78] : k4_xboole_0(k1_xboole_0,B_79) = k4_xboole_0(k1_xboole_0,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_197])).

tff(c_26,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_231,plain,(
    ! [B_79] : k4_xboole_0(k1_xboole_0,B_79) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_26])).

tff(c_257,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_197])).

tff(c_661,plain,(
    ! [A_1774,C_1775,B_1776] :
      ( ~ r2_hidden(A_1774,C_1775)
      | ~ r2_hidden(A_1774,B_1776)
      | ~ r2_hidden(A_1774,k5_xboole_0(B_1776,C_1775)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_677,plain,(
    ! [A_1823] :
      ( ~ r2_hidden(A_1823,k1_xboole_0)
      | ~ r2_hidden(A_1823,k1_xboole_0)
      | ~ r2_hidden(A_1823,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_661])).

tff(c_679,plain,(
    ~ r2_hidden('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_316,c_677])).

tff(c_683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_679])).

tff(c_684,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_166,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_6')
    | ~ r1_tarski(k1_tarski('#skF_6'),k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_84,c_157])).

tff(c_191,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_687,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_684,c_191])).

tff(c_691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_687])).

tff(c_692,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_702,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_692,c_54])).

tff(c_52,plain,(
    ! [C_23,A_19] :
      ( C_23 = A_19
      | ~ r2_hidden(C_23,k1_tarski(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_722,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_702,c_52])).

tff(c_726,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_722])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:17:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.38  
% 2.69/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.39  %$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 2.69/1.39  
% 2.69/1.39  %Foreground sorts:
% 2.69/1.39  
% 2.69/1.39  
% 2.69/1.39  %Background operators:
% 2.69/1.39  
% 2.69/1.39  
% 2.69/1.39  %Foreground operators:
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.69/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.69/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.69/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.69/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.69/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.69/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.69/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.69/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.69/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.69/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.69/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.69/1.39  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.69/1.39  
% 2.69/1.40  tff(f_91, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.69/1.40  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.69/1.40  tff(f_86, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.69/1.40  tff(f_68, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.69/1.40  tff(f_42, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.69/1.40  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.69/1.40  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.69/1.40  tff(f_46, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.69/1.40  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.69/1.40  tff(c_82, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.69/1.40  tff(c_18, plain, (![B_5]: (r1_tarski(B_5, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.69/1.40  tff(c_84, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.69/1.40  tff(c_275, plain, (![B_81, A_82]: (k1_tarski(B_81)=A_82 | k1_xboole_0=A_82 | ~r1_tarski(A_82, k1_tarski(B_81)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.69/1.40  tff(c_291, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6') | k1_tarski('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_84, c_275])).
% 2.69/1.40  tff(c_303, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_291])).
% 2.69/1.40  tff(c_54, plain, (![C_23]: (r2_hidden(C_23, k1_tarski(C_23)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.69/1.40  tff(c_316, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_303, c_54])).
% 2.69/1.40  tff(c_22, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.69/1.40  tff(c_24, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.69/1.40  tff(c_157, plain, (![B_73, A_74]: (B_73=A_74 | ~r1_tarski(B_73, A_74) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.69/1.40  tff(c_173, plain, (![A_75]: (k1_xboole_0=A_75 | ~r1_tarski(A_75, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_157])).
% 2.69/1.40  tff(c_192, plain, (![B_76]: (k3_xboole_0(k1_xboole_0, B_76)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_173])).
% 2.69/1.40  tff(c_20, plain, (![A_6, B_7]: (k5_xboole_0(A_6, k3_xboole_0(A_6, B_7))=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.69/1.40  tff(c_206, plain, (![B_77]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_77))), inference(superposition, [status(thm), theory('equality')], [c_192, c_20])).
% 2.69/1.40  tff(c_197, plain, (![B_76]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_76))), inference(superposition, [status(thm), theory('equality')], [c_192, c_20])).
% 2.69/1.40  tff(c_215, plain, (![B_79, B_78]: (k4_xboole_0(k1_xboole_0, B_79)=k4_xboole_0(k1_xboole_0, B_78))), inference(superposition, [status(thm), theory('equality')], [c_206, c_197])).
% 2.69/1.40  tff(c_26, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.69/1.40  tff(c_231, plain, (![B_79]: (k4_xboole_0(k1_xboole_0, B_79)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_215, c_26])).
% 2.69/1.40  tff(c_257, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_231, c_197])).
% 2.69/1.40  tff(c_661, plain, (![A_1774, C_1775, B_1776]: (~r2_hidden(A_1774, C_1775) | ~r2_hidden(A_1774, B_1776) | ~r2_hidden(A_1774, k5_xboole_0(B_1776, C_1775)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.69/1.40  tff(c_677, plain, (![A_1823]: (~r2_hidden(A_1823, k1_xboole_0) | ~r2_hidden(A_1823, k1_xboole_0) | ~r2_hidden(A_1823, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_257, c_661])).
% 2.69/1.40  tff(c_679, plain, (~r2_hidden('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_316, c_677])).
% 2.69/1.40  tff(c_683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_316, c_679])).
% 2.69/1.40  tff(c_684, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_291])).
% 2.69/1.40  tff(c_166, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski('#skF_6'), k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_84, c_157])).
% 2.69/1.40  tff(c_191, plain, (~r1_tarski(k1_tarski('#skF_6'), k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_166])).
% 2.69/1.40  tff(c_687, plain, (~r1_tarski(k1_tarski('#skF_6'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_684, c_191])).
% 2.69/1.40  tff(c_691, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_687])).
% 2.69/1.40  tff(c_692, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_166])).
% 2.69/1.40  tff(c_702, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_692, c_54])).
% 2.69/1.40  tff(c_52, plain, (![C_23, A_19]: (C_23=A_19 | ~r2_hidden(C_23, k1_tarski(A_19)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.69/1.40  tff(c_722, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_702, c_52])).
% 2.69/1.40  tff(c_726, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_722])).
% 2.69/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.40  
% 2.69/1.40  Inference rules
% 2.69/1.40  ----------------------
% 2.69/1.40  #Ref     : 0
% 2.69/1.40  #Sup     : 111
% 2.69/1.40  #Fact    : 0
% 2.69/1.40  #Define  : 0
% 2.69/1.40  #Split   : 3
% 2.69/1.40  #Chain   : 0
% 2.69/1.40  #Close   : 0
% 2.69/1.40  
% 2.69/1.40  Ordering : KBO
% 2.69/1.40  
% 2.69/1.40  Simplification rules
% 2.69/1.40  ----------------------
% 2.69/1.40  #Subsume      : 14
% 2.69/1.40  #Demod        : 33
% 2.69/1.40  #Tautology    : 68
% 2.69/1.40  #SimpNegUnit  : 1
% 2.69/1.40  #BackRed      : 7
% 2.69/1.40  
% 2.69/1.40  #Partial instantiations: 629
% 2.69/1.40  #Strategies tried      : 1
% 2.69/1.40  
% 2.69/1.40  Timing (in seconds)
% 2.69/1.40  ----------------------
% 2.69/1.40  Preprocessing        : 0.33
% 2.69/1.40  Parsing              : 0.17
% 2.69/1.40  CNF conversion       : 0.03
% 2.69/1.40  Main loop            : 0.31
% 2.69/1.40  Inferencing          : 0.14
% 2.69/1.40  Reduction            : 0.09
% 2.69/1.40  Demodulation         : 0.06
% 2.69/1.40  BG Simplification    : 0.02
% 2.69/1.40  Subsumption          : 0.05
% 2.69/1.40  Abstraction          : 0.01
% 2.69/1.40  MUC search           : 0.00
% 2.69/1.40  Cooper               : 0.00
% 2.69/1.40  Total                : 0.67
% 2.69/1.40  Index Insertion      : 0.00
% 2.69/1.40  Index Deletion       : 0.00
% 2.69/1.40  Index Matching       : 0.00
% 2.69/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
