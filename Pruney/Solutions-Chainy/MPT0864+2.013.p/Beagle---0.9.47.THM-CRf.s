%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:10 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   54 (  79 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  93 expanded)
%              Number of equality atoms :   33 (  73 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_54,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    k4_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_50,plain,(
    ! [A_28,B_29] : k1_mcart_1(k4_tarski(A_28,B_29)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_59,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_50])).

tff(c_32,plain,
    ( k2_mcart_1('#skF_1') = '#skF_1'
    | k1_mcart_1('#skF_1') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_93,plain,
    ( k2_mcart_1('#skF_1') = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_32])).

tff(c_94,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_96,plain,(
    k4_tarski('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_34])).

tff(c_8,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    ! [A_30,B_31] : k2_xboole_0(k1_tarski(A_30),B_31) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_70,plain,(
    ! [A_30] : k1_tarski(A_30) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_66])).

tff(c_173,plain,(
    ! [A_48,B_49] : k2_zfmisc_1(k1_tarski(A_48),k1_tarski(B_49)) = k1_tarski(k4_tarski(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( ~ r1_tarski(A_16,k2_zfmisc_1(A_16,B_17))
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_182,plain,(
    ! [A_48,B_49] :
      ( ~ r1_tarski(k1_tarski(A_48),k1_tarski(k4_tarski(A_48,B_49)))
      | k1_tarski(A_48) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_22])).

tff(c_194,plain,(
    ! [A_52,B_53] : ~ r1_tarski(k1_tarski(A_52),k1_tarski(k4_tarski(A_52,B_53))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_182])).

tff(c_197,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_194])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_197])).

tff(c_201,plain,(
    k2_mcart_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_81,plain,(
    ! [A_34,B_35] : k2_mcart_1(k4_tarski(A_34,B_35)) = B_35 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_90,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_81])).

tff(c_216,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_90])).

tff(c_217,plain,(
    k4_tarski('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_34])).

tff(c_286,plain,(
    ! [A_69,B_70] : k2_zfmisc_1(k1_tarski(A_69),k1_tarski(B_70)) = k1_tarski(k4_tarski(A_69,B_70)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( ~ r1_tarski(A_16,k2_zfmisc_1(B_17,A_16))
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_295,plain,(
    ! [B_70,A_69] :
      ( ~ r1_tarski(k1_tarski(B_70),k1_tarski(k4_tarski(A_69,B_70)))
      | k1_tarski(B_70) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_20])).

tff(c_307,plain,(
    ! [B_73,A_74] : ~ r1_tarski(k1_tarski(B_73),k1_tarski(k4_tarski(A_74,B_73))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_295])).

tff(c_310,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_307])).

tff(c_313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_310])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:51:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.20  
% 1.99/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.20  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.99/1.20  
% 1.99/1.20  %Foreground sorts:
% 1.99/1.20  
% 1.99/1.20  
% 1.99/1.20  %Background operators:
% 1.99/1.20  
% 1.99/1.20  
% 1.99/1.20  %Foreground operators:
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.99/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.99/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.20  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.99/1.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.99/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.20  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.99/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.20  
% 1.99/1.21  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.99/1.21  tff(f_68, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 1.99/1.21  tff(f_58, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.99/1.21  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.99/1.21  tff(f_54, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.99/1.21  tff(f_51, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 1.99/1.21  tff(f_49, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 1.99/1.21  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.21  tff(c_34, plain, (k4_tarski('#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.99/1.21  tff(c_50, plain, (![A_28, B_29]: (k1_mcart_1(k4_tarski(A_28, B_29))=A_28)), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.99/1.21  tff(c_59, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_34, c_50])).
% 1.99/1.21  tff(c_32, plain, (k2_mcart_1('#skF_1')='#skF_1' | k1_mcart_1('#skF_1')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.99/1.21  tff(c_93, plain, (k2_mcart_1('#skF_1')='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_32])).
% 1.99/1.21  tff(c_94, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_93])).
% 1.99/1.21  tff(c_96, plain, (k4_tarski('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_34])).
% 1.99/1.21  tff(c_8, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.21  tff(c_66, plain, (![A_30, B_31]: (k2_xboole_0(k1_tarski(A_30), B_31)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.99/1.21  tff(c_70, plain, (![A_30]: (k1_tarski(A_30)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_66])).
% 1.99/1.21  tff(c_173, plain, (![A_48, B_49]: (k2_zfmisc_1(k1_tarski(A_48), k1_tarski(B_49))=k1_tarski(k4_tarski(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.99/1.21  tff(c_22, plain, (![A_16, B_17]: (~r1_tarski(A_16, k2_zfmisc_1(A_16, B_17)) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.99/1.21  tff(c_182, plain, (![A_48, B_49]: (~r1_tarski(k1_tarski(A_48), k1_tarski(k4_tarski(A_48, B_49))) | k1_tarski(A_48)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_173, c_22])).
% 1.99/1.21  tff(c_194, plain, (![A_52, B_53]: (~r1_tarski(k1_tarski(A_52), k1_tarski(k4_tarski(A_52, B_53))))), inference(negUnitSimplification, [status(thm)], [c_70, c_182])).
% 1.99/1.21  tff(c_197, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_194])).
% 1.99/1.21  tff(c_200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_197])).
% 1.99/1.21  tff(c_201, plain, (k2_mcart_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_93])).
% 1.99/1.21  tff(c_81, plain, (![A_34, B_35]: (k2_mcart_1(k4_tarski(A_34, B_35))=B_35)), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.99/1.21  tff(c_90, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_34, c_81])).
% 1.99/1.21  tff(c_216, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_201, c_90])).
% 1.99/1.21  tff(c_217, plain, (k4_tarski('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_216, c_34])).
% 1.99/1.21  tff(c_286, plain, (![A_69, B_70]: (k2_zfmisc_1(k1_tarski(A_69), k1_tarski(B_70))=k1_tarski(k4_tarski(A_69, B_70)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.99/1.21  tff(c_20, plain, (![A_16, B_17]: (~r1_tarski(A_16, k2_zfmisc_1(B_17, A_16)) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.99/1.21  tff(c_295, plain, (![B_70, A_69]: (~r1_tarski(k1_tarski(B_70), k1_tarski(k4_tarski(A_69, B_70))) | k1_tarski(B_70)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_286, c_20])).
% 1.99/1.21  tff(c_307, plain, (![B_73, A_74]: (~r1_tarski(k1_tarski(B_73), k1_tarski(k4_tarski(A_74, B_73))))), inference(negUnitSimplification, [status(thm)], [c_70, c_295])).
% 1.99/1.21  tff(c_310, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_217, c_307])).
% 1.99/1.21  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_310])).
% 1.99/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.21  
% 1.99/1.21  Inference rules
% 1.99/1.21  ----------------------
% 1.99/1.21  #Ref     : 0
% 1.99/1.21  #Sup     : 69
% 1.99/1.21  #Fact    : 0
% 1.99/1.21  #Define  : 0
% 1.99/1.21  #Split   : 1
% 1.99/1.21  #Chain   : 0
% 1.99/1.21  #Close   : 0
% 1.99/1.21  
% 1.99/1.21  Ordering : KBO
% 1.99/1.21  
% 1.99/1.21  Simplification rules
% 1.99/1.21  ----------------------
% 1.99/1.21  #Subsume      : 0
% 1.99/1.21  #Demod        : 14
% 1.99/1.21  #Tautology    : 55
% 1.99/1.21  #SimpNegUnit  : 4
% 1.99/1.21  #BackRed      : 3
% 1.99/1.21  
% 1.99/1.21  #Partial instantiations: 0
% 1.99/1.21  #Strategies tried      : 1
% 1.99/1.21  
% 1.99/1.21  Timing (in seconds)
% 1.99/1.21  ----------------------
% 1.99/1.22  Preprocessing        : 0.29
% 1.99/1.22  Parsing              : 0.16
% 1.99/1.22  CNF conversion       : 0.02
% 1.99/1.22  Main loop            : 0.16
% 1.99/1.22  Inferencing          : 0.06
% 1.99/1.22  Reduction            : 0.05
% 1.99/1.22  Demodulation         : 0.04
% 1.99/1.22  BG Simplification    : 0.01
% 1.99/1.22  Subsumption          : 0.02
% 1.99/1.22  Abstraction          : 0.01
% 1.99/1.22  MUC search           : 0.00
% 1.99/1.22  Cooper               : 0.00
% 1.99/1.22  Total                : 0.48
% 1.99/1.22  Index Insertion      : 0.00
% 1.99/1.22  Index Deletion       : 0.00
% 1.99/1.22  Index Matching       : 0.00
% 1.99/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
