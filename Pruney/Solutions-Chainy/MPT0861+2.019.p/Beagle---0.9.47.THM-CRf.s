%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:03 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   49 (  78 expanded)
%              Number of leaves         :   21 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 ( 139 expanded)
%              Number of equality atoms :   29 (  75 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) )
     => ( ! [D,E] : A != k4_tarski(D,E)
        | r2_hidden(A,k2_zfmisc_1(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_mcart_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
     => ( ( k1_mcart_1(A) = B
          | k1_mcart_1(A) = C )
        & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).

tff(c_26,plain,
    ( k1_mcart_1('#skF_1') != '#skF_3'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_57,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k2_tarski('#skF_2','#skF_3'),k1_tarski('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_67,plain,(
    ! [A_30,C_31,B_32] :
      ( r2_hidden(k2_mcart_1(A_30),C_31)
      | ~ r2_hidden(A_30,k2_zfmisc_1(B_32,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_24,c_67])).

tff(c_20,plain,(
    ! [A_21,B_22] : k1_mcart_1(k4_tarski(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    ! [A_21,B_22] : k2_mcart_1(k4_tarski(A_21,B_22)) = B_22 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [D_12,E_13,B_8,C_9] :
      ( r2_hidden(k4_tarski(D_12,E_13),k2_zfmisc_1(B_8,C_9))
      | ~ r2_hidden(k2_mcart_1(k4_tarski(D_12,E_13)),C_9)
      | ~ r2_hidden(k1_mcart_1(k4_tarski(D_12,E_13)),B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,(
    ! [D_39,E_40,B_41,C_42] :
      ( r2_hidden(k4_tarski(D_39,E_40),k2_zfmisc_1(B_41,C_42))
      | ~ r2_hidden(E_40,C_42)
      | ~ r2_hidden(D_39,B_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_10])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] :
      ( k1_mcart_1(A_14) = B_15
      | ~ r2_hidden(A_14,k2_zfmisc_1(k1_tarski(B_15),C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_82,plain,(
    ! [D_39,E_40,B_15,C_42] :
      ( k1_mcart_1(k4_tarski(D_39,E_40)) = B_15
      | ~ r2_hidden(E_40,C_42)
      | ~ r2_hidden(D_39,k1_tarski(B_15)) ) ),
    inference(resolution,[status(thm)],[c_76,c_14])).

tff(c_88,plain,(
    ! [D_39,B_15,E_40,C_42] :
      ( D_39 = B_15
      | ~ r2_hidden(E_40,C_42)
      | ~ r2_hidden(D_39,k1_tarski(B_15)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_82])).

tff(c_91,plain,(
    ! [E_40,C_42] : ~ r2_hidden(E_40,C_42) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_72,plain,(
    ! [A_36,B_37,C_38] :
      ( r2_hidden(k1_mcart_1(A_36),B_37)
      | ~ r2_hidden(A_36,k2_zfmisc_1(B_37,C_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_75,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k2_tarski('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_72])).

tff(c_112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_75])).

tff(c_114,plain,(
    ! [D_47,B_48] :
      ( D_47 = B_48
      | ~ r2_hidden(D_47,k1_tarski(B_48)) ) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_117,plain,(
    k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_70,c_114])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_117])).

tff(c_123,plain,(
    k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_28,plain,
    ( k1_mcart_1('#skF_1') != '#skF_2'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_124,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_124])).

tff(c_131,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_122,plain,(
    k1_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_181,plain,(
    ! [A_64,C_65,B_66,D_67] :
      ( k1_mcart_1(A_64) = C_65
      | k1_mcart_1(A_64) = B_66
      | ~ r2_hidden(A_64,k2_zfmisc_1(k2_tarski(B_66,C_65),D_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_188,plain,
    ( k1_mcart_1('#skF_1') = '#skF_3'
    | k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_24,c_181])).

tff(c_197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_122,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:25:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.21  
% 1.77/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.21  %$ r2_hidden > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.77/1.21  
% 1.77/1.21  %Foreground sorts:
% 1.77/1.21  
% 1.77/1.21  
% 1.77/1.21  %Background operators:
% 1.77/1.21  
% 1.77/1.21  
% 1.77/1.21  %Foreground operators:
% 1.77/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.77/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.77/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.77/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.77/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.77/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.77/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.21  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.77/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.77/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.77/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.21  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.77/1.21  
% 1.99/1.23  tff(f_72, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_mcart_1)).
% 1.99/1.23  tff(f_35, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.99/1.23  tff(f_63, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.99/1.23  tff(f_45, axiom, (![A, B, C]: ((r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)) => ((![D, E]: ~(A = k4_tarski(D, E))) | r2_hidden(A, k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_mcart_1)).
% 1.99/1.23  tff(f_51, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 1.99/1.23  tff(f_59, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_mcart_1)).
% 1.99/1.23  tff(c_26, plain, (k1_mcart_1('#skF_1')!='#skF_3' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.99/1.23  tff(c_57, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(splitLeft, [status(thm)], [c_26])).
% 1.99/1.23  tff(c_24, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k2_tarski('#skF_2', '#skF_3'), k1_tarski('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.99/1.23  tff(c_67, plain, (![A_30, C_31, B_32]: (r2_hidden(k2_mcart_1(A_30), C_31) | ~r2_hidden(A_30, k2_zfmisc_1(B_32, C_31)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.99/1.23  tff(c_70, plain, (r2_hidden(k2_mcart_1('#skF_1'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_67])).
% 1.99/1.23  tff(c_20, plain, (![A_21, B_22]: (k1_mcart_1(k4_tarski(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.99/1.23  tff(c_22, plain, (![A_21, B_22]: (k2_mcart_1(k4_tarski(A_21, B_22))=B_22)), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.99/1.23  tff(c_10, plain, (![D_12, E_13, B_8, C_9]: (r2_hidden(k4_tarski(D_12, E_13), k2_zfmisc_1(B_8, C_9)) | ~r2_hidden(k2_mcart_1(k4_tarski(D_12, E_13)), C_9) | ~r2_hidden(k1_mcart_1(k4_tarski(D_12, E_13)), B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.99/1.23  tff(c_76, plain, (![D_39, E_40, B_41, C_42]: (r2_hidden(k4_tarski(D_39, E_40), k2_zfmisc_1(B_41, C_42)) | ~r2_hidden(E_40, C_42) | ~r2_hidden(D_39, B_41))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_10])).
% 1.99/1.23  tff(c_14, plain, (![A_14, B_15, C_16]: (k1_mcart_1(A_14)=B_15 | ~r2_hidden(A_14, k2_zfmisc_1(k1_tarski(B_15), C_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.99/1.23  tff(c_82, plain, (![D_39, E_40, B_15, C_42]: (k1_mcart_1(k4_tarski(D_39, E_40))=B_15 | ~r2_hidden(E_40, C_42) | ~r2_hidden(D_39, k1_tarski(B_15)))), inference(resolution, [status(thm)], [c_76, c_14])).
% 1.99/1.23  tff(c_88, plain, (![D_39, B_15, E_40, C_42]: (D_39=B_15 | ~r2_hidden(E_40, C_42) | ~r2_hidden(D_39, k1_tarski(B_15)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_82])).
% 1.99/1.23  tff(c_91, plain, (![E_40, C_42]: (~r2_hidden(E_40, C_42))), inference(splitLeft, [status(thm)], [c_88])).
% 1.99/1.23  tff(c_72, plain, (![A_36, B_37, C_38]: (r2_hidden(k1_mcart_1(A_36), B_37) | ~r2_hidden(A_36, k2_zfmisc_1(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.99/1.23  tff(c_75, plain, (r2_hidden(k1_mcart_1('#skF_1'), k2_tarski('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_72])).
% 1.99/1.23  tff(c_112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_75])).
% 1.99/1.23  tff(c_114, plain, (![D_47, B_48]: (D_47=B_48 | ~r2_hidden(D_47, k1_tarski(B_48)))), inference(splitRight, [status(thm)], [c_88])).
% 1.99/1.23  tff(c_117, plain, (k2_mcart_1('#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_70, c_114])).
% 1.99/1.23  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_117])).
% 1.99/1.23  tff(c_123, plain, (k2_mcart_1('#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_26])).
% 1.99/1.23  tff(c_28, plain, (k1_mcart_1('#skF_1')!='#skF_2' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.99/1.23  tff(c_124, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(splitLeft, [status(thm)], [c_28])).
% 1.99/1.23  tff(c_130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_124])).
% 1.99/1.23  tff(c_131, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitRight, [status(thm)], [c_28])).
% 1.99/1.23  tff(c_122, plain, (k1_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 1.99/1.23  tff(c_181, plain, (![A_64, C_65, B_66, D_67]: (k1_mcart_1(A_64)=C_65 | k1_mcart_1(A_64)=B_66 | ~r2_hidden(A_64, k2_zfmisc_1(k2_tarski(B_66, C_65), D_67)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.99/1.23  tff(c_188, plain, (k1_mcart_1('#skF_1')='#skF_3' | k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_24, c_181])).
% 1.99/1.23  tff(c_197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_122, c_188])).
% 1.99/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.23  
% 1.99/1.23  Inference rules
% 1.99/1.23  ----------------------
% 1.99/1.23  #Ref     : 0
% 1.99/1.23  #Sup     : 31
% 1.99/1.23  #Fact    : 0
% 1.99/1.23  #Define  : 0
% 1.99/1.23  #Split   : 4
% 1.99/1.23  #Chain   : 0
% 1.99/1.23  #Close   : 0
% 1.99/1.23  
% 1.99/1.23  Ordering : KBO
% 1.99/1.23  
% 1.99/1.23  Simplification rules
% 1.99/1.23  ----------------------
% 1.99/1.23  #Subsume      : 13
% 1.99/1.23  #Demod        : 15
% 1.99/1.23  #Tautology    : 19
% 1.99/1.23  #SimpNegUnit  : 14
% 1.99/1.23  #BackRed      : 6
% 1.99/1.23  
% 1.99/1.23  #Partial instantiations: 0
% 1.99/1.23  #Strategies tried      : 1
% 1.99/1.23  
% 1.99/1.23  Timing (in seconds)
% 1.99/1.23  ----------------------
% 1.99/1.23  Preprocessing        : 0.30
% 1.99/1.23  Parsing              : 0.16
% 1.99/1.23  CNF conversion       : 0.02
% 1.99/1.23  Main loop            : 0.17
% 1.99/1.23  Inferencing          : 0.07
% 1.99/1.23  Reduction            : 0.05
% 1.99/1.23  Demodulation         : 0.04
% 1.99/1.23  BG Simplification    : 0.01
% 1.99/1.23  Subsumption          : 0.02
% 1.99/1.23  Abstraction          : 0.01
% 1.99/1.23  MUC search           : 0.00
% 1.99/1.23  Cooper               : 0.00
% 1.99/1.23  Total                : 0.50
% 1.99/1.23  Index Insertion      : 0.00
% 1.99/1.23  Index Deletion       : 0.00
% 1.99/1.23  Index Matching       : 0.00
% 1.99/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
