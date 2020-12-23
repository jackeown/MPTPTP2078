%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:00 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 108 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 193 expanded)
%              Number of equality atoms :   22 (  63 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(c_36,plain,
    ( k1_mcart_1('#skF_1') != '#skF_3'
    | ~ r2_hidden(k2_mcart_1('#skF_1'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_75,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_1'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_34,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k2_tarski('#skF_2','#skF_3'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_77,plain,(
    ! [A_35,C_36,B_37] :
      ( r2_hidden(k2_mcart_1(A_35),C_36)
      | ~ r2_hidden(A_35,k2_zfmisc_1(B_37,C_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_79,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_77])).

tff(c_83,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_79])).

tff(c_84,plain,(
    k1_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_85,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38,plain,
    ( k1_mcart_1('#skF_1') != '#skF_2'
    | ~ r2_hidden(k2_mcart_1('#skF_1'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_87,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_38])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_102,plain,(
    ! [A_44,B_45,C_46] :
      ( r2_hidden(k1_mcart_1(A_44),B_45)
      | ~ r2_hidden(A_44,k2_zfmisc_1(B_45,C_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_105,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k2_tarski('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_102])).

tff(c_120,plain,(
    ! [C_66,A_67,B_68] :
      ( k4_xboole_0(C_66,k2_tarski(A_67,B_68)) = C_66
      | r2_hidden(B_68,C_66)
      | r2_hidden(A_67,C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [B_15,C_16,A_14] :
      ( ~ r2_hidden(B_15,C_16)
      | k4_xboole_0(k2_tarski(A_14,B_15),C_16) != k2_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_284,plain,(
    ! [B_90,A_91,B_92,A_93] :
      ( ~ r2_hidden(B_90,k2_tarski(A_91,B_92))
      | r2_hidden(B_92,k2_tarski(A_93,B_90))
      | r2_hidden(A_91,k2_tarski(A_93,B_90)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_18])).

tff(c_290,plain,(
    ! [A_94] :
      ( r2_hidden('#skF_3',k2_tarski(A_94,k1_mcart_1('#skF_1')))
      | r2_hidden('#skF_2',k2_tarski(A_94,k1_mcart_1('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_105,c_284])).

tff(c_296,plain,
    ( r2_hidden('#skF_3',k2_tarski(k1_mcart_1('#skF_1'),k1_mcart_1('#skF_1')))
    | r2_hidden('#skF_2',k1_tarski(k1_mcart_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_290])).

tff(c_298,plain,
    ( r2_hidden('#skF_3',k1_tarski(k1_mcart_1('#skF_1')))
    | r2_hidden('#skF_2',k1_tarski(k1_mcart_1('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_296])).

tff(c_299,plain,(
    r2_hidden('#skF_2',k1_tarski(k1_mcart_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_30,plain,(
    ! [A_23,B_24] : k1_mcart_1(k4_tarski(A_23,B_24)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_147,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( r2_hidden(k4_tarski(A_69,B_70),k2_zfmisc_1(C_71,D_72))
      | ~ r2_hidden(B_70,D_72)
      | ~ r2_hidden(A_69,C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [A_20,B_21,C_22] :
      ( k1_mcart_1(A_20) = B_21
      | ~ r2_hidden(A_20,k2_zfmisc_1(k1_tarski(B_21),C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_157,plain,(
    ! [A_69,B_70,B_21,D_72] :
      ( k1_mcart_1(k4_tarski(A_69,B_70)) = B_21
      | ~ r2_hidden(B_70,D_72)
      | ~ r2_hidden(A_69,k1_tarski(B_21)) ) ),
    inference(resolution,[status(thm)],[c_147,c_28])).

tff(c_165,plain,(
    ! [B_21,A_69,B_70,D_72] :
      ( B_21 = A_69
      | ~ r2_hidden(B_70,D_72)
      | ~ r2_hidden(A_69,k1_tarski(B_21)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_157])).

tff(c_170,plain,(
    ! [B_70,D_72] : ~ r2_hidden(B_70,D_72) ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_105])).

tff(c_181,plain,(
    ! [B_21,A_69] :
      ( B_21 = A_69
      | ~ r2_hidden(A_69,k1_tarski(B_21)) ) ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_308,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_299,c_181])).

tff(c_315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_308])).

tff(c_316,plain,(
    r2_hidden('#skF_3',k1_tarski(k1_mcart_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_362,plain,(
    k1_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_316,c_181])).

tff(c_369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_362])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.27  
% 2.09/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.27  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.09/1.27  
% 2.09/1.27  %Foreground sorts:
% 2.09/1.27  
% 2.09/1.27  
% 2.09/1.27  %Background operators:
% 2.09/1.27  
% 2.09/1.27  
% 2.09/1.27  %Foreground operators:
% 2.09/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.09/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.27  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.09/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.27  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.09/1.27  
% 2.09/1.28  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_mcart_1)).
% 2.09/1.28  tff(f_61, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.09/1.28  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.09/1.28  tff(f_47, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 2.09/1.28  tff(f_55, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 2.09/1.28  tff(f_71, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.09/1.28  tff(f_37, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.09/1.28  tff(f_67, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 2.09/1.28  tff(c_36, plain, (k1_mcart_1('#skF_1')!='#skF_3' | ~r2_hidden(k2_mcart_1('#skF_1'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.09/1.28  tff(c_75, plain, (~r2_hidden(k2_mcart_1('#skF_1'), '#skF_4')), inference(splitLeft, [status(thm)], [c_36])).
% 2.09/1.28  tff(c_34, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k2_tarski('#skF_2', '#skF_3'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.09/1.28  tff(c_77, plain, (![A_35, C_36, B_37]: (r2_hidden(k2_mcart_1(A_35), C_36) | ~r2_hidden(A_35, k2_zfmisc_1(B_37, C_36)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.09/1.28  tff(c_79, plain, (r2_hidden(k2_mcart_1('#skF_1'), '#skF_4')), inference(resolution, [status(thm)], [c_34, c_77])).
% 2.09/1.28  tff(c_83, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_79])).
% 2.09/1.28  tff(c_84, plain, (k1_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 2.09/1.28  tff(c_85, plain, (r2_hidden(k2_mcart_1('#skF_1'), '#skF_4')), inference(splitRight, [status(thm)], [c_36])).
% 2.09/1.28  tff(c_38, plain, (k1_mcart_1('#skF_1')!='#skF_2' | ~r2_hidden(k2_mcart_1('#skF_1'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.09/1.28  tff(c_87, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_38])).
% 2.09/1.28  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.09/1.28  tff(c_102, plain, (![A_44, B_45, C_46]: (r2_hidden(k1_mcart_1(A_44), B_45) | ~r2_hidden(A_44, k2_zfmisc_1(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.09/1.28  tff(c_105, plain, (r2_hidden(k1_mcart_1('#skF_1'), k2_tarski('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_102])).
% 2.09/1.28  tff(c_120, plain, (![C_66, A_67, B_68]: (k4_xboole_0(C_66, k2_tarski(A_67, B_68))=C_66 | r2_hidden(B_68, C_66) | r2_hidden(A_67, C_66))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.09/1.28  tff(c_18, plain, (![B_15, C_16, A_14]: (~r2_hidden(B_15, C_16) | k4_xboole_0(k2_tarski(A_14, B_15), C_16)!=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.09/1.28  tff(c_284, plain, (![B_90, A_91, B_92, A_93]: (~r2_hidden(B_90, k2_tarski(A_91, B_92)) | r2_hidden(B_92, k2_tarski(A_93, B_90)) | r2_hidden(A_91, k2_tarski(A_93, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_120, c_18])).
% 2.09/1.28  tff(c_290, plain, (![A_94]: (r2_hidden('#skF_3', k2_tarski(A_94, k1_mcart_1('#skF_1'))) | r2_hidden('#skF_2', k2_tarski(A_94, k1_mcart_1('#skF_1'))))), inference(resolution, [status(thm)], [c_105, c_284])).
% 2.09/1.28  tff(c_296, plain, (r2_hidden('#skF_3', k2_tarski(k1_mcart_1('#skF_1'), k1_mcart_1('#skF_1'))) | r2_hidden('#skF_2', k1_tarski(k1_mcart_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_290])).
% 2.09/1.28  tff(c_298, plain, (r2_hidden('#skF_3', k1_tarski(k1_mcart_1('#skF_1'))) | r2_hidden('#skF_2', k1_tarski(k1_mcart_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_296])).
% 2.09/1.28  tff(c_299, plain, (r2_hidden('#skF_2', k1_tarski(k1_mcart_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_298])).
% 2.09/1.28  tff(c_30, plain, (![A_23, B_24]: (k1_mcart_1(k4_tarski(A_23, B_24))=A_23)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.09/1.28  tff(c_147, plain, (![A_69, B_70, C_71, D_72]: (r2_hidden(k4_tarski(A_69, B_70), k2_zfmisc_1(C_71, D_72)) | ~r2_hidden(B_70, D_72) | ~r2_hidden(A_69, C_71))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.28  tff(c_28, plain, (![A_20, B_21, C_22]: (k1_mcart_1(A_20)=B_21 | ~r2_hidden(A_20, k2_zfmisc_1(k1_tarski(B_21), C_22)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.09/1.28  tff(c_157, plain, (![A_69, B_70, B_21, D_72]: (k1_mcart_1(k4_tarski(A_69, B_70))=B_21 | ~r2_hidden(B_70, D_72) | ~r2_hidden(A_69, k1_tarski(B_21)))), inference(resolution, [status(thm)], [c_147, c_28])).
% 2.09/1.28  tff(c_165, plain, (![B_21, A_69, B_70, D_72]: (B_21=A_69 | ~r2_hidden(B_70, D_72) | ~r2_hidden(A_69, k1_tarski(B_21)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_157])).
% 2.09/1.28  tff(c_170, plain, (![B_70, D_72]: (~r2_hidden(B_70, D_72))), inference(splitLeft, [status(thm)], [c_165])).
% 2.09/1.28  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_105])).
% 2.09/1.28  tff(c_181, plain, (![B_21, A_69]: (B_21=A_69 | ~r2_hidden(A_69, k1_tarski(B_21)))), inference(splitRight, [status(thm)], [c_165])).
% 2.09/1.28  tff(c_308, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_299, c_181])).
% 2.09/1.28  tff(c_315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_308])).
% 2.09/1.28  tff(c_316, plain, (r2_hidden('#skF_3', k1_tarski(k1_mcart_1('#skF_1')))), inference(splitRight, [status(thm)], [c_298])).
% 2.09/1.28  tff(c_362, plain, (k1_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_316, c_181])).
% 2.09/1.28  tff(c_369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_362])).
% 2.09/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.28  
% 2.09/1.28  Inference rules
% 2.09/1.28  ----------------------
% 2.09/1.28  #Ref     : 0
% 2.09/1.28  #Sup     : 64
% 2.09/1.28  #Fact    : 2
% 2.09/1.28  #Define  : 0
% 2.09/1.28  #Split   : 3
% 2.09/1.28  #Chain   : 0
% 2.09/1.28  #Close   : 0
% 2.09/1.28  
% 2.09/1.28  Ordering : KBO
% 2.09/1.28  
% 2.09/1.28  Simplification rules
% 2.09/1.28  ----------------------
% 2.09/1.28  #Subsume      : 13
% 2.09/1.28  #Demod        : 12
% 2.09/1.28  #Tautology    : 34
% 2.09/1.28  #SimpNegUnit  : 12
% 2.09/1.28  #BackRed      : 4
% 2.09/1.28  
% 2.09/1.28  #Partial instantiations: 0
% 2.09/1.28  #Strategies tried      : 1
% 2.09/1.28  
% 2.09/1.28  Timing (in seconds)
% 2.09/1.28  ----------------------
% 2.09/1.29  Preprocessing        : 0.30
% 2.09/1.29  Parsing              : 0.16
% 2.09/1.29  CNF conversion       : 0.02
% 2.09/1.29  Main loop            : 0.22
% 2.09/1.29  Inferencing          : 0.09
% 2.09/1.29  Reduction            : 0.07
% 2.09/1.29  Demodulation         : 0.04
% 2.09/1.29  BG Simplification    : 0.01
% 2.09/1.29  Subsumption          : 0.03
% 2.09/1.29  Abstraction          : 0.02
% 2.09/1.29  MUC search           : 0.00
% 2.09/1.29  Cooper               : 0.00
% 2.09/1.29  Total                : 0.55
% 2.09/1.29  Index Insertion      : 0.00
% 2.09/1.29  Index Deletion       : 0.00
% 2.09/1.29  Index Matching       : 0.00
% 2.09/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
