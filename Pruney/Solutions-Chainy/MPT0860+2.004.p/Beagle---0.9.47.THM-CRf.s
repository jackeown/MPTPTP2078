%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:00 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   50 (  80 expanded)
%              Number of leaves         :   24 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 ( 126 expanded)
%              Number of equality atoms :   19 (  48 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
       => ( r2_hidden(k1_mcart_1(A),B)
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_34,plain,
    ( k2_mcart_1('#skF_3') != '#skF_6'
    | ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_53,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_32,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1('#skF_4',k2_tarski('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_72,plain,(
    ! [A_30,B_31,C_32] :
      ( r2_hidden(k1_mcart_1(A_30),B_31)
      | ~ r2_hidden(A_30,k2_zfmisc_1(B_31,C_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_74,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_72])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_74])).

tff(c_79,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_80,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_91,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_36])).

tff(c_97,plain,(
    ! [A_38,C_39,B_40] :
      ( r2_hidden(k2_mcart_1(A_38),C_39)
      | ~ r2_hidden(A_38,k2_zfmisc_1(B_40,C_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_100,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_32,c_97])).

tff(c_136,plain,(
    ! [C_56,A_57,B_58] :
      ( k4_xboole_0(C_56,k2_tarski(A_57,B_58)) = C_56
      | r2_hidden(B_58,C_56)
      | r2_hidden(A_57,C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_110,plain,(
    ! [A_44,C_45,B_46] :
      ( ~ r2_hidden(A_44,C_45)
      | k4_xboole_0(k2_tarski(A_44,B_46),C_45) != k2_tarski(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_113,plain,(
    ! [A_6,C_45] :
      ( ~ r2_hidden(A_6,C_45)
      | k4_xboole_0(k1_tarski(A_6),C_45) != k2_tarski(A_6,A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_110])).

tff(c_114,plain,(
    ! [A_6,C_45] :
      ( ~ r2_hidden(A_6,C_45)
      | k4_xboole_0(k1_tarski(A_6),C_45) != k1_tarski(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_113])).

tff(c_249,plain,(
    ! [A_77,A_78,B_79] :
      ( ~ r2_hidden(A_77,k2_tarski(A_78,B_79))
      | r2_hidden(B_79,k1_tarski(A_77))
      | r2_hidden(A_78,k1_tarski(A_77)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_114])).

tff(c_270,plain,
    ( r2_hidden('#skF_6',k1_tarski(k2_mcart_1('#skF_3')))
    | r2_hidden('#skF_5',k1_tarski(k2_mcart_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_100,c_249])).

tff(c_271,plain,(
    r2_hidden('#skF_5',k1_tarski(k2_mcart_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_321,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_271,c_2])).

tff(c_328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_321])).

tff(c_329,plain,(
    r2_hidden('#skF_6',k1_tarski(k2_mcart_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_339,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_329,c_2])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:51:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.30  
% 2.05/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.30  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.05/1.30  
% 2.05/1.30  %Foreground sorts:
% 2.05/1.30  
% 2.05/1.30  
% 2.05/1.30  %Background operators:
% 2.05/1.30  
% 2.05/1.30  
% 2.05/1.30  %Foreground operators:
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.05/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.05/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.05/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.30  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.05/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.05/1.30  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.05/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.05/1.30  
% 2.30/1.31  tff(f_71, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_mcart_1)).
% 2.30/1.31  tff(f_62, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.30/1.31  tff(f_48, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 2.30/1.31  tff(f_34, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.30/1.31  tff(f_56, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 2.30/1.31  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.30/1.31  tff(c_34, plain, (k2_mcart_1('#skF_3')!='#skF_6' | ~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.30/1.31  tff(c_53, plain, (~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_34])).
% 2.30/1.31  tff(c_32, plain, (r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', k2_tarski('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.30/1.31  tff(c_72, plain, (![A_30, B_31, C_32]: (r2_hidden(k1_mcart_1(A_30), B_31) | ~r2_hidden(A_30, k2_zfmisc_1(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.30/1.31  tff(c_74, plain, (r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_32, c_72])).
% 2.30/1.31  tff(c_78, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_74])).
% 2.30/1.31  tff(c_79, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitRight, [status(thm)], [c_34])).
% 2.30/1.31  tff(c_80, plain, (r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_34])).
% 2.30/1.31  tff(c_36, plain, (k2_mcart_1('#skF_3')!='#skF_5' | ~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.30/1.31  tff(c_91, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_36])).
% 2.30/1.31  tff(c_97, plain, (![A_38, C_39, B_40]: (r2_hidden(k2_mcart_1(A_38), C_39) | ~r2_hidden(A_38, k2_zfmisc_1(B_40, C_39)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.30/1.31  tff(c_100, plain, (r2_hidden(k2_mcart_1('#skF_3'), k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_32, c_97])).
% 2.30/1.31  tff(c_136, plain, (![C_56, A_57, B_58]: (k4_xboole_0(C_56, k2_tarski(A_57, B_58))=C_56 | r2_hidden(B_58, C_56) | r2_hidden(A_57, C_56))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.30/1.31  tff(c_14, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.30/1.31  tff(c_110, plain, (![A_44, C_45, B_46]: (~r2_hidden(A_44, C_45) | k4_xboole_0(k2_tarski(A_44, B_46), C_45)!=k2_tarski(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.30/1.31  tff(c_113, plain, (![A_6, C_45]: (~r2_hidden(A_6, C_45) | k4_xboole_0(k1_tarski(A_6), C_45)!=k2_tarski(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_14, c_110])).
% 2.30/1.31  tff(c_114, plain, (![A_6, C_45]: (~r2_hidden(A_6, C_45) | k4_xboole_0(k1_tarski(A_6), C_45)!=k1_tarski(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_113])).
% 2.30/1.31  tff(c_249, plain, (![A_77, A_78, B_79]: (~r2_hidden(A_77, k2_tarski(A_78, B_79)) | r2_hidden(B_79, k1_tarski(A_77)) | r2_hidden(A_78, k1_tarski(A_77)))), inference(superposition, [status(thm), theory('equality')], [c_136, c_114])).
% 2.30/1.31  tff(c_270, plain, (r2_hidden('#skF_6', k1_tarski(k2_mcart_1('#skF_3'))) | r2_hidden('#skF_5', k1_tarski(k2_mcart_1('#skF_3')))), inference(resolution, [status(thm)], [c_100, c_249])).
% 2.30/1.31  tff(c_271, plain, (r2_hidden('#skF_5', k1_tarski(k2_mcart_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_270])).
% 2.30/1.31  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.30/1.31  tff(c_321, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_271, c_2])).
% 2.30/1.31  tff(c_328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_321])).
% 2.30/1.31  tff(c_329, plain, (r2_hidden('#skF_6', k1_tarski(k2_mcart_1('#skF_3')))), inference(splitRight, [status(thm)], [c_270])).
% 2.30/1.31  tff(c_339, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_329, c_2])).
% 2.30/1.31  tff(c_346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_339])).
% 2.30/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.31  
% 2.30/1.31  Inference rules
% 2.30/1.31  ----------------------
% 2.30/1.31  #Ref     : 0
% 2.30/1.31  #Sup     : 67
% 2.30/1.31  #Fact    : 0
% 2.30/1.31  #Define  : 0
% 2.30/1.31  #Split   : 2
% 2.30/1.31  #Chain   : 0
% 2.30/1.31  #Close   : 0
% 2.30/1.31  
% 2.30/1.31  Ordering : KBO
% 2.30/1.31  
% 2.30/1.31  Simplification rules
% 2.30/1.31  ----------------------
% 2.30/1.31  #Subsume      : 3
% 2.30/1.31  #Demod        : 10
% 2.30/1.31  #Tautology    : 29
% 2.30/1.31  #SimpNegUnit  : 3
% 2.30/1.31  #BackRed      : 0
% 2.30/1.31  
% 2.30/1.31  #Partial instantiations: 0
% 2.30/1.31  #Strategies tried      : 1
% 2.30/1.31  
% 2.30/1.31  Timing (in seconds)
% 2.30/1.31  ----------------------
% 2.30/1.32  Preprocessing        : 0.30
% 2.30/1.32  Parsing              : 0.15
% 2.30/1.32  CNF conversion       : 0.02
% 2.30/1.32  Main loop            : 0.23
% 2.30/1.32  Inferencing          : 0.08
% 2.30/1.32  Reduction            : 0.07
% 2.30/1.32  Demodulation         : 0.04
% 2.30/1.32  BG Simplification    : 0.01
% 2.30/1.32  Subsumption          : 0.04
% 2.30/1.32  Abstraction          : 0.02
% 2.30/1.32  MUC search           : 0.00
% 2.30/1.32  Cooper               : 0.00
% 2.30/1.32  Total                : 0.55
% 2.30/1.32  Index Insertion      : 0.00
% 2.30/1.32  Index Deletion       : 0.00
% 2.30/1.32  Index Matching       : 0.00
% 2.30/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
