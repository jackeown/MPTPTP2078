%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:12 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   48 (  57 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 (  77 expanded)
%              Number of equality atoms :   21 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(c_48,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(k1_tarski(A_38),B_39) = k1_xboole_0
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | k4_xboole_0(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    ! [C_42,B_41] : r1_tarski(k1_tarski(C_42),k2_tarski(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_71,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = k1_xboole_0
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_85,plain,(
    ! [C_42,B_41] : k4_xboole_0(k1_tarski(C_42),k2_tarski(B_41,C_42)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_71])).

tff(c_206,plain,(
    ! [A_79,B_80] :
      ( r2_hidden(A_79,B_80)
      | k4_xboole_0(k1_tarski(A_79),B_80) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_217,plain,(
    ! [C_42,B_41] : r2_hidden(C_42,k2_tarski(B_41,C_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_206])).

tff(c_120,plain,(
    ! [A_68,B_69] :
      ( r1_xboole_0(A_68,B_69)
      | k4_xboole_0(A_68,B_69) != A_68 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_46,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden(A_43,B_44)
      | ~ r1_xboole_0(k1_tarski(A_43),B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_419,plain,(
    ! [A_98,B_99] :
      ( ~ r2_hidden(A_98,B_99)
      | k4_xboole_0(k1_tarski(A_98),B_99) != k1_tarski(A_98) ) ),
    inference(resolution,[status(thm)],[c_120,c_46])).

tff(c_433,plain,(
    ! [C_42,B_41] :
      ( ~ r2_hidden(C_42,k2_tarski(B_41,C_42))
      | k1_tarski(C_42) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_419])).

tff(c_439,plain,(
    ! [C_42] : k1_tarski(C_42) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_433])).

tff(c_42,plain,(
    ! [B_41,C_42] : r1_tarski(k1_tarski(B_41),k2_tarski(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_50,plain,(
    r1_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_442,plain,(
    ! [A_100,B_101,C_102] :
      ( k1_xboole_0 = A_100
      | ~ r1_xboole_0(B_101,C_102)
      | ~ r1_tarski(A_100,C_102)
      | ~ r1_tarski(A_100,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_453,plain,(
    ! [A_104] :
      ( k1_xboole_0 = A_104
      | ~ r1_tarski(A_104,'#skF_3')
      | ~ r1_tarski(A_104,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_50,c_442])).

tff(c_469,plain,
    ( k1_tarski('#skF_1') = k1_xboole_0
    | ~ r1_tarski(k1_tarski('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_453])).

tff(c_481,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_439,c_469])).

tff(c_491,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_481])).

tff(c_504,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_491])).

tff(c_508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_504])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.33  
% 2.47/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.47/1.34  
% 2.47/1.34  %Foreground sorts:
% 2.47/1.34  
% 2.47/1.34  
% 2.47/1.34  %Background operators:
% 2.47/1.34  
% 2.47/1.34  
% 2.47/1.34  %Foreground operators:
% 2.47/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.47/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.47/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.34  
% 2.47/1.35  tff(f_91, negated_conjecture, ~(![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.47/1.35  tff(f_65, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.47/1.35  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 2.47/1.35  tff(f_80, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_zfmisc_1)).
% 2.47/1.35  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.47/1.35  tff(f_85, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_zfmisc_1)).
% 2.47/1.35  tff(f_45, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 2.47/1.35  tff(c_48, plain, (r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.47/1.35  tff(c_34, plain, (![A_38, B_39]: (k4_xboole_0(k1_tarski(A_38), B_39)=k1_xboole_0 | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.47/1.35  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | k4_xboole_0(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.35  tff(c_40, plain, (![C_42, B_41]: (r1_tarski(k1_tarski(C_42), k2_tarski(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.47/1.35  tff(c_71, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=k1_xboole_0 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.35  tff(c_85, plain, (![C_42, B_41]: (k4_xboole_0(k1_tarski(C_42), k2_tarski(B_41, C_42))=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_71])).
% 2.47/1.35  tff(c_206, plain, (![A_79, B_80]: (r2_hidden(A_79, B_80) | k4_xboole_0(k1_tarski(A_79), B_80)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.47/1.35  tff(c_217, plain, (![C_42, B_41]: (r2_hidden(C_42, k2_tarski(B_41, C_42)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_206])).
% 2.47/1.35  tff(c_120, plain, (![A_68, B_69]: (r1_xboole_0(A_68, B_69) | k4_xboole_0(A_68, B_69)!=A_68)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.47/1.35  tff(c_46, plain, (![A_43, B_44]: (~r2_hidden(A_43, B_44) | ~r1_xboole_0(k1_tarski(A_43), B_44))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.47/1.35  tff(c_419, plain, (![A_98, B_99]: (~r2_hidden(A_98, B_99) | k4_xboole_0(k1_tarski(A_98), B_99)!=k1_tarski(A_98))), inference(resolution, [status(thm)], [c_120, c_46])).
% 2.47/1.35  tff(c_433, plain, (![C_42, B_41]: (~r2_hidden(C_42, k2_tarski(B_41, C_42)) | k1_tarski(C_42)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_85, c_419])).
% 2.47/1.35  tff(c_439, plain, (![C_42]: (k1_tarski(C_42)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_217, c_433])).
% 2.47/1.35  tff(c_42, plain, (![B_41, C_42]: (r1_tarski(k1_tarski(B_41), k2_tarski(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.47/1.35  tff(c_50, plain, (r1_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.47/1.35  tff(c_442, plain, (![A_100, B_101, C_102]: (k1_xboole_0=A_100 | ~r1_xboole_0(B_101, C_102) | ~r1_tarski(A_100, C_102) | ~r1_tarski(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.47/1.35  tff(c_453, plain, (![A_104]: (k1_xboole_0=A_104 | ~r1_tarski(A_104, '#skF_3') | ~r1_tarski(A_104, k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_50, c_442])).
% 2.47/1.35  tff(c_469, plain, (k1_tarski('#skF_1')=k1_xboole_0 | ~r1_tarski(k1_tarski('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_42, c_453])).
% 2.47/1.35  tff(c_481, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_439, c_469])).
% 2.47/1.35  tff(c_491, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_481])).
% 2.47/1.35  tff(c_504, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_491])).
% 2.47/1.35  tff(c_508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_504])).
% 2.47/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.35  
% 2.47/1.35  Inference rules
% 2.47/1.35  ----------------------
% 2.47/1.35  #Ref     : 0
% 2.47/1.35  #Sup     : 109
% 2.47/1.35  #Fact    : 0
% 2.47/1.35  #Define  : 0
% 2.47/1.35  #Split   : 0
% 2.47/1.35  #Chain   : 0
% 2.47/1.35  #Close   : 0
% 2.47/1.35  
% 2.47/1.35  Ordering : KBO
% 2.47/1.35  
% 2.47/1.35  Simplification rules
% 2.47/1.35  ----------------------
% 2.47/1.35  #Subsume      : 7
% 2.47/1.35  #Demod        : 18
% 2.47/1.35  #Tautology    : 50
% 2.47/1.35  #SimpNegUnit  : 2
% 2.47/1.35  #BackRed      : 0
% 2.47/1.35  
% 2.47/1.35  #Partial instantiations: 0
% 2.47/1.35  #Strategies tried      : 1
% 2.47/1.35  
% 2.47/1.35  Timing (in seconds)
% 2.47/1.35  ----------------------
% 2.47/1.35  Preprocessing        : 0.30
% 2.47/1.35  Parsing              : 0.16
% 2.47/1.35  CNF conversion       : 0.02
% 2.47/1.35  Main loop            : 0.23
% 2.47/1.35  Inferencing          : 0.09
% 2.47/1.35  Reduction            : 0.07
% 2.47/1.35  Demodulation         : 0.06
% 2.47/1.35  BG Simplification    : 0.02
% 2.47/1.35  Subsumption          : 0.04
% 2.47/1.35  Abstraction          : 0.02
% 2.47/1.35  MUC search           : 0.00
% 2.47/1.35  Cooper               : 0.00
% 2.47/1.35  Total                : 0.56
% 2.47/1.35  Index Insertion      : 0.00
% 2.47/1.35  Index Deletion       : 0.00
% 2.47/1.35  Index Matching       : 0.00
% 2.47/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
