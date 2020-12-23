%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:26 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   61 (  80 expanded)
%              Number of leaves         :   30 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 ( 113 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
         => ( r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_50,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_32,plain,
    ( ~ r2_hidden('#skF_3',k3_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_2',k3_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_166,plain,(
    ~ r2_hidden('#skF_2',k3_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_186,plain,(
    ! [A_65] :
      ( k2_xboole_0(k1_relat_1(A_65),k2_relat_1(A_65)) = k3_relat_1(A_65)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_195,plain,(
    ! [A_65] :
      ( r1_tarski(k1_relat_1(A_65),k3_relat_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_8])).

tff(c_34,plain,(
    r2_hidden(k4_tarski('#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_223,plain,(
    ! [A_76,C_77,B_78] :
      ( r2_hidden(A_76,k1_relat_1(C_77))
      | ~ r2_hidden(k4_tarski(A_76,B_78),C_77)
      | ~ v1_relat_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_229,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_223])).

tff(c_233,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_229])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_251,plain,(
    ! [B_82] :
      ( r2_hidden('#skF_2',B_82)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_82) ) ),
    inference(resolution,[status(thm)],[c_233,c_2])).

tff(c_255,plain,
    ( r2_hidden('#skF_2',k3_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_195,c_251])).

tff(c_270,plain,(
    r2_hidden('#skF_2',k3_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_255])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_270])).

tff(c_273,plain,(
    ~ r2_hidden('#skF_3',k3_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_353,plain,(
    ! [A_98] :
      ( k2_xboole_0(k1_relat_1(A_98),k2_relat_1(A_98)) = k3_relat_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_80,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_95,plain,(
    ! [B_51,A_52] : k3_tarski(k2_tarski(B_51,A_52)) = k2_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_80])).

tff(c_24,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_118,plain,(
    ! [B_53,A_54] : k2_xboole_0(B_53,A_54) = k2_xboole_0(A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_24])).

tff(c_133,plain,(
    ! [A_54,B_53] : r1_tarski(A_54,k2_xboole_0(B_53,A_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_8])).

tff(c_359,plain,(
    ! [A_98] :
      ( r1_tarski(k2_relat_1(A_98),k3_relat_1(A_98))
      | ~ v1_relat_1(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_133])).

tff(c_578,plain,(
    ! [B_120,C_121,A_122] :
      ( r2_hidden(B_120,k2_relat_1(C_121))
      | ~ r2_hidden(k4_tarski(A_122,B_120),C_121)
      | ~ v1_relat_1(C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_584,plain,
    ( r2_hidden('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_578])).

tff(c_588,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_584])).

tff(c_592,plain,(
    ! [B_123] :
      ( r2_hidden('#skF_3',B_123)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_123) ) ),
    inference(resolution,[status(thm)],[c_588,c_2])).

tff(c_596,plain,
    ( r2_hidden('#skF_3',k3_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_359,c_592])).

tff(c_611,plain,(
    r2_hidden('#skF_3',k3_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_596])).

tff(c_613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_611])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.57  
% 2.70/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.57  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.70/1.57  
% 2.70/1.57  %Foreground sorts:
% 2.70/1.57  
% 2.70/1.57  
% 2.70/1.57  %Background operators:
% 2.70/1.57  
% 2.70/1.57  
% 2.70/1.57  %Foreground operators:
% 2.70/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.70/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.70/1.57  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.70/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.70/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.70/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.70/1.57  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.57  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.70/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.57  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.70/1.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.70/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.57  
% 2.70/1.58  tff(f_71, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 2.70/1.58  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 2.70/1.58  tff(f_34, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.70/1.58  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 2.70/1.58  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.70/1.58  tff(f_36, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.70/1.58  tff(f_50, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.70/1.58  tff(c_32, plain, (~r2_hidden('#skF_3', k3_relat_1('#skF_4')) | ~r2_hidden('#skF_2', k3_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.70/1.58  tff(c_166, plain, (~r2_hidden('#skF_2', k3_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.70/1.58  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.70/1.58  tff(c_186, plain, (![A_65]: (k2_xboole_0(k1_relat_1(A_65), k2_relat_1(A_65))=k3_relat_1(A_65) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.70/1.58  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.70/1.58  tff(c_195, plain, (![A_65]: (r1_tarski(k1_relat_1(A_65), k3_relat_1(A_65)) | ~v1_relat_1(A_65))), inference(superposition, [status(thm), theory('equality')], [c_186, c_8])).
% 2.70/1.58  tff(c_34, plain, (r2_hidden(k4_tarski('#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.70/1.58  tff(c_223, plain, (![A_76, C_77, B_78]: (r2_hidden(A_76, k1_relat_1(C_77)) | ~r2_hidden(k4_tarski(A_76, B_78), C_77) | ~v1_relat_1(C_77))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.70/1.58  tff(c_229, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_223])).
% 2.70/1.58  tff(c_233, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_229])).
% 2.70/1.58  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.70/1.58  tff(c_251, plain, (![B_82]: (r2_hidden('#skF_2', B_82) | ~r1_tarski(k1_relat_1('#skF_4'), B_82))), inference(resolution, [status(thm)], [c_233, c_2])).
% 2.70/1.58  tff(c_255, plain, (r2_hidden('#skF_2', k3_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_195, c_251])).
% 2.70/1.58  tff(c_270, plain, (r2_hidden('#skF_2', k3_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_255])).
% 2.70/1.58  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_270])).
% 2.70/1.58  tff(c_273, plain, (~r2_hidden('#skF_3', k3_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_32])).
% 2.70/1.58  tff(c_353, plain, (![A_98]: (k2_xboole_0(k1_relat_1(A_98), k2_relat_1(A_98))=k3_relat_1(A_98) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.70/1.58  tff(c_10, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.70/1.58  tff(c_80, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.70/1.58  tff(c_95, plain, (![B_51, A_52]: (k3_tarski(k2_tarski(B_51, A_52))=k2_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_10, c_80])).
% 2.70/1.58  tff(c_24, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.70/1.58  tff(c_118, plain, (![B_53, A_54]: (k2_xboole_0(B_53, A_54)=k2_xboole_0(A_54, B_53))), inference(superposition, [status(thm), theory('equality')], [c_95, c_24])).
% 2.70/1.58  tff(c_133, plain, (![A_54, B_53]: (r1_tarski(A_54, k2_xboole_0(B_53, A_54)))), inference(superposition, [status(thm), theory('equality')], [c_118, c_8])).
% 2.70/1.58  tff(c_359, plain, (![A_98]: (r1_tarski(k2_relat_1(A_98), k3_relat_1(A_98)) | ~v1_relat_1(A_98))), inference(superposition, [status(thm), theory('equality')], [c_353, c_133])).
% 2.70/1.58  tff(c_578, plain, (![B_120, C_121, A_122]: (r2_hidden(B_120, k2_relat_1(C_121)) | ~r2_hidden(k4_tarski(A_122, B_120), C_121) | ~v1_relat_1(C_121))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.70/1.58  tff(c_584, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_578])).
% 2.70/1.58  tff(c_588, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_584])).
% 2.70/1.58  tff(c_592, plain, (![B_123]: (r2_hidden('#skF_3', B_123) | ~r1_tarski(k2_relat_1('#skF_4'), B_123))), inference(resolution, [status(thm)], [c_588, c_2])).
% 2.70/1.58  tff(c_596, plain, (r2_hidden('#skF_3', k3_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_359, c_592])).
% 2.70/1.58  tff(c_611, plain, (r2_hidden('#skF_3', k3_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_596])).
% 2.70/1.58  tff(c_613, plain, $false, inference(negUnitSimplification, [status(thm)], [c_273, c_611])).
% 2.70/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.58  
% 2.70/1.58  Inference rules
% 2.70/1.58  ----------------------
% 2.70/1.58  #Ref     : 0
% 2.70/1.58  #Sup     : 126
% 2.70/1.58  #Fact    : 0
% 2.70/1.58  #Define  : 0
% 2.70/1.58  #Split   : 1
% 2.70/1.58  #Chain   : 0
% 2.70/1.58  #Close   : 0
% 2.70/1.58  
% 2.70/1.58  Ordering : KBO
% 2.70/1.58  
% 2.70/1.58  Simplification rules
% 2.70/1.58  ----------------------
% 2.70/1.58  #Subsume      : 3
% 2.70/1.58  #Demod        : 40
% 2.70/1.58  #Tautology    : 64
% 2.70/1.58  #SimpNegUnit  : 2
% 2.70/1.58  #BackRed      : 0
% 2.70/1.58  
% 2.70/1.58  #Partial instantiations: 0
% 2.70/1.58  #Strategies tried      : 1
% 2.70/1.58  
% 2.70/1.58  Timing (in seconds)
% 2.70/1.58  ----------------------
% 2.70/1.58  Preprocessing        : 0.45
% 2.70/1.58  Parsing              : 0.26
% 2.70/1.58  CNF conversion       : 0.02
% 2.70/1.59  Main loop            : 0.28
% 2.70/1.59  Inferencing          : 0.10
% 2.70/1.59  Reduction            : 0.10
% 2.70/1.59  Demodulation         : 0.07
% 2.70/1.59  BG Simplification    : 0.02
% 2.70/1.59  Subsumption          : 0.04
% 2.70/1.59  Abstraction          : 0.02
% 2.70/1.59  MUC search           : 0.00
% 2.70/1.59  Cooper               : 0.00
% 2.70/1.59  Total                : 0.76
% 2.70/1.59  Index Insertion      : 0.00
% 2.70/1.59  Index Deletion       : 0.00
% 2.70/1.59  Index Matching       : 0.00
% 2.70/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
