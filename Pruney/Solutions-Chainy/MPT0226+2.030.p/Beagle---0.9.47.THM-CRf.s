%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:41 EST 2020

% Result     : Theorem 12.39s
% Output     : CNFRefutation 12.51s
% Verified   : 
% Statistics : Number of formulae       :   57 (  96 expanded)
%              Number of leaves         :   30 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 ( 134 expanded)
%              Number of equality atoms :   32 (  72 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_66,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_70,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_56,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_219,plain,(
    ! [A_68,B_69] : k1_enumset1(A_68,A_68,B_69) = k2_tarski(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_38,plain,(
    ! [E_23,B_18,C_19] : r2_hidden(E_23,k1_enumset1(E_23,B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_267,plain,(
    ! [A_73,B_74] : r2_hidden(A_73,k2_tarski(A_73,B_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_38])).

tff(c_270,plain,(
    ! [A_24] : r2_hidden(A_24,k1_tarski(A_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_267])).

tff(c_72,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_781,plain,(
    ! [D_110,A_111,B_112] :
      ( r2_hidden(D_110,k4_xboole_0(A_111,B_112))
      | r2_hidden(D_110,B_112)
      | ~ r2_hidden(D_110,A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_944,plain,(
    ! [D_121] :
      ( r2_hidden(D_121,k1_xboole_0)
      | r2_hidden(D_121,k1_tarski('#skF_6'))
      | ~ r2_hidden(D_121,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_781])).

tff(c_953,plain,
    ( r2_hidden('#skF_5',k1_xboole_0)
    | r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_270,c_944])).

tff(c_954,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_953])).

tff(c_58,plain,(
    ! [A_25,B_26] : k1_enumset1(A_25,A_25,B_26) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_804,plain,(
    ! [E_113,C_114,B_115,A_116] :
      ( E_113 = C_114
      | E_113 = B_115
      | E_113 = A_116
      | ~ r2_hidden(E_113,k1_enumset1(A_116,B_115,C_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22164,plain,(
    ! [E_327,B_328,A_329] :
      ( E_327 = B_328
      | E_327 = A_329
      | E_327 = A_329
      | ~ r2_hidden(E_327,k2_tarski(A_329,B_328)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_804])).

tff(c_22233,plain,(
    ! [E_330,A_331] :
      ( E_330 = A_331
      | E_330 = A_331
      | E_330 = A_331
      | ~ r2_hidden(E_330,k1_tarski(A_331)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_22164])).

tff(c_22304,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_954,c_22233])).

tff(c_22333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_70,c_70,c_22304])).

tff(c_22334,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_953])).

tff(c_26,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_237,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_254,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_237])).

tff(c_257,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_254])).

tff(c_272,plain,(
    ! [D_76,B_77,A_78] :
      ( ~ r2_hidden(D_76,B_77)
      | ~ r2_hidden(D_76,k4_xboole_0(A_78,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_275,plain,(
    ! [D_76,A_11] :
      ( ~ r2_hidden(D_76,k1_xboole_0)
      | ~ r2_hidden(D_76,A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_272])).

tff(c_22338,plain,(
    ! [A_11] : ~ r2_hidden('#skF_5',A_11) ),
    inference(resolution,[status(thm)],[c_22334,c_275])).

tff(c_22340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22338,c_22334])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:13:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.39/6.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.39/6.08  
% 12.39/6.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.39/6.09  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 12.39/6.09  
% 12.39/6.09  %Foreground sorts:
% 12.39/6.09  
% 12.39/6.09  
% 12.39/6.09  %Background operators:
% 12.39/6.09  
% 12.39/6.09  
% 12.39/6.09  %Foreground operators:
% 12.39/6.09  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.39/6.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.39/6.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.39/6.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.39/6.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.39/6.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.39/6.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.39/6.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.39/6.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.39/6.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.39/6.09  tff('#skF_5', type, '#skF_5': $i).
% 12.39/6.09  tff('#skF_6', type, '#skF_6': $i).
% 12.39/6.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.39/6.09  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.39/6.09  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.39/6.09  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 12.39/6.09  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.39/6.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.39/6.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.39/6.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.39/6.09  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 12.39/6.09  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.39/6.09  
% 12.51/6.10  tff(f_81, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 12.51/6.10  tff(f_64, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 12.51/6.10  tff(f_66, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 12.51/6.10  tff(f_62, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 12.51/6.10  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 12.51/6.10  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 12.51/6.10  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 12.51/6.10  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.51/6.10  tff(c_70, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.51/6.10  tff(c_56, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.51/6.10  tff(c_219, plain, (![A_68, B_69]: (k1_enumset1(A_68, A_68, B_69)=k2_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.51/6.10  tff(c_38, plain, (![E_23, B_18, C_19]: (r2_hidden(E_23, k1_enumset1(E_23, B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.51/6.10  tff(c_267, plain, (![A_73, B_74]: (r2_hidden(A_73, k2_tarski(A_73, B_74)))), inference(superposition, [status(thm), theory('equality')], [c_219, c_38])).
% 12.51/6.10  tff(c_270, plain, (![A_24]: (r2_hidden(A_24, k1_tarski(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_267])).
% 12.51/6.10  tff(c_72, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.51/6.10  tff(c_781, plain, (![D_110, A_111, B_112]: (r2_hidden(D_110, k4_xboole_0(A_111, B_112)) | r2_hidden(D_110, B_112) | ~r2_hidden(D_110, A_111))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.51/6.10  tff(c_944, plain, (![D_121]: (r2_hidden(D_121, k1_xboole_0) | r2_hidden(D_121, k1_tarski('#skF_6')) | ~r2_hidden(D_121, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_72, c_781])).
% 12.51/6.10  tff(c_953, plain, (r2_hidden('#skF_5', k1_xboole_0) | r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_270, c_944])).
% 12.51/6.10  tff(c_954, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_953])).
% 12.51/6.10  tff(c_58, plain, (![A_25, B_26]: (k1_enumset1(A_25, A_25, B_26)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.51/6.10  tff(c_804, plain, (![E_113, C_114, B_115, A_116]: (E_113=C_114 | E_113=B_115 | E_113=A_116 | ~r2_hidden(E_113, k1_enumset1(A_116, B_115, C_114)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.51/6.10  tff(c_22164, plain, (![E_327, B_328, A_329]: (E_327=B_328 | E_327=A_329 | E_327=A_329 | ~r2_hidden(E_327, k2_tarski(A_329, B_328)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_804])).
% 12.51/6.10  tff(c_22233, plain, (![E_330, A_331]: (E_330=A_331 | E_330=A_331 | E_330=A_331 | ~r2_hidden(E_330, k1_tarski(A_331)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_22164])).
% 12.51/6.10  tff(c_22304, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_954, c_22233])).
% 12.51/6.10  tff(c_22333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_70, c_70, c_22304])).
% 12.51/6.10  tff(c_22334, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_953])).
% 12.51/6.10  tff(c_26, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.51/6.10  tff(c_24, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.51/6.10  tff(c_237, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.51/6.10  tff(c_254, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_237])).
% 12.51/6.10  tff(c_257, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_254])).
% 12.51/6.10  tff(c_272, plain, (![D_76, B_77, A_78]: (~r2_hidden(D_76, B_77) | ~r2_hidden(D_76, k4_xboole_0(A_78, B_77)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.51/6.10  tff(c_275, plain, (![D_76, A_11]: (~r2_hidden(D_76, k1_xboole_0) | ~r2_hidden(D_76, A_11))), inference(superposition, [status(thm), theory('equality')], [c_257, c_272])).
% 12.51/6.10  tff(c_22338, plain, (![A_11]: (~r2_hidden('#skF_5', A_11))), inference(resolution, [status(thm)], [c_22334, c_275])).
% 12.51/6.10  tff(c_22340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22338, c_22334])).
% 12.51/6.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.51/6.10  
% 12.51/6.10  Inference rules
% 12.51/6.10  ----------------------
% 12.51/6.10  #Ref     : 0
% 12.51/6.10  #Sup     : 5635
% 12.51/6.10  #Fact    : 0
% 12.51/6.10  #Define  : 0
% 12.51/6.10  #Split   : 1
% 12.51/6.10  #Chain   : 0
% 12.51/6.10  #Close   : 0
% 12.51/6.10  
% 12.51/6.10  Ordering : KBO
% 12.51/6.10  
% 12.51/6.10  Simplification rules
% 12.51/6.10  ----------------------
% 12.51/6.10  #Subsume      : 713
% 12.51/6.10  #Demod        : 8618
% 12.51/6.10  #Tautology    : 2447
% 12.51/6.10  #SimpNegUnit  : 2
% 12.51/6.10  #BackRed      : 1
% 12.51/6.10  
% 12.51/6.10  #Partial instantiations: 0
% 12.51/6.10  #Strategies tried      : 1
% 12.51/6.10  
% 12.51/6.10  Timing (in seconds)
% 12.51/6.10  ----------------------
% 12.51/6.10  Preprocessing        : 0.33
% 12.51/6.10  Parsing              : 0.17
% 12.51/6.10  CNF conversion       : 0.02
% 12.51/6.10  Main loop            : 5.00
% 12.51/6.10  Inferencing          : 0.70
% 12.51/6.10  Reduction            : 3.63
% 12.51/6.10  Demodulation         : 3.46
% 12.51/6.10  BG Simplification    : 0.11
% 12.51/6.10  Subsumption          : 0.43
% 12.51/6.10  Abstraction          : 0.17
% 12.51/6.10  MUC search           : 0.00
% 12.51/6.10  Cooper               : 0.00
% 12.51/6.10  Total                : 5.36
% 12.51/6.10  Index Insertion      : 0.00
% 12.51/6.10  Index Deletion       : 0.00
% 12.51/6.10  Index Matching       : 0.00
% 12.51/6.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
