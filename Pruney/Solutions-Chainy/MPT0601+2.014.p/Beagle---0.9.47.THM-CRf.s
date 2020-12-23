%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:15 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   55 (  76 expanded)
%              Number of leaves         :   26 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 ( 120 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_56,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_40,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_42,plain,
    ( k11_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_87,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_5'))
    | k11_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_90,plain,(
    k11_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_48])).

tff(c_69,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,k1_tarski(B_31)) = A_30
      | r2_hidden(B_31,A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_xboole_0(k4_xboole_0(A_6,B_7),B_7) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_75,plain,(
    ! [A_30,B_31] :
      ( r1_xboole_0(A_30,k1_tarski(B_31))
      | r2_hidden(B_31,A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_8])).

tff(c_161,plain,(
    ! [B_53,A_54] :
      ( k9_relat_1(B_53,A_54) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_53),A_54)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_201,plain,(
    ! [B_67,B_68] :
      ( k9_relat_1(B_67,k1_tarski(B_68)) = k1_xboole_0
      | ~ v1_relat_1(B_67)
      | r2_hidden(B_68,k1_relat_1(B_67)) ) ),
    inference(resolution,[status(thm)],[c_75,c_161])).

tff(c_208,plain,
    ( k9_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_201,c_87])).

tff(c_212,plain,(
    k9_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_208])).

tff(c_34,plain,(
    ! [A_17,B_19] :
      ( k9_relat_1(A_17,k1_tarski(B_19)) = k11_relat_1(A_17,B_19)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_216,plain,
    ( k11_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_34])).

tff(c_223,plain,(
    k11_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_216])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_223])).

tff(c_226,plain,(
    k11_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_233,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_48])).

tff(c_28,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_58,plain,(
    ! [D_23,B_24] : r2_hidden(D_23,k2_tarski(D_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_61,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_58])).

tff(c_326,plain,(
    ! [B_92,A_93] :
      ( r1_xboole_0(k1_relat_1(B_92),A_93)
      | k9_relat_1(B_92,A_93) != k1_xboole_0
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2190,plain,(
    ! [C_2558,A_2559,B_2560] :
      ( ~ r2_hidden(C_2558,A_2559)
      | ~ r2_hidden(C_2558,k1_relat_1(B_2560))
      | k9_relat_1(B_2560,A_2559) != k1_xboole_0
      | ~ v1_relat_1(B_2560) ) ),
    inference(resolution,[status(thm)],[c_326,c_2])).

tff(c_2230,plain,(
    ! [A_2724,B_2725] :
      ( ~ r2_hidden(A_2724,k1_relat_1(B_2725))
      | k9_relat_1(B_2725,k1_tarski(A_2724)) != k1_xboole_0
      | ~ v1_relat_1(B_2725) ) ),
    inference(resolution,[status(thm)],[c_61,c_2190])).

tff(c_2247,plain,
    ( k9_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_233,c_2230])).

tff(c_2253,plain,(
    k9_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2247])).

tff(c_2263,plain,
    ( k11_relat_1('#skF_5','#skF_4') != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2253])).

tff(c_2266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_226,c_2263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:08:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.58  
% 3.48/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.58  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.48/1.58  
% 3.48/1.58  %Foreground sorts:
% 3.48/1.58  
% 3.48/1.58  
% 3.48/1.58  %Background operators:
% 3.48/1.58  
% 3.48/1.58  
% 3.48/1.58  %Foreground operators:
% 3.48/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.48/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.48/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.48/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.48/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.48/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.48/1.58  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.48/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.48/1.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.48/1.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.48/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.48/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.48/1.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.48/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.48/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.48/1.58  
% 3.48/1.59  tff(f_80, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.48/1.59  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.48/1.59  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.48/1.59  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 3.48/1.59  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.48/1.59  tff(f_56, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.48/1.59  tff(f_54, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.48/1.59  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.48/1.59  tff(c_40, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.48/1.59  tff(c_42, plain, (k11_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | ~r2_hidden('#skF_4', k1_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.48/1.59  tff(c_87, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_42])).
% 3.48/1.59  tff(c_48, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_5')) | k11_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.48/1.59  tff(c_90, plain, (k11_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_87, c_48])).
% 3.48/1.59  tff(c_69, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k1_tarski(B_31))=A_30 | r2_hidden(B_31, A_30))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.48/1.59  tff(c_8, plain, (![A_6, B_7]: (r1_xboole_0(k4_xboole_0(A_6, B_7), B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.48/1.59  tff(c_75, plain, (![A_30, B_31]: (r1_xboole_0(A_30, k1_tarski(B_31)) | r2_hidden(B_31, A_30))), inference(superposition, [status(thm), theory('equality')], [c_69, c_8])).
% 3.48/1.59  tff(c_161, plain, (![B_53, A_54]: (k9_relat_1(B_53, A_54)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_53), A_54) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.48/1.59  tff(c_201, plain, (![B_67, B_68]: (k9_relat_1(B_67, k1_tarski(B_68))=k1_xboole_0 | ~v1_relat_1(B_67) | r2_hidden(B_68, k1_relat_1(B_67)))), inference(resolution, [status(thm)], [c_75, c_161])).
% 3.48/1.59  tff(c_208, plain, (k9_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_201, c_87])).
% 3.48/1.59  tff(c_212, plain, (k9_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_208])).
% 3.48/1.59  tff(c_34, plain, (![A_17, B_19]: (k9_relat_1(A_17, k1_tarski(B_19))=k11_relat_1(A_17, B_19) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.48/1.59  tff(c_216, plain, (k11_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_212, c_34])).
% 3.48/1.59  tff(c_223, plain, (k11_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_216])).
% 3.48/1.59  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_223])).
% 3.48/1.59  tff(c_226, plain, (k11_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 3.48/1.59  tff(c_233, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_48])).
% 3.48/1.59  tff(c_28, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.48/1.59  tff(c_58, plain, (![D_23, B_24]: (r2_hidden(D_23, k2_tarski(D_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.48/1.59  tff(c_61, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_58])).
% 3.48/1.59  tff(c_326, plain, (![B_92, A_93]: (r1_xboole_0(k1_relat_1(B_92), A_93) | k9_relat_1(B_92, A_93)!=k1_xboole_0 | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.48/1.59  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.48/1.59  tff(c_2190, plain, (![C_2558, A_2559, B_2560]: (~r2_hidden(C_2558, A_2559) | ~r2_hidden(C_2558, k1_relat_1(B_2560)) | k9_relat_1(B_2560, A_2559)!=k1_xboole_0 | ~v1_relat_1(B_2560))), inference(resolution, [status(thm)], [c_326, c_2])).
% 3.48/1.59  tff(c_2230, plain, (![A_2724, B_2725]: (~r2_hidden(A_2724, k1_relat_1(B_2725)) | k9_relat_1(B_2725, k1_tarski(A_2724))!=k1_xboole_0 | ~v1_relat_1(B_2725))), inference(resolution, [status(thm)], [c_61, c_2190])).
% 3.48/1.59  tff(c_2247, plain, (k9_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_233, c_2230])).
% 3.48/1.59  tff(c_2253, plain, (k9_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2247])).
% 3.48/1.59  tff(c_2263, plain, (k11_relat_1('#skF_5', '#skF_4')!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_34, c_2253])).
% 3.48/1.59  tff(c_2266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_226, c_2263])).
% 3.48/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.59  
% 3.48/1.59  Inference rules
% 3.48/1.59  ----------------------
% 3.48/1.59  #Ref     : 0
% 3.48/1.59  #Sup     : 284
% 3.48/1.59  #Fact    : 4
% 3.48/1.59  #Define  : 0
% 3.48/1.59  #Split   : 1
% 3.48/1.59  #Chain   : 0
% 3.48/1.59  #Close   : 0
% 3.48/1.59  
% 3.48/1.59  Ordering : KBO
% 3.48/1.59  
% 3.48/1.59  Simplification rules
% 3.48/1.59  ----------------------
% 3.48/1.59  #Subsume      : 41
% 3.48/1.59  #Demod        : 27
% 3.48/1.59  #Tautology    : 62
% 3.48/1.59  #SimpNegUnit  : 2
% 3.48/1.59  #BackRed      : 0
% 3.48/1.59  
% 3.48/1.59  #Partial instantiations: 1764
% 3.48/1.59  #Strategies tried      : 1
% 3.48/1.59  
% 3.48/1.59  Timing (in seconds)
% 3.48/1.59  ----------------------
% 3.48/1.60  Preprocessing        : 0.31
% 3.48/1.60  Parsing              : 0.16
% 3.48/1.60  CNF conversion       : 0.02
% 3.48/1.60  Main loop            : 0.51
% 3.48/1.60  Inferencing          : 0.27
% 3.48/1.60  Reduction            : 0.10
% 3.48/1.60  Demodulation         : 0.07
% 3.48/1.60  BG Simplification    : 0.03
% 3.48/1.60  Subsumption          : 0.09
% 3.48/1.60  Abstraction          : 0.03
% 3.48/1.60  MUC search           : 0.00
% 3.48/1.60  Cooper               : 0.00
% 3.48/1.60  Total                : 0.85
% 3.48/1.60  Index Insertion      : 0.00
% 3.48/1.60  Index Deletion       : 0.00
% 3.48/1.60  Index Matching       : 0.00
% 3.48/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
