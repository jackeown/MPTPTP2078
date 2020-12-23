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
% DateTime   : Thu Dec  3 09:48:39 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   54 (  57 expanded)
%              Number of leaves         :   31 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   47 (  54 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_50,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_48,plain,(
    ! [A_43,B_44] :
      ( r1_xboole_0(k1_tarski(A_43),B_44)
      | r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    ! [C_25] : r2_hidden(C_25,k1_tarski(C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_87,plain,(
    ! [B_49,A_50] :
      ( ~ r2_hidden(B_49,A_50)
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [C_25] : ~ v1_xboole_0(k1_tarski(C_25)) ),
    inference(resolution,[status(thm)],[c_26,c_87])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_198,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k3_xboole_0(A_65,B_66)) = k4_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_207,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = k4_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_198])).

tff(c_210,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_207])).

tff(c_52,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_286,plain,(
    ! [A_73,B_74] : k4_xboole_0(A_73,k4_xboole_0(A_73,B_74)) = k3_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_307,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k4_xboole_0(k1_tarski('#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_286])).

tff(c_311,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_307])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_223,plain,(
    ! [A_68,B_69,C_70] :
      ( ~ r1_xboole_0(A_68,B_69)
      | ~ r2_hidden(C_70,k3_xboole_0(A_68,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_393,plain,(
    ! [A_80,B_81] :
      ( ~ r1_xboole_0(A_80,B_81)
      | v1_xboole_0(k3_xboole_0(A_80,B_81)) ) ),
    inference(resolution,[status(thm)],[c_4,c_223])).

tff(c_396,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6'))
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_393])).

tff(c_403,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_396])).

tff(c_417,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_48,c_403])).

tff(c_24,plain,(
    ! [C_25,A_21] :
      ( C_25 = A_21
      | ~ r2_hidden(C_25,k1_tarski(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_420,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_417,c_24])).

tff(c_427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_420])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:59:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.42  
% 2.25/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.43  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 2.25/1.43  
% 2.25/1.43  %Foreground sorts:
% 2.25/1.43  
% 2.25/1.43  
% 2.25/1.43  %Background operators:
% 2.25/1.43  
% 2.25/1.43  
% 2.25/1.43  %Foreground operators:
% 2.25/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.25/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.25/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.25/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.25/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.25/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.25/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.25/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.25/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.25/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.25/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.25/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.25/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.25/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.25/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.25/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.25/1.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.25/1.43  
% 2.25/1.44  tff(f_88, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.25/1.44  tff(f_83, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.25/1.44  tff(f_66, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.25/1.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.25/1.44  tff(f_53, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.25/1.44  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.25/1.44  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.25/1.44  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.25/1.44  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.25/1.44  tff(c_50, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.25/1.44  tff(c_48, plain, (![A_43, B_44]: (r1_xboole_0(k1_tarski(A_43), B_44) | r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.25/1.44  tff(c_26, plain, (![C_25]: (r2_hidden(C_25, k1_tarski(C_25)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.25/1.44  tff(c_87, plain, (![B_49, A_50]: (~r2_hidden(B_49, A_50) | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.25/1.44  tff(c_91, plain, (![C_25]: (~v1_xboole_0(k1_tarski(C_25)))), inference(resolution, [status(thm)], [c_26, c_87])).
% 2.25/1.44  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.25/1.44  tff(c_12, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.25/1.44  tff(c_198, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k3_xboole_0(A_65, B_66))=k4_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.25/1.44  tff(c_207, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=k4_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_198])).
% 2.25/1.44  tff(c_210, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_207])).
% 2.25/1.44  tff(c_52, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.25/1.44  tff(c_286, plain, (![A_73, B_74]: (k4_xboole_0(A_73, k4_xboole_0(A_73, B_74))=k3_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.25/1.44  tff(c_307, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k4_xboole_0(k1_tarski('#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_52, c_286])).
% 2.25/1.44  tff(c_311, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_307])).
% 2.25/1.44  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.25/1.44  tff(c_223, plain, (![A_68, B_69, C_70]: (~r1_xboole_0(A_68, B_69) | ~r2_hidden(C_70, k3_xboole_0(A_68, B_69)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.25/1.44  tff(c_393, plain, (![A_80, B_81]: (~r1_xboole_0(A_80, B_81) | v1_xboole_0(k3_xboole_0(A_80, B_81)))), inference(resolution, [status(thm)], [c_4, c_223])).
% 2.25/1.44  tff(c_396, plain, (~r1_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6')) | v1_xboole_0(k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_311, c_393])).
% 2.25/1.44  tff(c_403, plain, (~r1_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_91, c_396])).
% 2.25/1.44  tff(c_417, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_403])).
% 2.25/1.44  tff(c_24, plain, (![C_25, A_21]: (C_25=A_21 | ~r2_hidden(C_25, k1_tarski(A_21)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.25/1.44  tff(c_420, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_417, c_24])).
% 2.25/1.44  tff(c_427, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_420])).
% 2.25/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.44  
% 2.25/1.44  Inference rules
% 2.25/1.44  ----------------------
% 2.25/1.44  #Ref     : 0
% 2.25/1.44  #Sup     : 89
% 2.25/1.44  #Fact    : 0
% 2.25/1.44  #Define  : 0
% 2.25/1.44  #Split   : 1
% 2.25/1.44  #Chain   : 0
% 2.25/1.44  #Close   : 0
% 2.25/1.44  
% 2.25/1.44  Ordering : KBO
% 2.25/1.44  
% 2.25/1.44  Simplification rules
% 2.25/1.44  ----------------------
% 2.25/1.44  #Subsume      : 0
% 2.25/1.44  #Demod        : 19
% 2.25/1.44  #Tautology    : 65
% 2.25/1.44  #SimpNegUnit  : 4
% 2.25/1.44  #BackRed      : 0
% 2.25/1.44  
% 2.25/1.44  #Partial instantiations: 0
% 2.25/1.44  #Strategies tried      : 1
% 2.25/1.44  
% 2.25/1.44  Timing (in seconds)
% 2.25/1.44  ----------------------
% 2.25/1.44  Preprocessing        : 0.46
% 2.25/1.44  Parsing              : 0.27
% 2.25/1.44  CNF conversion       : 0.02
% 2.25/1.44  Main loop            : 0.20
% 2.25/1.44  Inferencing          : 0.07
% 2.25/1.44  Reduction            : 0.07
% 2.25/1.44  Demodulation         : 0.05
% 2.25/1.44  BG Simplification    : 0.01
% 2.25/1.44  Subsumption          : 0.03
% 2.25/1.44  Abstraction          : 0.01
% 2.25/1.44  MUC search           : 0.00
% 2.25/1.44  Cooper               : 0.00
% 2.25/1.44  Total                : 0.69
% 2.25/1.44  Index Insertion      : 0.00
% 2.25/1.45  Index Deletion       : 0.00
% 2.25/1.45  Index Matching       : 0.00
% 2.25/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
