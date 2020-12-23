%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:00 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 170 expanded)
%              Number of leaves         :   19 (  62 expanded)
%              Depth                    :    7
%              Number of atoms          :  115 ( 308 expanded)
%              Number of equality atoms :   24 (  96 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_43,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,k1_ordinal1(B))
      <=> ( r2_hidden(A,B)
          | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(c_22,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_tarski(A_12)) = k1_ordinal1(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_726,plain,(
    ! [D_603,B_604,A_605] :
      ( ~ r2_hidden(D_603,B_604)
      | r2_hidden(D_603,k2_xboole_0(A_605,B_604)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_739,plain,(
    ! [D_611,A_612] :
      ( ~ r2_hidden(D_611,k1_tarski(A_612))
      | r2_hidden(D_611,k1_ordinal1(A_612)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_726])).

tff(c_743,plain,(
    ! [C_11] : r2_hidden(C_11,k1_ordinal1(C_11)) ),
    inference(resolution,[status(thm)],[c_22,c_739])).

tff(c_656,plain,(
    ! [D_587,B_588,A_589] :
      ( ~ r2_hidden(D_587,B_588)
      | r2_hidden(D_587,k2_xboole_0(A_589,B_588)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_662,plain,(
    ! [D_590,A_591] :
      ( ~ r2_hidden(D_590,k1_tarski(A_591))
      | r2_hidden(D_590,k1_ordinal1(A_591)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_656])).

tff(c_666,plain,(
    ! [C_11] : r2_hidden(C_11,k1_ordinal1(C_11)) ),
    inference(resolution,[status(thm)],[c_22,c_662])).

tff(c_73,plain,(
    ! [D_22,B_23,A_24] :
      ( ~ r2_hidden(D_22,B_23)
      | r2_hidden(D_22,k2_xboole_0(A_24,B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_341,plain,(
    ! [D_314,A_315] :
      ( ~ r2_hidden(D_314,k1_tarski(A_315))
      | r2_hidden(D_314,k1_ordinal1(A_315)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_73])).

tff(c_345,plain,(
    ! [C_11] : r2_hidden(C_11,k1_ordinal1(C_11)) ),
    inference(resolution,[status(thm)],[c_22,c_341])).

tff(c_38,plain,
    ( ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_62,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,
    ( ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_46,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_64,plain,(
    ! [D_17,A_18,B_19] :
      ( ~ r2_hidden(D_17,A_18)
      | r2_hidden(D_17,k2_xboole_0(A_18,B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_68,plain,(
    ! [D_20,A_21] :
      ( ~ r2_hidden(D_20,A_21)
      | r2_hidden(D_20,k1_ordinal1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_64])).

tff(c_42,plain,
    ( ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_63,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_72,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_63])).

tff(c_44,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_77,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_44])).

tff(c_78,plain,(
    r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_85,plain,(
    ! [D_28,B_29,A_30] :
      ( r2_hidden(D_28,B_29)
      | r2_hidden(D_28,A_30)
      | ~ r2_hidden(D_28,k2_xboole_0(A_30,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_264,plain,(
    ! [D_282,A_283] :
      ( r2_hidden(D_282,k1_tarski(A_283))
      | r2_hidden(D_282,A_283)
      | ~ r2_hidden(D_282,k1_ordinal1(A_283)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_85])).

tff(c_20,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_308,plain,(
    ! [D_298,A_299] :
      ( D_298 = A_299
      | r2_hidden(D_298,A_299)
      | ~ r2_hidden(D_298,k1_ordinal1(A_299)) ) ),
    inference(resolution,[status(thm)],[c_264,c_20])).

tff(c_315,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_78,c_308])).

tff(c_324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_46,c_315])).

tff(c_325,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_328,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_63])).

tff(c_348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_328])).

tff(c_349,plain,(
    r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_351,plain,(
    r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_368,plain,(
    ! [D_327,B_328,A_329] :
      ( r2_hidden(D_327,B_328)
      | r2_hidden(D_327,A_329)
      | ~ r2_hidden(D_327,k2_xboole_0(A_329,B_328)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_547,plain,(
    ! [D_542,A_543] :
      ( r2_hidden(D_542,k1_tarski(A_543))
      | r2_hidden(D_542,A_543)
      | ~ r2_hidden(D_542,k1_ordinal1(A_543)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_368])).

tff(c_591,plain,(
    ! [D_558,A_559] :
      ( D_558 = A_559
      | r2_hidden(D_558,A_559)
      | ~ r2_hidden(D_558,k1_ordinal1(A_559)) ) ),
    inference(resolution,[status(thm)],[c_547,c_20])).

tff(c_604,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_351,c_591])).

tff(c_612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_46,c_604])).

tff(c_614,plain,(
    ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_616,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_614])).

tff(c_618,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_40,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_620,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_40])).

tff(c_621,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_620])).

tff(c_627,plain,(
    ! [D_577,A_578,B_579] :
      ( ~ r2_hidden(D_577,A_578)
      | r2_hidden(D_577,k2_xboole_0(A_578,B_579)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_631,plain,(
    ! [D_580,A_581] :
      ( ~ r2_hidden(D_580,A_581)
      | r2_hidden(D_580,k1_ordinal1(A_581)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_627])).

tff(c_617,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_634,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_631,c_617])).

tff(c_638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_634])).

tff(c_639,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_620])).

tff(c_641,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_617])).

tff(c_669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_641])).

tff(c_671,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6')
    | '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_693,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_671,c_36])).

tff(c_694,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_693])).

tff(c_701,plain,(
    ! [D_598,A_599,B_600] :
      ( ~ r2_hidden(D_598,A_599)
      | r2_hidden(D_598,k2_xboole_0(A_599,B_600)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_705,plain,(
    ! [D_601,A_602] :
      ( ~ r2_hidden(D_601,A_602)
      | r2_hidden(D_601,k1_ordinal1(A_602)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_701])).

tff(c_670,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_708,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_705,c_670])).

tff(c_712,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_694,c_708])).

tff(c_713,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_693])).

tff(c_715,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_670])).

tff(c_746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_715])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.38  
% 2.50/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.38  %$ r2_hidden > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4
% 2.50/1.38  
% 2.50/1.38  %Foreground sorts:
% 2.50/1.38  
% 2.50/1.38  
% 2.50/1.38  %Background operators:
% 2.50/1.38  
% 2.50/1.38  
% 2.50/1.38  %Foreground operators:
% 2.50/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.50/1.38  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.50/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.50/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.50/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.50/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.50/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.50/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.50/1.38  tff('#skF_8', type, '#skF_8': $i).
% 2.50/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.50/1.38  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.50/1.38  
% 2.50/1.39  tff(f_41, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.50/1.39  tff(f_43, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.50/1.39  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.50/1.39  tff(f_50, negated_conjecture, ~(![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 2.50/1.39  tff(c_22, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.50/1.39  tff(c_32, plain, (![A_12]: (k2_xboole_0(A_12, k1_tarski(A_12))=k1_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.50/1.39  tff(c_726, plain, (![D_603, B_604, A_605]: (~r2_hidden(D_603, B_604) | r2_hidden(D_603, k2_xboole_0(A_605, B_604)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.50/1.39  tff(c_739, plain, (![D_611, A_612]: (~r2_hidden(D_611, k1_tarski(A_612)) | r2_hidden(D_611, k1_ordinal1(A_612)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_726])).
% 2.50/1.39  tff(c_743, plain, (![C_11]: (r2_hidden(C_11, k1_ordinal1(C_11)))), inference(resolution, [status(thm)], [c_22, c_739])).
% 2.50/1.39  tff(c_656, plain, (![D_587, B_588, A_589]: (~r2_hidden(D_587, B_588) | r2_hidden(D_587, k2_xboole_0(A_589, B_588)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.50/1.39  tff(c_662, plain, (![D_590, A_591]: (~r2_hidden(D_590, k1_tarski(A_591)) | r2_hidden(D_590, k1_ordinal1(A_591)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_656])).
% 2.50/1.39  tff(c_666, plain, (![C_11]: (r2_hidden(C_11, k1_ordinal1(C_11)))), inference(resolution, [status(thm)], [c_22, c_662])).
% 2.50/1.39  tff(c_73, plain, (![D_22, B_23, A_24]: (~r2_hidden(D_22, B_23) | r2_hidden(D_22, k2_xboole_0(A_24, B_23)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.50/1.40  tff(c_341, plain, (![D_314, A_315]: (~r2_hidden(D_314, k1_tarski(A_315)) | r2_hidden(D_314, k1_ordinal1(A_315)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_73])).
% 2.50/1.40  tff(c_345, plain, (![C_11]: (r2_hidden(C_11, k1_ordinal1(C_11)))), inference(resolution, [status(thm)], [c_22, c_341])).
% 2.50/1.40  tff(c_38, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6')) | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.50/1.40  tff(c_62, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_38])).
% 2.50/1.40  tff(c_34, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6')) | '#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.50/1.40  tff(c_46, plain, ('#skF_7'!='#skF_8'), inference(splitLeft, [status(thm)], [c_34])).
% 2.50/1.40  tff(c_64, plain, (![D_17, A_18, B_19]: (~r2_hidden(D_17, A_18) | r2_hidden(D_17, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.50/1.40  tff(c_68, plain, (![D_20, A_21]: (~r2_hidden(D_20, A_21) | r2_hidden(D_20, k1_ordinal1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_64])).
% 2.50/1.40  tff(c_42, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6')) | r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.50/1.40  tff(c_63, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitLeft, [status(thm)], [c_42])).
% 2.50/1.40  tff(c_72, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_68, c_63])).
% 2.50/1.40  tff(c_44, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.50/1.40  tff(c_77, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_72, c_44])).
% 2.50/1.40  tff(c_78, plain, (r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(splitLeft, [status(thm)], [c_77])).
% 2.50/1.40  tff(c_85, plain, (![D_28, B_29, A_30]: (r2_hidden(D_28, B_29) | r2_hidden(D_28, A_30) | ~r2_hidden(D_28, k2_xboole_0(A_30, B_29)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.50/1.40  tff(c_264, plain, (![D_282, A_283]: (r2_hidden(D_282, k1_tarski(A_283)) | r2_hidden(D_282, A_283) | ~r2_hidden(D_282, k1_ordinal1(A_283)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_85])).
% 2.50/1.40  tff(c_20, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.50/1.40  tff(c_308, plain, (![D_298, A_299]: (D_298=A_299 | r2_hidden(D_298, A_299) | ~r2_hidden(D_298, k1_ordinal1(A_299)))), inference(resolution, [status(thm)], [c_264, c_20])).
% 2.50/1.40  tff(c_315, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_78, c_308])).
% 2.50/1.40  tff(c_324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_46, c_315])).
% 2.50/1.40  tff(c_325, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_77])).
% 2.50/1.40  tff(c_328, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_325, c_63])).
% 2.50/1.40  tff(c_348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_345, c_328])).
% 2.50/1.40  tff(c_349, plain, (r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(splitRight, [status(thm)], [c_42])).
% 2.50/1.40  tff(c_351, plain, (r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(splitLeft, [status(thm)], [c_44])).
% 2.50/1.40  tff(c_368, plain, (![D_327, B_328, A_329]: (r2_hidden(D_327, B_328) | r2_hidden(D_327, A_329) | ~r2_hidden(D_327, k2_xboole_0(A_329, B_328)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.50/1.40  tff(c_547, plain, (![D_542, A_543]: (r2_hidden(D_542, k1_tarski(A_543)) | r2_hidden(D_542, A_543) | ~r2_hidden(D_542, k1_ordinal1(A_543)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_368])).
% 2.50/1.40  tff(c_591, plain, (![D_558, A_559]: (D_558=A_559 | r2_hidden(D_558, A_559) | ~r2_hidden(D_558, k1_ordinal1(A_559)))), inference(resolution, [status(thm)], [c_547, c_20])).
% 2.50/1.40  tff(c_604, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_351, c_591])).
% 2.50/1.40  tff(c_612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_46, c_604])).
% 2.50/1.40  tff(c_614, plain, (~r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(splitRight, [status(thm)], [c_44])).
% 2.50/1.40  tff(c_616, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_349, c_614])).
% 2.50/1.40  tff(c_618, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_38])).
% 2.50/1.40  tff(c_40, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.50/1.40  tff(c_620, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_618, c_40])).
% 2.50/1.40  tff(c_621, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_620])).
% 2.50/1.40  tff(c_627, plain, (![D_577, A_578, B_579]: (~r2_hidden(D_577, A_578) | r2_hidden(D_577, k2_xboole_0(A_578, B_579)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.50/1.40  tff(c_631, plain, (![D_580, A_581]: (~r2_hidden(D_580, A_581) | r2_hidden(D_580, k1_ordinal1(A_581)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_627])).
% 2.50/1.40  tff(c_617, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitRight, [status(thm)], [c_38])).
% 2.50/1.40  tff(c_634, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_631, c_617])).
% 2.50/1.40  tff(c_638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_621, c_634])).
% 2.50/1.40  tff(c_639, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_620])).
% 2.50/1.40  tff(c_641, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_639, c_617])).
% 2.50/1.40  tff(c_669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_666, c_641])).
% 2.50/1.40  tff(c_671, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_34])).
% 2.50/1.40  tff(c_36, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6') | '#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.50/1.40  tff(c_693, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_671, c_36])).
% 2.50/1.40  tff(c_694, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_693])).
% 2.50/1.40  tff(c_701, plain, (![D_598, A_599, B_600]: (~r2_hidden(D_598, A_599) | r2_hidden(D_598, k2_xboole_0(A_599, B_600)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.50/1.40  tff(c_705, plain, (![D_601, A_602]: (~r2_hidden(D_601, A_602) | r2_hidden(D_601, k1_ordinal1(A_602)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_701])).
% 2.50/1.40  tff(c_670, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitRight, [status(thm)], [c_34])).
% 2.50/1.40  tff(c_708, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_705, c_670])).
% 2.50/1.40  tff(c_712, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_694, c_708])).
% 2.50/1.40  tff(c_713, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_693])).
% 2.50/1.40  tff(c_715, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_713, c_670])).
% 2.50/1.40  tff(c_746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_743, c_715])).
% 2.50/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.40  
% 2.50/1.40  Inference rules
% 2.50/1.40  ----------------------
% 2.50/1.40  #Ref     : 0
% 2.50/1.40  #Sup     : 103
% 2.50/1.40  #Fact    : 0
% 2.50/1.40  #Define  : 0
% 2.50/1.40  #Split   : 7
% 2.50/1.40  #Chain   : 0
% 2.50/1.40  #Close   : 0
% 2.50/1.40  
% 2.50/1.40  Ordering : KBO
% 2.50/1.40  
% 2.50/1.40  Simplification rules
% 2.50/1.40  ----------------------
% 2.50/1.40  #Subsume      : 10
% 2.50/1.40  #Demod        : 30
% 2.50/1.40  #Tautology    : 33
% 2.50/1.40  #SimpNegUnit  : 6
% 2.50/1.40  #BackRed      : 7
% 2.50/1.40  
% 2.50/1.40  #Partial instantiations: 385
% 2.50/1.40  #Strategies tried      : 1
% 2.50/1.40  
% 2.50/1.40  Timing (in seconds)
% 2.50/1.40  ----------------------
% 2.50/1.40  Preprocessing        : 0.28
% 2.50/1.40  Parsing              : 0.13
% 2.50/1.40  CNF conversion       : 0.02
% 2.50/1.40  Main loop            : 0.31
% 2.50/1.40  Inferencing          : 0.15
% 2.50/1.40  Reduction            : 0.07
% 2.50/1.40  Demodulation         : 0.05
% 2.50/1.40  BG Simplification    : 0.02
% 2.50/1.40  Subsumption          : 0.05
% 2.50/1.40  Abstraction          : 0.01
% 2.50/1.40  MUC search           : 0.00
% 2.50/1.40  Cooper               : 0.00
% 2.50/1.40  Total                : 0.63
% 2.50/1.40  Index Insertion      : 0.00
% 2.50/1.40  Index Deletion       : 0.00
% 2.50/1.40  Index Matching       : 0.00
% 2.50/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
