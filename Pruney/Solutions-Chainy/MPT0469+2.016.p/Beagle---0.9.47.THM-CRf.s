%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:53 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 108 expanded)
%              Number of leaves         :   37 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 151 expanded)
%              Number of equality atoms :   27 (  55 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_93,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_42,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_50,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_79,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_6,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_199,plain,(
    ! [C_90,A_91] :
      ( r2_hidden(k4_tarski(C_90,'#skF_5'(A_91,k1_relat_1(A_91),C_90)),A_91)
      | ~ r2_hidden(C_90,k1_relat_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_140,plain,(
    ! [B_68,A_69] :
      ( ~ r2_hidden(B_68,A_69)
      | k4_xboole_0(A_69,k1_tarski(B_68)) != A_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_149,plain,(
    ! [B_68] : ~ r2_hidden(B_68,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_140])).

tff(c_212,plain,(
    ! [C_92] : ~ r2_hidden(C_92,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_199,c_149])).

tff(c_220,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_212])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_220])).

tff(c_226,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_58,plain,(
    ! [A_54] :
      ( v1_relat_1(A_54)
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_62,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_58])).

tff(c_227,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_42,plain,(
    ! [A_50] :
      ( v1_relat_1(k4_relat_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_46,plain,(
    ! [A_52] :
      ( k2_relat_1(k4_relat_1(A_52)) = k1_relat_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_242,plain,(
    ! [A_95] :
      ( ~ v1_xboole_0(k2_relat_1(A_95))
      | ~ v1_relat_1(A_95)
      | v1_xboole_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_328,plain,(
    ! [A_116] :
      ( ~ v1_xboole_0(k1_relat_1(A_116))
      | ~ v1_relat_1(k4_relat_1(A_116))
      | v1_xboole_0(k4_relat_1(A_116))
      | ~ v1_relat_1(A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_242])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_337,plain,(
    ! [A_117] :
      ( k4_relat_1(A_117) = k1_xboole_0
      | ~ v1_xboole_0(k1_relat_1(A_117))
      | ~ v1_relat_1(k4_relat_1(A_117))
      | ~ v1_relat_1(A_117) ) ),
    inference(resolution,[status(thm)],[c_328,c_4])).

tff(c_343,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_337])).

tff(c_345,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2,c_343])).

tff(c_346,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_345])).

tff(c_349,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_42,c_346])).

tff(c_353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_349])).

tff(c_354,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_48,plain,(
    ! [A_52] :
      ( k1_relat_1(k4_relat_1(A_52)) = k2_relat_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_363,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_48])).

tff(c_375,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_227,c_363])).

tff(c_377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_375])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.28  
% 2.24/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.29  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.24/1.29  
% 2.24/1.29  %Foreground sorts:
% 2.24/1.29  
% 2.24/1.29  
% 2.24/1.29  %Background operators:
% 2.24/1.29  
% 2.24/1.29  
% 2.24/1.29  %Foreground operators:
% 2.24/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.24/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.24/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.24/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.24/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.24/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.24/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.24/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.29  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.24/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.24/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.24/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.24/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.24/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.24/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.24/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.24/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.24/1.29  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.24/1.29  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.24/1.29  
% 2.24/1.30  tff(f_93, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.24/1.30  tff(f_38, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.24/1.30  tff(f_71, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.24/1.30  tff(f_42, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.24/1.30  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.24/1.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.24/1.30  tff(f_63, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.24/1.30  tff(f_75, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.24/1.30  tff(f_89, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 2.24/1.30  tff(f_83, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.24/1.30  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.24/1.30  tff(c_50, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.24/1.30  tff(c_79, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 2.24/1.30  tff(c_6, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.24/1.30  tff(c_199, plain, (![C_90, A_91]: (r2_hidden(k4_tarski(C_90, '#skF_5'(A_91, k1_relat_1(A_91), C_90)), A_91) | ~r2_hidden(C_90, k1_relat_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.24/1.30  tff(c_10, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.24/1.30  tff(c_140, plain, (![B_68, A_69]: (~r2_hidden(B_68, A_69) | k4_xboole_0(A_69, k1_tarski(B_68))!=A_69)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.30  tff(c_149, plain, (![B_68]: (~r2_hidden(B_68, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_140])).
% 2.24/1.30  tff(c_212, plain, (![C_92]: (~r2_hidden(C_92, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_199, c_149])).
% 2.24/1.30  tff(c_220, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_212])).
% 2.24/1.30  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_220])).
% 2.24/1.30  tff(c_226, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 2.24/1.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.24/1.30  tff(c_58, plain, (![A_54]: (v1_relat_1(A_54) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.24/1.30  tff(c_62, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_58])).
% 2.24/1.30  tff(c_227, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 2.24/1.30  tff(c_42, plain, (![A_50]: (v1_relat_1(k4_relat_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.24/1.30  tff(c_46, plain, (![A_52]: (k2_relat_1(k4_relat_1(A_52))=k1_relat_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.24/1.30  tff(c_242, plain, (![A_95]: (~v1_xboole_0(k2_relat_1(A_95)) | ~v1_relat_1(A_95) | v1_xboole_0(A_95))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.24/1.30  tff(c_328, plain, (![A_116]: (~v1_xboole_0(k1_relat_1(A_116)) | ~v1_relat_1(k4_relat_1(A_116)) | v1_xboole_0(k4_relat_1(A_116)) | ~v1_relat_1(A_116))), inference(superposition, [status(thm), theory('equality')], [c_46, c_242])).
% 2.24/1.30  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.24/1.30  tff(c_337, plain, (![A_117]: (k4_relat_1(A_117)=k1_xboole_0 | ~v1_xboole_0(k1_relat_1(A_117)) | ~v1_relat_1(k4_relat_1(A_117)) | ~v1_relat_1(A_117))), inference(resolution, [status(thm)], [c_328, c_4])).
% 2.24/1.30  tff(c_343, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_227, c_337])).
% 2.24/1.30  tff(c_345, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2, c_343])).
% 2.24/1.30  tff(c_346, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_345])).
% 2.24/1.30  tff(c_349, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_346])).
% 2.24/1.30  tff(c_353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_349])).
% 2.24/1.30  tff(c_354, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_345])).
% 2.24/1.30  tff(c_48, plain, (![A_52]: (k1_relat_1(k4_relat_1(A_52))=k2_relat_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.24/1.30  tff(c_363, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_354, c_48])).
% 2.24/1.30  tff(c_375, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_227, c_363])).
% 2.24/1.30  tff(c_377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_226, c_375])).
% 2.24/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.30  
% 2.24/1.30  Inference rules
% 2.24/1.30  ----------------------
% 2.24/1.30  #Ref     : 0
% 2.24/1.30  #Sup     : 69
% 2.24/1.30  #Fact    : 0
% 2.24/1.30  #Define  : 0
% 2.24/1.30  #Split   : 2
% 2.24/1.30  #Chain   : 0
% 2.24/1.30  #Close   : 0
% 2.24/1.30  
% 2.24/1.30  Ordering : KBO
% 2.24/1.30  
% 2.24/1.30  Simplification rules
% 2.24/1.30  ----------------------
% 2.24/1.30  #Subsume      : 2
% 2.24/1.30  #Demod        : 11
% 2.24/1.30  #Tautology    : 48
% 2.24/1.30  #SimpNegUnit  : 2
% 2.24/1.30  #BackRed      : 0
% 2.24/1.30  
% 2.24/1.30  #Partial instantiations: 0
% 2.24/1.30  #Strategies tried      : 1
% 2.24/1.30  
% 2.24/1.30  Timing (in seconds)
% 2.24/1.30  ----------------------
% 2.24/1.30  Preprocessing        : 0.32
% 2.24/1.30  Parsing              : 0.17
% 2.24/1.30  CNF conversion       : 0.02
% 2.24/1.30  Main loop            : 0.22
% 2.24/1.30  Inferencing          : 0.09
% 2.24/1.30  Reduction            : 0.06
% 2.24/1.30  Demodulation         : 0.04
% 2.24/1.30  BG Simplification    : 0.02
% 2.24/1.30  Subsumption          : 0.03
% 2.24/1.30  Abstraction          : 0.01
% 2.24/1.30  MUC search           : 0.00
% 2.24/1.30  Cooper               : 0.00
% 2.24/1.30  Total                : 0.57
% 2.24/1.30  Index Insertion      : 0.00
% 2.24/1.30  Index Deletion       : 0.00
% 2.24/1.30  Index Matching       : 0.00
% 2.24/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
