%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:03 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 217 expanded)
%              Number of leaves         :   38 (  89 expanded)
%              Depth                    :   11
%              Number of atoms          :   62 ( 335 expanded)
%              Number of equality atoms :   30 ( 193 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_47,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => r2_xboole_0(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_89,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_42,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_96,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_18,plain,(
    ! [A_8] :
      ( r2_xboole_0(k1_xboole_0,A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_101,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(A_73,B_74)
      | ~ r2_xboole_0(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_105,plain,(
    ! [A_8] :
      ( r1_tarski(k1_xboole_0,A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(resolution,[status(thm)],[c_18,c_101])).

tff(c_52,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_129,plain,(
    ! [A_83] :
      ( k7_relat_1(A_83,k1_relat_1(A_83)) = A_83
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_138,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_129])).

tff(c_158,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_46,plain,(
    ! [A_43] :
      ( r2_hidden('#skF_1'(A_43),A_43)
      | v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_159,plain,(
    ! [B_85,A_86] :
      ( ~ r2_hidden(B_85,A_86)
      | k4_xboole_0(A_86,k1_tarski(B_85)) != A_86 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_165,plain,(
    ! [B_87] : ~ r2_hidden(B_87,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_159])).

tff(c_169,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_46,c_165])).

tff(c_173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_169])).

tff(c_175,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_174,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_297,plain,(
    ! [C_108,A_109,B_110] :
      ( k7_relat_1(k7_relat_1(C_108,A_109),B_110) = k7_relat_1(C_108,A_109)
      | ~ r1_tarski(A_109,B_110)
      | ~ v1_relat_1(C_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_316,plain,(
    ! [B_110] :
      ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(k1_xboole_0,B_110)
      | ~ r1_tarski(k1_xboole_0,B_110)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_297])).

tff(c_330,plain,(
    ! [B_111] :
      ( k7_relat_1(k1_xboole_0,B_111) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_174,c_316])).

tff(c_351,plain,(
    ! [A_117] :
      ( k7_relat_1(k1_xboole_0,A_117) = k1_xboole_0
      | k1_xboole_0 = A_117 ) ),
    inference(resolution,[status(thm)],[c_105,c_330])).

tff(c_56,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_385,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_56])).

tff(c_399,plain,(
    k7_relat_1('#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_385,c_56])).

tff(c_396,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_175])).

tff(c_402,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_385,c_52])).

tff(c_54,plain,(
    ! [A_64] :
      ( k7_relat_1(A_64,k1_relat_1(A_64)) = A_64
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_421,plain,
    ( k7_relat_1('#skF_4','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_54])).

tff(c_425,plain,(
    k7_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_421])).

tff(c_427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_399,c_425])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:05:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.58  
% 2.52/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.59  %$ r2_xboole_0 > r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.52/1.59  
% 2.52/1.59  %Foreground sorts:
% 2.52/1.59  
% 2.52/1.59  
% 2.52/1.59  %Background operators:
% 2.52/1.59  
% 2.52/1.59  
% 2.52/1.59  %Foreground operators:
% 2.52/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.52/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.52/1.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.52/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.52/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.52/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.52/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.52/1.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.52/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.52/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.52/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.52/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.52/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.52/1.59  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.52/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.52/1.59  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.52/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.52/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.52/1.59  tff('#skF_4', type, '#skF_4': $i).
% 2.52/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.52/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.52/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.52/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.52/1.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.52/1.59  
% 2.52/1.60  tff(f_47, axiom, (![A]: (~(A = k1_xboole_0) => r2_xboole_0(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_xboole_1)).
% 2.52/1.60  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.52/1.60  tff(f_89, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.52/1.60  tff(f_93, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 2.52/1.60  tff(f_80, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.52/1.60  tff(f_42, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.52/1.60  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.52/1.60  tff(f_86, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 2.52/1.60  tff(f_96, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 2.52/1.60  tff(c_18, plain, (![A_8]: (r2_xboole_0(k1_xboole_0, A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.52/1.60  tff(c_101, plain, (![A_73, B_74]: (r1_tarski(A_73, B_74) | ~r2_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.52/1.60  tff(c_105, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8) | k1_xboole_0=A_8)), inference(resolution, [status(thm)], [c_18, c_101])).
% 2.52/1.60  tff(c_52, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.52/1.60  tff(c_129, plain, (![A_83]: (k7_relat_1(A_83, k1_relat_1(A_83))=A_83 | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.52/1.60  tff(c_138, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_52, c_129])).
% 2.52/1.60  tff(c_158, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_138])).
% 2.52/1.60  tff(c_46, plain, (![A_43]: (r2_hidden('#skF_1'(A_43), A_43) | v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.52/1.60  tff(c_16, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.52/1.60  tff(c_159, plain, (![B_85, A_86]: (~r2_hidden(B_85, A_86) | k4_xboole_0(A_86, k1_tarski(B_85))!=A_86)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.52/1.60  tff(c_165, plain, (![B_87]: (~r2_hidden(B_87, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_159])).
% 2.52/1.60  tff(c_169, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_165])).
% 2.52/1.60  tff(c_173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_158, c_169])).
% 2.52/1.60  tff(c_175, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_138])).
% 2.52/1.60  tff(c_174, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_138])).
% 2.52/1.60  tff(c_297, plain, (![C_108, A_109, B_110]: (k7_relat_1(k7_relat_1(C_108, A_109), B_110)=k7_relat_1(C_108, A_109) | ~r1_tarski(A_109, B_110) | ~v1_relat_1(C_108))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.52/1.60  tff(c_316, plain, (![B_110]: (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1(k1_xboole_0, B_110) | ~r1_tarski(k1_xboole_0, B_110) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_174, c_297])).
% 2.52/1.60  tff(c_330, plain, (![B_111]: (k7_relat_1(k1_xboole_0, B_111)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_111))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_174, c_316])).
% 2.52/1.60  tff(c_351, plain, (![A_117]: (k7_relat_1(k1_xboole_0, A_117)=k1_xboole_0 | k1_xboole_0=A_117)), inference(resolution, [status(thm)], [c_105, c_330])).
% 2.52/1.60  tff(c_56, plain, (k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.52/1.60  tff(c_385, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_351, c_56])).
% 2.52/1.60  tff(c_399, plain, (k7_relat_1('#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_385, c_385, c_56])).
% 2.52/1.60  tff(c_396, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_385, c_175])).
% 2.52/1.60  tff(c_402, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_385, c_385, c_52])).
% 2.52/1.60  tff(c_54, plain, (![A_64]: (k7_relat_1(A_64, k1_relat_1(A_64))=A_64 | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.52/1.60  tff(c_421, plain, (k7_relat_1('#skF_4', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_402, c_54])).
% 2.52/1.60  tff(c_425, plain, (k7_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_396, c_421])).
% 2.52/1.60  tff(c_427, plain, $false, inference(negUnitSimplification, [status(thm)], [c_399, c_425])).
% 2.52/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.60  
% 2.52/1.60  Inference rules
% 2.52/1.60  ----------------------
% 2.52/1.60  #Ref     : 0
% 2.52/1.60  #Sup     : 79
% 2.52/1.60  #Fact    : 0
% 2.52/1.60  #Define  : 0
% 2.52/1.60  #Split   : 1
% 2.52/1.60  #Chain   : 0
% 2.52/1.60  #Close   : 0
% 2.52/1.60  
% 2.52/1.60  Ordering : KBO
% 2.52/1.60  
% 2.52/1.60  Simplification rules
% 2.52/1.60  ----------------------
% 2.52/1.60  #Subsume      : 0
% 2.52/1.60  #Demod        : 40
% 2.52/1.60  #Tautology    : 63
% 2.52/1.60  #SimpNegUnit  : 4
% 2.52/1.60  #BackRed      : 12
% 2.52/1.60  
% 2.52/1.60  #Partial instantiations: 0
% 2.52/1.60  #Strategies tried      : 1
% 2.52/1.60  
% 2.52/1.60  Timing (in seconds)
% 2.52/1.60  ----------------------
% 2.52/1.60  Preprocessing        : 0.48
% 2.52/1.60  Parsing              : 0.28
% 2.52/1.60  CNF conversion       : 0.02
% 2.52/1.60  Main loop            : 0.23
% 2.52/1.60  Inferencing          : 0.09
% 2.52/1.60  Reduction            : 0.07
% 2.52/1.60  Demodulation         : 0.05
% 2.52/1.60  BG Simplification    : 0.02
% 2.52/1.60  Subsumption          : 0.03
% 2.52/1.60  Abstraction          : 0.02
% 2.52/1.60  MUC search           : 0.00
% 2.52/1.60  Cooper               : 0.00
% 2.52/1.60  Total                : 0.74
% 2.52/1.60  Index Insertion      : 0.00
% 2.52/1.60  Index Deletion       : 0.00
% 2.52/1.60  Index Matching       : 0.00
% 2.52/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
