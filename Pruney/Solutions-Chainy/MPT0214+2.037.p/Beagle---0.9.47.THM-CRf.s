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
% DateTime   : Thu Dec  3 09:47:34 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   55 (  79 expanded)
%              Number of leaves         :   29 (  41 expanded)
%              Depth                    :    6
%              Number of atoms          :   60 ( 101 expanded)
%              Number of equality atoms :   32 (  59 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_64,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_56,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_75,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(A_61,B_62) = k1_xboole_0
      | ~ r1_xboole_0(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_83,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_75])).

tff(c_114,plain,(
    ! [A_69,B_70,C_71] :
      ( ~ r1_xboole_0(A_69,B_70)
      | ~ r2_hidden(C_71,k3_xboole_0(A_69,B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_117,plain,(
    ! [A_8,C_71] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_71,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_114])).

tff(c_119,plain,(
    ! [C_71] : ~ r2_hidden(C_71,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_117])).

tff(c_58,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_136,plain,(
    ! [B_78,A_79] :
      ( k1_tarski(B_78) = A_79
      | k1_xboole_0 = A_79
      | ~ r1_tarski(A_79,k1_tarski(B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_148,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_4')
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_136])).

tff(c_151,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_36,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_91,plain,(
    ! [A_64,B_65] : k1_enumset1(A_64,A_64,B_65) = k2_tarski(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    ! [E_15,B_10,C_11] : r2_hidden(E_15,k1_enumset1(E_15,B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_109,plain,(
    ! [A_66,B_67] : r2_hidden(A_66,k2_tarski(A_66,B_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_18])).

tff(c_112,plain,(
    ! [A_16] : r2_hidden(A_16,k1_tarski(A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_109])).

tff(c_160,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_112])).

tff(c_173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_160])).

tff(c_174,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_184,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_112])).

tff(c_38,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_219,plain,(
    ! [E_86,C_87,B_88,A_89] :
      ( E_86 = C_87
      | E_86 = B_88
      | E_86 = A_89
      | ~ r2_hidden(E_86,k1_enumset1(A_89,B_88,C_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_247,plain,(
    ! [E_95,B_96,A_97] :
      ( E_95 = B_96
      | E_95 = A_97
      | E_95 = A_97
      | ~ r2_hidden(E_95,k2_tarski(A_97,B_96)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_219])).

tff(c_261,plain,(
    ! [E_98,A_99] :
      ( E_98 = A_99
      | E_98 = A_99
      | E_98 = A_99
      | ~ r2_hidden(E_98,k1_tarski(A_99)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_247])).

tff(c_264,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_184,c_261])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_56,c_264])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.25  
% 2.15/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.15/1.25  
% 2.15/1.25  %Foreground sorts:
% 2.15/1.25  
% 2.15/1.25  
% 2.15/1.25  %Background operators:
% 2.15/1.25  
% 2.15/1.25  
% 2.15/1.25  %Foreground operators:
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.15/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.15/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.15/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.15/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.15/1.25  
% 2.15/1.26  tff(f_85, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.15/1.26  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.15/1.26  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.15/1.26  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.15/1.26  tff(f_80, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.15/1.26  tff(f_62, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.15/1.26  tff(f_64, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.15/1.26  tff(f_60, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.15/1.26  tff(c_56, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.15/1.26  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.15/1.26  tff(c_75, plain, (![A_61, B_62]: (k3_xboole_0(A_61, B_62)=k1_xboole_0 | ~r1_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.15/1.26  tff(c_83, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_75])).
% 2.15/1.26  tff(c_114, plain, (![A_69, B_70, C_71]: (~r1_xboole_0(A_69, B_70) | ~r2_hidden(C_71, k3_xboole_0(A_69, B_70)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.15/1.26  tff(c_117, plain, (![A_8, C_71]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_71, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_83, c_114])).
% 2.15/1.26  tff(c_119, plain, (![C_71]: (~r2_hidden(C_71, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_117])).
% 2.15/1.26  tff(c_58, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.15/1.26  tff(c_136, plain, (![B_78, A_79]: (k1_tarski(B_78)=A_79 | k1_xboole_0=A_79 | ~r1_tarski(A_79, k1_tarski(B_78)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.15/1.26  tff(c_148, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4') | k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_136])).
% 2.15/1.26  tff(c_151, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_148])).
% 2.15/1.26  tff(c_36, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.15/1.26  tff(c_91, plain, (![A_64, B_65]: (k1_enumset1(A_64, A_64, B_65)=k2_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.15/1.26  tff(c_18, plain, (![E_15, B_10, C_11]: (r2_hidden(E_15, k1_enumset1(E_15, B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.15/1.26  tff(c_109, plain, (![A_66, B_67]: (r2_hidden(A_66, k2_tarski(A_66, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_91, c_18])).
% 2.15/1.26  tff(c_112, plain, (![A_16]: (r2_hidden(A_16, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_109])).
% 2.15/1.26  tff(c_160, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_151, c_112])).
% 2.15/1.26  tff(c_173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_160])).
% 2.15/1.26  tff(c_174, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_148])).
% 2.15/1.26  tff(c_184, plain, (r2_hidden('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_174, c_112])).
% 2.15/1.26  tff(c_38, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.15/1.26  tff(c_219, plain, (![E_86, C_87, B_88, A_89]: (E_86=C_87 | E_86=B_88 | E_86=A_89 | ~r2_hidden(E_86, k1_enumset1(A_89, B_88, C_87)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.15/1.26  tff(c_247, plain, (![E_95, B_96, A_97]: (E_95=B_96 | E_95=A_97 | E_95=A_97 | ~r2_hidden(E_95, k2_tarski(A_97, B_96)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_219])).
% 2.15/1.26  tff(c_261, plain, (![E_98, A_99]: (E_98=A_99 | E_98=A_99 | E_98=A_99 | ~r2_hidden(E_98, k1_tarski(A_99)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_247])).
% 2.15/1.26  tff(c_264, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_184, c_261])).
% 2.15/1.26  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_56, c_264])).
% 2.15/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.26  
% 2.15/1.26  Inference rules
% 2.15/1.26  ----------------------
% 2.15/1.26  #Ref     : 0
% 2.15/1.26  #Sup     : 49
% 2.15/1.26  #Fact    : 0
% 2.15/1.26  #Define  : 0
% 2.15/1.26  #Split   : 1
% 2.15/1.26  #Chain   : 0
% 2.15/1.26  #Close   : 0
% 2.15/1.26  
% 2.15/1.26  Ordering : KBO
% 2.15/1.26  
% 2.15/1.26  Simplification rules
% 2.15/1.26  ----------------------
% 2.15/1.26  #Subsume      : 1
% 2.15/1.26  #Demod        : 15
% 2.15/1.26  #Tautology    : 32
% 2.15/1.26  #SimpNegUnit  : 3
% 2.15/1.26  #BackRed      : 2
% 2.15/1.26  
% 2.15/1.26  #Partial instantiations: 0
% 2.15/1.26  #Strategies tried      : 1
% 2.15/1.26  
% 2.15/1.26  Timing (in seconds)
% 2.15/1.26  ----------------------
% 2.15/1.26  Preprocessing        : 0.32
% 2.15/1.26  Parsing              : 0.17
% 2.15/1.26  CNF conversion       : 0.02
% 2.15/1.26  Main loop            : 0.18
% 2.15/1.26  Inferencing          : 0.06
% 2.15/1.26  Reduction            : 0.06
% 2.15/1.26  Demodulation         : 0.04
% 2.15/1.26  BG Simplification    : 0.02
% 2.15/1.26  Subsumption          : 0.03
% 2.15/1.26  Abstraction          : 0.01
% 2.15/1.26  MUC search           : 0.00
% 2.15/1.26  Cooper               : 0.00
% 2.15/1.26  Total                : 0.53
% 2.15/1.26  Index Insertion      : 0.00
% 2.15/1.26  Index Deletion       : 0.00
% 2.15/1.26  Index Matching       : 0.00
% 2.15/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
