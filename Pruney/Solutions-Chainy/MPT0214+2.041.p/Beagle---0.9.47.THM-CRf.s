%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:35 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 116 expanded)
%              Number of leaves         :   31 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 153 expanded)
%              Number of equality atoms :   41 (  95 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_42,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_38,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_66,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_68,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_155,plain,(
    ! [B_73,A_74] :
      ( k1_tarski(B_73) = A_74
      | k1_xboole_0 = A_74
      | ~ r1_tarski(A_74,k1_tarski(B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_172,plain,
    ( k1_tarski('#skF_3') = k1_tarski('#skF_4')
    | k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_155])).

tff(c_261,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_46,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_114,plain,(
    ! [A_64,B_65] : k1_enumset1(A_64,A_64,B_65) = k2_tarski(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    ! [E_16,A_10,C_12] : r2_hidden(E_16,k1_enumset1(A_10,E_16,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_132,plain,(
    ! [A_66,B_67] : r2_hidden(A_66,k2_tarski(A_66,B_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_26])).

tff(c_135,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_132])).

tff(c_270,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_135])).

tff(c_81,plain,(
    ! [A_51,B_52] : r1_tarski(k3_xboole_0(A_51,B_52),A_51) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_20,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_86,plain,(
    ! [B_52] : k3_xboole_0(k1_xboole_0,B_52) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_81,c_20])).

tff(c_136,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = k4_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_175,plain,(
    ! [B_75] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_136])).

tff(c_145,plain,(
    ! [B_52] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_136])).

tff(c_184,plain,(
    ! [B_77,B_76] : k4_xboole_0(k1_xboole_0,B_77) = k4_xboole_0(k1_xboole_0,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_145])).

tff(c_18,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_200,plain,(
    ! [B_77] : k4_xboole_0(k1_xboole_0,B_77) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_18])).

tff(c_226,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_145])).

tff(c_295,plain,(
    ! [A_86,C_87,B_88] :
      ( ~ r2_hidden(A_86,C_87)
      | ~ r2_hidden(A_86,B_88)
      | ~ r2_hidden(A_86,k5_xboole_0(B_88,C_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_302,plain,(
    ! [A_89] :
      ( ~ r2_hidden(A_89,k1_xboole_0)
      | ~ r2_hidden(A_89,k1_xboole_0)
      | ~ r2_hidden(A_89,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_295])).

tff(c_304,plain,(
    ~ r2_hidden('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_270,c_302])).

tff(c_308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_304])).

tff(c_309,plain,(
    k1_tarski('#skF_3') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_327,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_135])).

tff(c_48,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_390,plain,(
    ! [E_107,C_108,B_109,A_110] :
      ( E_107 = C_108
      | E_107 = B_109
      | E_107 = A_110
      | ~ r2_hidden(E_107,k1_enumset1(A_110,B_109,C_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_459,plain,(
    ! [E_115,B_116,A_117] :
      ( E_115 = B_116
      | E_115 = A_117
      | E_115 = A_117
      | ~ r2_hidden(E_115,k2_tarski(A_117,B_116)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_390])).

tff(c_482,plain,(
    ! [E_123,A_124] :
      ( E_123 = A_124
      | E_123 = A_124
      | E_123 = A_124
      | ~ r2_hidden(E_123,k1_tarski(A_124)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_459])).

tff(c_485,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_327,c_482])).

tff(c_495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_66,c_66,c_485])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.30  % Computer   : n014.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 16:12:22 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.31  
% 2.50/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.32  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.50/1.32  
% 2.50/1.32  %Foreground sorts:
% 2.50/1.32  
% 2.50/1.32  
% 2.50/1.32  %Background operators:
% 2.50/1.32  
% 2.50/1.32  
% 2.50/1.32  %Foreground operators:
% 2.50/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.50/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.50/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.50/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.50/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.50/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.50/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.50/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.50/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.50/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.50/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.50/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.50/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.50/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.50/1.32  
% 2.50/1.33  tff(f_82, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.50/1.33  tff(f_77, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.50/1.33  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.50/1.33  tff(f_61, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.50/1.33  tff(f_57, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.50/1.33  tff(f_36, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.50/1.33  tff(f_42, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.50/1.33  tff(f_34, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.50/1.33  tff(f_38, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.50/1.33  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.50/1.33  tff(c_66, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.50/1.33  tff(c_68, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.50/1.33  tff(c_155, plain, (![B_73, A_74]: (k1_tarski(B_73)=A_74 | k1_xboole_0=A_74 | ~r1_tarski(A_74, k1_tarski(B_73)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.50/1.33  tff(c_172, plain, (k1_tarski('#skF_3')=k1_tarski('#skF_4') | k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_155])).
% 2.50/1.33  tff(c_261, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_172])).
% 2.50/1.33  tff(c_46, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.50/1.33  tff(c_114, plain, (![A_64, B_65]: (k1_enumset1(A_64, A_64, B_65)=k2_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.50/1.33  tff(c_26, plain, (![E_16, A_10, C_12]: (r2_hidden(E_16, k1_enumset1(A_10, E_16, C_12)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.50/1.33  tff(c_132, plain, (![A_66, B_67]: (r2_hidden(A_66, k2_tarski(A_66, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_26])).
% 2.50/1.33  tff(c_135, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_132])).
% 2.50/1.33  tff(c_270, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_261, c_135])).
% 2.50/1.33  tff(c_81, plain, (![A_51, B_52]: (r1_tarski(k3_xboole_0(A_51, B_52), A_51))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.50/1.33  tff(c_20, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.50/1.33  tff(c_86, plain, (![B_52]: (k3_xboole_0(k1_xboole_0, B_52)=k1_xboole_0)), inference(resolution, [status(thm)], [c_81, c_20])).
% 2.50/1.33  tff(c_136, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k3_xboole_0(A_68, B_69))=k4_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.50/1.33  tff(c_175, plain, (![B_75]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_75))), inference(superposition, [status(thm), theory('equality')], [c_86, c_136])).
% 2.50/1.33  tff(c_145, plain, (![B_52]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_52))), inference(superposition, [status(thm), theory('equality')], [c_86, c_136])).
% 2.50/1.33  tff(c_184, plain, (![B_77, B_76]: (k4_xboole_0(k1_xboole_0, B_77)=k4_xboole_0(k1_xboole_0, B_76))), inference(superposition, [status(thm), theory('equality')], [c_175, c_145])).
% 2.50/1.33  tff(c_18, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.50/1.33  tff(c_200, plain, (![B_77]: (k4_xboole_0(k1_xboole_0, B_77)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_184, c_18])).
% 2.50/1.33  tff(c_226, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_200, c_145])).
% 2.50/1.33  tff(c_295, plain, (![A_86, C_87, B_88]: (~r2_hidden(A_86, C_87) | ~r2_hidden(A_86, B_88) | ~r2_hidden(A_86, k5_xboole_0(B_88, C_87)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.50/1.33  tff(c_302, plain, (![A_89]: (~r2_hidden(A_89, k1_xboole_0) | ~r2_hidden(A_89, k1_xboole_0) | ~r2_hidden(A_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_226, c_295])).
% 2.50/1.33  tff(c_304, plain, (~r2_hidden('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_270, c_302])).
% 2.50/1.33  tff(c_308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_270, c_304])).
% 2.50/1.33  tff(c_309, plain, (k1_tarski('#skF_3')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_172])).
% 2.50/1.33  tff(c_327, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_309, c_135])).
% 2.50/1.33  tff(c_48, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.50/1.33  tff(c_390, plain, (![E_107, C_108, B_109, A_110]: (E_107=C_108 | E_107=B_109 | E_107=A_110 | ~r2_hidden(E_107, k1_enumset1(A_110, B_109, C_108)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.50/1.33  tff(c_459, plain, (![E_115, B_116, A_117]: (E_115=B_116 | E_115=A_117 | E_115=A_117 | ~r2_hidden(E_115, k2_tarski(A_117, B_116)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_390])).
% 2.50/1.33  tff(c_482, plain, (![E_123, A_124]: (E_123=A_124 | E_123=A_124 | E_123=A_124 | ~r2_hidden(E_123, k1_tarski(A_124)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_459])).
% 2.50/1.33  tff(c_485, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_327, c_482])).
% 2.50/1.33  tff(c_495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_66, c_66, c_485])).
% 2.50/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.33  
% 2.50/1.33  Inference rules
% 2.50/1.33  ----------------------
% 2.50/1.33  #Ref     : 0
% 2.50/1.33  #Sup     : 108
% 2.50/1.33  #Fact    : 1
% 2.50/1.33  #Define  : 0
% 2.50/1.33  #Split   : 1
% 2.50/1.33  #Chain   : 0
% 2.50/1.33  #Close   : 0
% 2.50/1.33  
% 2.50/1.33  Ordering : KBO
% 2.50/1.33  
% 2.50/1.33  Simplification rules
% 2.50/1.33  ----------------------
% 2.50/1.33  #Subsume      : 18
% 2.50/1.33  #Demod        : 32
% 2.50/1.33  #Tautology    : 68
% 2.50/1.33  #SimpNegUnit  : 1
% 2.50/1.33  #BackRed      : 4
% 2.50/1.33  
% 2.50/1.33  #Partial instantiations: 0
% 2.50/1.33  #Strategies tried      : 1
% 2.50/1.33  
% 2.50/1.33  Timing (in seconds)
% 2.50/1.33  ----------------------
% 2.50/1.33  Preprocessing        : 0.32
% 2.50/1.33  Parsing              : 0.16
% 2.50/1.33  CNF conversion       : 0.02
% 2.50/1.33  Main loop            : 0.26
% 2.50/1.33  Inferencing          : 0.09
% 2.50/1.33  Reduction            : 0.09
% 2.50/1.33  Demodulation         : 0.06
% 2.50/1.33  BG Simplification    : 0.02
% 2.50/1.33  Subsumption          : 0.04
% 2.50/1.33  Abstraction          : 0.01
% 2.50/1.33  MUC search           : 0.00
% 2.50/1.33  Cooper               : 0.00
% 2.50/1.33  Total                : 0.61
% 2.50/1.33  Index Insertion      : 0.00
% 2.50/1.33  Index Deletion       : 0.00
% 2.50/1.33  Index Matching       : 0.00
% 2.50/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
