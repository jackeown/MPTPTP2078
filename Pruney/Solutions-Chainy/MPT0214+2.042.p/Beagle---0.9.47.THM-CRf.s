%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:35 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_42,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_66,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_68,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_237,plain,(
    ! [B_76,A_77] :
      ( k1_tarski(B_76) = A_77
      | k1_xboole_0 = A_77
      | ~ r1_tarski(A_77,k1_tarski(B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_250,plain,
    ( k1_tarski('#skF_3') = k1_tarski('#skF_4')
    | k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_237])).

tff(c_266,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_46,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_113,plain,(
    ! [A_63,B_64] : k1_enumset1(A_63,A_63,B_64) = k2_tarski(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [E_16,B_11,C_12] : r2_hidden(E_16,k1_enumset1(E_16,B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_131,plain,(
    ! [A_65,B_66] : r2_hidden(A_65,k2_tarski(A_65,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_28])).

tff(c_134,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_131])).

tff(c_283,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_134])).

tff(c_18,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_93,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_105,plain,(
    ! [A_8] : k3_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_93])).

tff(c_137,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = k4_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_154,plain,(
    ! [A_72] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_137])).

tff(c_146,plain,(
    ! [A_8] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_137])).

tff(c_163,plain,(
    ! [A_74,A_73] : k4_xboole_0(k1_xboole_0,A_74) = k4_xboole_0(k1_xboole_0,A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_146])).

tff(c_20,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_179,plain,(
    ! [A_74] : k4_xboole_0(k1_xboole_0,A_74) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_20])).

tff(c_212,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_146])).

tff(c_342,plain,(
    ! [A_87,C_88,B_89] :
      ( ~ r2_hidden(A_87,C_88)
      | ~ r2_hidden(A_87,B_89)
      | ~ r2_hidden(A_87,k5_xboole_0(B_89,C_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_352,plain,(
    ! [A_90] :
      ( ~ r2_hidden(A_90,k1_xboole_0)
      | ~ r2_hidden(A_90,k1_xboole_0)
      | ~ r2_hidden(A_90,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_342])).

tff(c_354,plain,(
    ~ r2_hidden('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_283,c_352])).

tff(c_358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_354])).

tff(c_359,plain,(
    k1_tarski('#skF_3') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_378,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_134])).

tff(c_48,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_486,plain,(
    ! [E_112,C_113,B_114,A_115] :
      ( E_112 = C_113
      | E_112 = B_114
      | E_112 = A_115
      | ~ r2_hidden(E_112,k1_enumset1(A_115,B_114,C_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_505,plain,(
    ! [E_116,B_117,A_118] :
      ( E_116 = B_117
      | E_116 = A_118
      | E_116 = A_118
      | ~ r2_hidden(E_116,k2_tarski(A_118,B_117)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_486])).

tff(c_519,plain,(
    ! [E_119,A_120] :
      ( E_119 = A_120
      | E_119 = A_120
      | E_119 = A_120
      | ~ r2_hidden(E_119,k1_tarski(A_120)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_505])).

tff(c_522,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_378,c_519])).

tff(c_532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_66,c_66,c_522])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:18:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.49  
% 2.66/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.50  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.66/1.50  
% 2.66/1.50  %Foreground sorts:
% 2.66/1.50  
% 2.66/1.50  
% 2.66/1.50  %Background operators:
% 2.66/1.50  
% 2.66/1.50  
% 2.66/1.50  %Foreground operators:
% 2.66/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.66/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.66/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.66/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.66/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.66/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.66/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.66/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.66/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.66/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.66/1.50  
% 2.66/1.51  tff(f_82, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.66/1.51  tff(f_77, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.66/1.51  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.66/1.51  tff(f_61, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.66/1.51  tff(f_57, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.66/1.51  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.66/1.51  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.66/1.51  tff(f_34, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.66/1.51  tff(f_42, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.66/1.51  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.66/1.51  tff(c_66, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.66/1.51  tff(c_68, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.66/1.51  tff(c_237, plain, (![B_76, A_77]: (k1_tarski(B_76)=A_77 | k1_xboole_0=A_77 | ~r1_tarski(A_77, k1_tarski(B_76)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.66/1.51  tff(c_250, plain, (k1_tarski('#skF_3')=k1_tarski('#skF_4') | k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_237])).
% 2.66/1.51  tff(c_266, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_250])).
% 2.66/1.51  tff(c_46, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.66/1.51  tff(c_113, plain, (![A_63, B_64]: (k1_enumset1(A_63, A_63, B_64)=k2_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.66/1.51  tff(c_28, plain, (![E_16, B_11, C_12]: (r2_hidden(E_16, k1_enumset1(E_16, B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.66/1.51  tff(c_131, plain, (![A_65, B_66]: (r2_hidden(A_65, k2_tarski(A_65, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_28])).
% 2.66/1.51  tff(c_134, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_131])).
% 2.66/1.51  tff(c_283, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_266, c_134])).
% 2.66/1.51  tff(c_18, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.66/1.51  tff(c_93, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.66/1.51  tff(c_105, plain, (![A_8]: (k3_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_93])).
% 2.66/1.51  tff(c_137, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k3_xboole_0(A_68, B_69))=k4_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.66/1.51  tff(c_154, plain, (![A_72]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_72))), inference(superposition, [status(thm), theory('equality')], [c_105, c_137])).
% 2.66/1.51  tff(c_146, plain, (![A_8]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_8))), inference(superposition, [status(thm), theory('equality')], [c_105, c_137])).
% 2.66/1.51  tff(c_163, plain, (![A_74, A_73]: (k4_xboole_0(k1_xboole_0, A_74)=k4_xboole_0(k1_xboole_0, A_73))), inference(superposition, [status(thm), theory('equality')], [c_154, c_146])).
% 2.66/1.51  tff(c_20, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.66/1.51  tff(c_179, plain, (![A_74]: (k4_xboole_0(k1_xboole_0, A_74)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_163, c_20])).
% 2.66/1.51  tff(c_212, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_179, c_146])).
% 2.66/1.51  tff(c_342, plain, (![A_87, C_88, B_89]: (~r2_hidden(A_87, C_88) | ~r2_hidden(A_87, B_89) | ~r2_hidden(A_87, k5_xboole_0(B_89, C_88)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.51  tff(c_352, plain, (![A_90]: (~r2_hidden(A_90, k1_xboole_0) | ~r2_hidden(A_90, k1_xboole_0) | ~r2_hidden(A_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_212, c_342])).
% 2.66/1.51  tff(c_354, plain, (~r2_hidden('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_283, c_352])).
% 2.66/1.51  tff(c_358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_283, c_354])).
% 2.66/1.51  tff(c_359, plain, (k1_tarski('#skF_3')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_250])).
% 2.66/1.51  tff(c_378, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_359, c_134])).
% 2.66/1.51  tff(c_48, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.66/1.51  tff(c_486, plain, (![E_112, C_113, B_114, A_115]: (E_112=C_113 | E_112=B_114 | E_112=A_115 | ~r2_hidden(E_112, k1_enumset1(A_115, B_114, C_113)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.66/1.51  tff(c_505, plain, (![E_116, B_117, A_118]: (E_116=B_117 | E_116=A_118 | E_116=A_118 | ~r2_hidden(E_116, k2_tarski(A_118, B_117)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_486])).
% 2.66/1.51  tff(c_519, plain, (![E_119, A_120]: (E_119=A_120 | E_119=A_120 | E_119=A_120 | ~r2_hidden(E_119, k1_tarski(A_120)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_505])).
% 2.66/1.51  tff(c_522, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_378, c_519])).
% 2.66/1.51  tff(c_532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_66, c_66, c_522])).
% 2.66/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.51  
% 2.66/1.51  Inference rules
% 2.66/1.51  ----------------------
% 2.66/1.51  #Ref     : 0
% 2.66/1.51  #Sup     : 118
% 2.66/1.51  #Fact    : 0
% 2.66/1.51  #Define  : 0
% 2.66/1.51  #Split   : 1
% 2.66/1.51  #Chain   : 0
% 2.66/1.51  #Close   : 0
% 2.66/1.51  
% 2.66/1.51  Ordering : KBO
% 2.66/1.51  
% 2.66/1.51  Simplification rules
% 2.66/1.51  ----------------------
% 2.66/1.51  #Subsume      : 13
% 2.66/1.51  #Demod        : 68
% 2.66/1.51  #Tautology    : 82
% 2.66/1.51  #SimpNegUnit  : 1
% 2.66/1.51  #BackRed      : 6
% 2.66/1.51  
% 2.66/1.51  #Partial instantiations: 0
% 2.66/1.51  #Strategies tried      : 1
% 2.66/1.51  
% 2.66/1.51  Timing (in seconds)
% 2.66/1.51  ----------------------
% 2.66/1.51  Preprocessing        : 0.38
% 2.66/1.51  Parsing              : 0.20
% 2.66/1.51  CNF conversion       : 0.03
% 2.66/1.51  Main loop            : 0.29
% 2.66/1.51  Inferencing          : 0.10
% 2.66/1.51  Reduction            : 0.10
% 2.66/1.51  Demodulation         : 0.08
% 2.66/1.51  BG Simplification    : 0.02
% 2.66/1.52  Subsumption          : 0.04
% 2.66/1.52  Abstraction          : 0.02
% 2.66/1.52  MUC search           : 0.00
% 2.66/1.52  Cooper               : 0.00
% 2.66/1.52  Total                : 0.71
% 2.66/1.52  Index Insertion      : 0.00
% 2.66/1.52  Index Deletion       : 0.00
% 2.66/1.52  Index Matching       : 0.00
% 2.66/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
