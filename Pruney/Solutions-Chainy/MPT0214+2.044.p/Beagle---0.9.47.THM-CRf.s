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
% DateTime   : Thu Dec  3 09:47:35 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   52 (  89 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 ( 129 expanded)
%              Number of equality atoms :   35 (  78 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_66,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_52,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_119,plain,(
    ! [B_59,A_60] :
      ( k1_tarski(B_59) = A_60
      | k1_xboole_0 = A_60
      | ~ r1_tarski(A_60,k1_tarski(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_131,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_4')
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_119])).

tff(c_134,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_38,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_84,plain,(
    ! [A_45,B_46] : k1_enumset1(A_45,A_45,B_46) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [E_15,B_10,C_11] : r2_hidden(E_15,k1_enumset1(E_15,B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_102,plain,(
    ! [A_47,B_48] : r2_hidden(A_47,k2_tarski(A_47,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_20])).

tff(c_105,plain,(
    ! [A_16] : r2_hidden(A_16,k1_tarski(A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_102])).

tff(c_143,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_105])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_115,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,B_57)
      | ~ r2_hidden(C_58,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_174,plain,(
    ! [C_65,B_66,A_67] :
      ( ~ r2_hidden(C_65,B_66)
      | ~ r2_hidden(C_65,A_67)
      | k4_xboole_0(A_67,B_66) != A_67 ) ),
    inference(resolution,[status(thm)],[c_12,c_115])).

tff(c_176,plain,(
    ! [A_67] :
      ( ~ r2_hidden('#skF_4',A_67)
      | k4_xboole_0(A_67,k1_xboole_0) != A_67 ) ),
    inference(resolution,[status(thm)],[c_143,c_174])).

tff(c_195,plain,(
    ! [A_67] : ~ r2_hidden('#skF_4',A_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_176])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_143])).

tff(c_206,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_216,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_105])).

tff(c_40,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_287,plain,(
    ! [E_84,C_85,B_86,A_87] :
      ( E_84 = C_85
      | E_84 = B_86
      | E_84 = A_87
      | ~ r2_hidden(E_84,k1_enumset1(A_87,B_86,C_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_332,plain,(
    ! [E_103,B_104,A_105] :
      ( E_103 = B_104
      | E_103 = A_105
      | E_103 = A_105
      | ~ r2_hidden(E_103,k2_tarski(A_105,B_104)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_287])).

tff(c_357,plain,(
    ! [E_110,A_111] :
      ( E_110 = A_111
      | E_110 = A_111
      | E_110 = A_111
      | ~ r2_hidden(E_110,k1_tarski(A_111)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_332])).

tff(c_360,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_216,c_357])).

tff(c_378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_52,c_52,c_360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.33  
% 2.08/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.08/1.33  
% 2.08/1.33  %Foreground sorts:
% 2.08/1.33  
% 2.08/1.33  
% 2.08/1.33  %Background operators:
% 2.08/1.33  
% 2.08/1.33  
% 2.08/1.33  %Foreground operators:
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.08/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.08/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.08/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.08/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.08/1.33  
% 2.46/1.34  tff(f_83, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.46/1.34  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.46/1.34  tff(f_78, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.46/1.34  tff(f_66, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.46/1.34  tff(f_68, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.46/1.34  tff(f_64, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.46/1.34  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.46/1.34  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.46/1.34  tff(c_52, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.46/1.34  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.46/1.34  tff(c_54, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.46/1.34  tff(c_119, plain, (![B_59, A_60]: (k1_tarski(B_59)=A_60 | k1_xboole_0=A_60 | ~r1_tarski(A_60, k1_tarski(B_59)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.46/1.34  tff(c_131, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4') | k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_119])).
% 2.46/1.34  tff(c_134, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_131])).
% 2.46/1.34  tff(c_38, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.46/1.34  tff(c_84, plain, (![A_45, B_46]: (k1_enumset1(A_45, A_45, B_46)=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.46/1.34  tff(c_20, plain, (![E_15, B_10, C_11]: (r2_hidden(E_15, k1_enumset1(E_15, B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.46/1.34  tff(c_102, plain, (![A_47, B_48]: (r2_hidden(A_47, k2_tarski(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_20])).
% 2.46/1.34  tff(c_105, plain, (![A_16]: (r2_hidden(A_16, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_102])).
% 2.46/1.34  tff(c_143, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_134, c_105])).
% 2.46/1.34  tff(c_12, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k4_xboole_0(A_7, B_8)!=A_7)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.46/1.34  tff(c_115, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, B_57) | ~r2_hidden(C_58, A_56))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.46/1.34  tff(c_174, plain, (![C_65, B_66, A_67]: (~r2_hidden(C_65, B_66) | ~r2_hidden(C_65, A_67) | k4_xboole_0(A_67, B_66)!=A_67)), inference(resolution, [status(thm)], [c_12, c_115])).
% 2.46/1.34  tff(c_176, plain, (![A_67]: (~r2_hidden('#skF_4', A_67) | k4_xboole_0(A_67, k1_xboole_0)!=A_67)), inference(resolution, [status(thm)], [c_143, c_174])).
% 2.46/1.34  tff(c_195, plain, (![A_67]: (~r2_hidden('#skF_4', A_67))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_176])).
% 2.46/1.34  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_195, c_143])).
% 2.46/1.34  tff(c_206, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_131])).
% 2.46/1.34  tff(c_216, plain, (r2_hidden('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_206, c_105])).
% 2.46/1.34  tff(c_40, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.46/1.34  tff(c_287, plain, (![E_84, C_85, B_86, A_87]: (E_84=C_85 | E_84=B_86 | E_84=A_87 | ~r2_hidden(E_84, k1_enumset1(A_87, B_86, C_85)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.46/1.34  tff(c_332, plain, (![E_103, B_104, A_105]: (E_103=B_104 | E_103=A_105 | E_103=A_105 | ~r2_hidden(E_103, k2_tarski(A_105, B_104)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_287])).
% 2.46/1.34  tff(c_357, plain, (![E_110, A_111]: (E_110=A_111 | E_110=A_111 | E_110=A_111 | ~r2_hidden(E_110, k1_tarski(A_111)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_332])).
% 2.46/1.34  tff(c_360, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_216, c_357])).
% 2.46/1.34  tff(c_378, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_52, c_52, c_360])).
% 2.46/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.34  
% 2.46/1.34  Inference rules
% 2.46/1.34  ----------------------
% 2.46/1.34  #Ref     : 0
% 2.46/1.34  #Sup     : 77
% 2.46/1.34  #Fact    : 0
% 2.46/1.34  #Define  : 0
% 2.46/1.34  #Split   : 1
% 2.46/1.35  #Chain   : 0
% 2.46/1.35  #Close   : 0
% 2.46/1.35  
% 2.46/1.35  Ordering : KBO
% 2.46/1.35  
% 2.46/1.35  Simplification rules
% 2.46/1.35  ----------------------
% 2.46/1.35  #Subsume      : 7
% 2.46/1.35  #Demod        : 17
% 2.46/1.35  #Tautology    : 34
% 2.46/1.35  #SimpNegUnit  : 2
% 2.46/1.35  #BackRed      : 3
% 2.46/1.35  
% 2.46/1.35  #Partial instantiations: 0
% 2.46/1.35  #Strategies tried      : 1
% 2.46/1.35  
% 2.46/1.35  Timing (in seconds)
% 2.46/1.35  ----------------------
% 2.46/1.35  Preprocessing        : 0.29
% 2.46/1.35  Parsing              : 0.14
% 2.46/1.35  CNF conversion       : 0.02
% 2.46/1.35  Main loop            : 0.23
% 2.46/1.35  Inferencing          : 0.09
% 2.46/1.35  Reduction            : 0.07
% 2.46/1.35  Demodulation         : 0.05
% 2.46/1.35  BG Simplification    : 0.02
% 2.46/1.35  Subsumption          : 0.04
% 2.46/1.35  Abstraction          : 0.01
% 2.46/1.35  MUC search           : 0.00
% 2.46/1.35  Cooper               : 0.00
% 2.46/1.35  Total                : 0.55
% 2.46/1.35  Index Insertion      : 0.00
% 2.46/1.35  Index Deletion       : 0.00
% 2.46/1.35  Index Matching       : 0.00
% 2.46/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
