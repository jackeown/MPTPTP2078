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

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   56 (  88 expanded)
%              Number of leaves         :   29 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :   63 ( 118 expanded)
%              Number of equality atoms :   35 (  64 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

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

tff(f_82,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_36,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_103,plain,(
    ! [A_66,B_67] : k1_enumset1(A_66,A_66,B_67) = k2_tarski(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [E_16,A_10,C_12] : r2_hidden(E_16,k1_enumset1(A_10,E_16,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_121,plain,(
    ! [A_68,B_69] : r2_hidden(A_68,k2_tarski(A_68,B_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_16])).

tff(c_124,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_121])).

tff(c_56,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_58,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_73,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(A_59,B_60) = A_59
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_84,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_73])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_125,plain,(
    ! [A_70,B_71,C_72] :
      ( ~ r1_xboole_0(A_70,B_71)
      | ~ r2_hidden(C_72,k3_xboole_0(A_70,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_131,plain,(
    ! [C_72] :
      ( ~ r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5'))
      | ~ r2_hidden(C_72,k1_tarski('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_125])).

tff(c_139,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_142,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_139])).

tff(c_144,plain,(
    k1_tarski('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_142])).

tff(c_168,plain,(
    ! [B_81,A_82] :
      ( k1_tarski(B_81) = A_82
      | k1_xboole_0 = A_82
      | ~ r1_tarski(A_82,k1_tarski(B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_174,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_4')
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_168])).

tff(c_182,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_174])).

tff(c_202,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_124])).

tff(c_38,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_286,plain,(
    ! [E_95,C_96,B_97,A_98] :
      ( E_95 = C_96
      | E_95 = B_97
      | E_95 = A_98
      | ~ r2_hidden(E_95,k1_enumset1(A_98,B_97,C_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_305,plain,(
    ! [E_99,B_100,A_101] :
      ( E_99 = B_100
      | E_99 = A_101
      | E_99 = A_101
      | ~ r2_hidden(E_99,k2_tarski(A_101,B_100)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_286])).

tff(c_319,plain,(
    ! [E_102,A_103] :
      ( E_102 = A_103
      | E_102 = A_103
      | E_102 = A_103
      | ~ r2_hidden(E_102,k1_tarski(A_103)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_305])).

tff(c_322,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_202,c_319])).

tff(c_332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_56,c_322])).

tff(c_335,plain,(
    ! [C_104] : ~ r2_hidden(C_104,k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_340,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_124,c_335])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n018.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 17:17:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.30  
% 2.20/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.30  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.20/1.30  
% 2.20/1.30  %Foreground sorts:
% 2.20/1.30  
% 2.20/1.30  
% 2.20/1.30  %Background operators:
% 2.20/1.30  
% 2.20/1.30  
% 2.20/1.30  %Foreground operators:
% 2.20/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.20/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.20/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.20/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.20/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.20/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.20/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.20/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.20/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.20/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.20/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.20/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.20/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.20/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.20/1.30  
% 2.20/1.31  tff(f_64, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.20/1.31  tff(f_66, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.20/1.31  tff(f_62, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.20/1.31  tff(f_87, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.20/1.31  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.20/1.31  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.20/1.31  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.20/1.31  tff(f_82, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.20/1.31  tff(c_36, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.20/1.31  tff(c_103, plain, (![A_66, B_67]: (k1_enumset1(A_66, A_66, B_67)=k2_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.20/1.31  tff(c_16, plain, (![E_16, A_10, C_12]: (r2_hidden(E_16, k1_enumset1(A_10, E_16, C_12)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.20/1.31  tff(c_121, plain, (![A_68, B_69]: (r2_hidden(A_68, k2_tarski(A_68, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_16])).
% 2.20/1.31  tff(c_124, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_121])).
% 2.20/1.31  tff(c_56, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.20/1.31  tff(c_58, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.20/1.31  tff(c_73, plain, (![A_59, B_60]: (k3_xboole_0(A_59, B_60)=A_59 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.20/1.31  tff(c_84, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_58, c_73])).
% 2.20/1.31  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.31  tff(c_125, plain, (![A_70, B_71, C_72]: (~r1_xboole_0(A_70, B_71) | ~r2_hidden(C_72, k3_xboole_0(A_70, B_71)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.20/1.31  tff(c_131, plain, (![C_72]: (~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')) | ~r2_hidden(C_72, k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_84, c_125])).
% 2.20/1.31  tff(c_139, plain, (~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_131])).
% 2.20/1.31  tff(c_142, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_139])).
% 2.20/1.31  tff(c_144, plain, (k1_tarski('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_84, c_142])).
% 2.20/1.31  tff(c_168, plain, (![B_81, A_82]: (k1_tarski(B_81)=A_82 | k1_xboole_0=A_82 | ~r1_tarski(A_82, k1_tarski(B_81)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.20/1.31  tff(c_174, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4') | k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_168])).
% 2.20/1.31  tff(c_182, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_144, c_174])).
% 2.20/1.31  tff(c_202, plain, (r2_hidden('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_182, c_124])).
% 2.20/1.31  tff(c_38, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.20/1.31  tff(c_286, plain, (![E_95, C_96, B_97, A_98]: (E_95=C_96 | E_95=B_97 | E_95=A_98 | ~r2_hidden(E_95, k1_enumset1(A_98, B_97, C_96)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.20/1.31  tff(c_305, plain, (![E_99, B_100, A_101]: (E_99=B_100 | E_99=A_101 | E_99=A_101 | ~r2_hidden(E_99, k2_tarski(A_101, B_100)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_286])).
% 2.20/1.31  tff(c_319, plain, (![E_102, A_103]: (E_102=A_103 | E_102=A_103 | E_102=A_103 | ~r2_hidden(E_102, k1_tarski(A_103)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_305])).
% 2.20/1.31  tff(c_322, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_202, c_319])).
% 2.20/1.31  tff(c_332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_56, c_322])).
% 2.20/1.31  tff(c_335, plain, (![C_104]: (~r2_hidden(C_104, k1_tarski('#skF_4')))), inference(splitRight, [status(thm)], [c_131])).
% 2.20/1.31  tff(c_340, plain, $false, inference(resolution, [status(thm)], [c_124, c_335])).
% 2.20/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.31  
% 2.20/1.31  Inference rules
% 2.20/1.31  ----------------------
% 2.20/1.31  #Ref     : 0
% 2.20/1.31  #Sup     : 64
% 2.20/1.31  #Fact    : 0
% 2.20/1.31  #Define  : 0
% 2.20/1.31  #Split   : 2
% 2.20/1.31  #Chain   : 0
% 2.20/1.31  #Close   : 0
% 2.20/1.31  
% 2.20/1.31  Ordering : KBO
% 2.20/1.31  
% 2.20/1.31  Simplification rules
% 2.20/1.31  ----------------------
% 2.20/1.31  #Subsume      : 9
% 2.20/1.31  #Demod        : 30
% 2.20/1.31  #Tautology    : 37
% 2.20/1.31  #SimpNegUnit  : 3
% 2.20/1.31  #BackRed      : 3
% 2.20/1.31  
% 2.20/1.31  #Partial instantiations: 0
% 2.20/1.31  #Strategies tried      : 1
% 2.20/1.31  
% 2.20/1.31  Timing (in seconds)
% 2.20/1.31  ----------------------
% 2.20/1.32  Preprocessing        : 0.32
% 2.20/1.32  Parsing              : 0.16
% 2.20/1.32  CNF conversion       : 0.02
% 2.20/1.32  Main loop            : 0.20
% 2.20/1.32  Inferencing          : 0.07
% 2.20/1.32  Reduction            : 0.07
% 2.20/1.32  Demodulation         : 0.05
% 2.20/1.32  BG Simplification    : 0.02
% 2.20/1.32  Subsumption          : 0.04
% 2.20/1.32  Abstraction          : 0.01
% 2.20/1.32  MUC search           : 0.00
% 2.20/1.32  Cooper               : 0.00
% 2.20/1.32  Total                : 0.54
% 2.20/1.32  Index Insertion      : 0.00
% 2.20/1.32  Index Deletion       : 0.00
% 2.20/1.32  Index Matching       : 0.00
% 2.20/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
