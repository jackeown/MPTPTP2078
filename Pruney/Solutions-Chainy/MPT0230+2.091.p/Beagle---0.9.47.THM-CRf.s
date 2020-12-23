%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:07 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   63 (  92 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 120 expanded)
%              Number of equality atoms :   44 (  81 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_58,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_105,plain,(
    ! [A_61,B_62] : k1_enumset1(A_61,A_61,B_62) = k2_tarski(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    ! [E_14,B_9,C_10] : r2_hidden(E_14,k1_enumset1(E_14,B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_111,plain,(
    ! [A_61,B_62] : r2_hidden(A_61,k2_tarski(A_61,B_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_20])).

tff(c_12,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,B_59) = A_58
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_144,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_153,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_144])).

tff(c_156,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_153])).

tff(c_302,plain,(
    ! [A_95,C_96,B_97] :
      ( ~ r2_hidden(A_95,C_96)
      | k4_xboole_0(k2_tarski(A_95,B_97),C_96) != k1_tarski(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_306,plain,(
    ! [A_95,B_97] :
      ( ~ r2_hidden(A_95,k2_tarski(A_95,B_97))
      | k1_tarski(A_95) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_302])).

tff(c_311,plain,(
    ! [A_95] : k1_tarski(A_95) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_306])).

tff(c_62,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_60,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_38,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_56,plain,(
    ! [B_44,C_45] :
      ( k4_xboole_0(k2_tarski(B_44,B_44),C_45) = k1_tarski(B_44)
      | r2_hidden(B_44,C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_185,plain,(
    ! [B_76,C_77] :
      ( k4_xboole_0(k1_tarski(B_76),C_77) = k1_tarski(B_76)
      | r2_hidden(B_76,C_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_56])).

tff(c_64,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_94,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_87])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_167,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_8])).

tff(c_170,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_167])).

tff(c_191,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_170])).

tff(c_210,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_40,plain,(
    ! [A_16,B_17] : k1_enumset1(A_16,A_16,B_17) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_250,plain,(
    ! [E_88,C_89,B_90,A_91] :
      ( E_88 = C_89
      | E_88 = B_90
      | E_88 = A_91
      | ~ r2_hidden(E_88,k1_enumset1(A_91,B_90,C_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_269,plain,(
    ! [E_92,B_93,A_94] :
      ( E_92 = B_93
      | E_92 = A_94
      | E_92 = A_94
      | ~ r2_hidden(E_92,k2_tarski(A_94,B_93)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_250])).

tff(c_272,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_210,c_269])).

tff(c_285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_62,c_60,c_272])).

tff(c_286,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.30  
% 2.13/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.30  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.13/1.30  
% 2.13/1.30  %Foreground sorts:
% 2.13/1.30  
% 2.13/1.30  
% 2.13/1.30  %Background operators:
% 2.13/1.30  
% 2.13/1.30  
% 2.13/1.30  %Foreground operators:
% 2.13/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.13/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.13/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.13/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.13/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.13/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.13/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.13/1.30  
% 2.13/1.31  tff(f_58, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.13/1.31  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.13/1.31  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.13/1.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.13/1.31  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.13/1.31  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.13/1.31  tff(f_77, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 2.13/1.31  tff(f_87, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.13/1.31  tff(f_56, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.13/1.31  tff(c_105, plain, (![A_61, B_62]: (k1_enumset1(A_61, A_61, B_62)=k2_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.13/1.31  tff(c_20, plain, (![E_14, B_9, C_10]: (r2_hidden(E_14, k1_enumset1(E_14, B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.13/1.31  tff(c_111, plain, (![A_61, B_62]: (r2_hidden(A_61, k2_tarski(A_61, B_62)))), inference(superposition, [status(thm), theory('equality')], [c_105, c_20])).
% 2.13/1.31  tff(c_12, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.13/1.31  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.31  tff(c_87, plain, (![A_58, B_59]: (k3_xboole_0(A_58, B_59)=A_58 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.31  tff(c_95, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_87])).
% 2.13/1.31  tff(c_144, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.31  tff(c_153, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_95, c_144])).
% 2.13/1.31  tff(c_156, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_153])).
% 2.13/1.31  tff(c_302, plain, (![A_95, C_96, B_97]: (~r2_hidden(A_95, C_96) | k4_xboole_0(k2_tarski(A_95, B_97), C_96)!=k1_tarski(A_95))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.13/1.31  tff(c_306, plain, (![A_95, B_97]: (~r2_hidden(A_95, k2_tarski(A_95, B_97)) | k1_tarski(A_95)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_156, c_302])).
% 2.13/1.31  tff(c_311, plain, (![A_95]: (k1_tarski(A_95)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_306])).
% 2.13/1.31  tff(c_62, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.13/1.31  tff(c_60, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.13/1.31  tff(c_38, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.13/1.31  tff(c_56, plain, (![B_44, C_45]: (k4_xboole_0(k2_tarski(B_44, B_44), C_45)=k1_tarski(B_44) | r2_hidden(B_44, C_45))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.13/1.31  tff(c_185, plain, (![B_76, C_77]: (k4_xboole_0(k1_tarski(B_76), C_77)=k1_tarski(B_76) | r2_hidden(B_76, C_77))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_56])).
% 2.13/1.31  tff(c_64, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.13/1.31  tff(c_94, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_64, c_87])).
% 2.13/1.31  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.31  tff(c_167, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_8])).
% 2.13/1.31  tff(c_170, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_167])).
% 2.13/1.31  tff(c_191, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_185, c_170])).
% 2.13/1.31  tff(c_210, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_191])).
% 2.13/1.31  tff(c_40, plain, (![A_16, B_17]: (k1_enumset1(A_16, A_16, B_17)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.13/1.31  tff(c_250, plain, (![E_88, C_89, B_90, A_91]: (E_88=C_89 | E_88=B_90 | E_88=A_91 | ~r2_hidden(E_88, k1_enumset1(A_91, B_90, C_89)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.13/1.31  tff(c_269, plain, (![E_92, B_93, A_94]: (E_92=B_93 | E_92=A_94 | E_92=A_94 | ~r2_hidden(E_92, k2_tarski(A_94, B_93)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_250])).
% 2.13/1.31  tff(c_272, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_210, c_269])).
% 2.13/1.31  tff(c_285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_62, c_60, c_272])).
% 2.13/1.31  tff(c_286, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_191])).
% 2.13/1.31  tff(c_313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_311, c_286])).
% 2.13/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.31  
% 2.13/1.31  Inference rules
% 2.13/1.31  ----------------------
% 2.13/1.31  #Ref     : 0
% 2.13/1.31  #Sup     : 56
% 2.13/1.31  #Fact    : 0
% 2.13/1.31  #Define  : 0
% 2.13/1.31  #Split   : 2
% 2.13/1.31  #Chain   : 0
% 2.13/1.31  #Close   : 0
% 2.13/1.31  
% 2.13/1.31  Ordering : KBO
% 2.13/1.31  
% 2.13/1.31  Simplification rules
% 2.13/1.31  ----------------------
% 2.13/1.31  #Subsume      : 2
% 2.13/1.31  #Demod        : 19
% 2.13/1.31  #Tautology    : 35
% 2.13/1.31  #SimpNegUnit  : 3
% 2.13/1.31  #BackRed      : 4
% 2.13/1.31  
% 2.13/1.31  #Partial instantiations: 0
% 2.13/1.31  #Strategies tried      : 1
% 2.13/1.31  
% 2.13/1.31  Timing (in seconds)
% 2.13/1.31  ----------------------
% 2.13/1.31  Preprocessing        : 0.33
% 2.13/1.32  Parsing              : 0.18
% 2.13/1.32  CNF conversion       : 0.02
% 2.13/1.32  Main loop            : 0.19
% 2.13/1.32  Inferencing          : 0.06
% 2.13/1.32  Reduction            : 0.06
% 2.13/1.32  Demodulation         : 0.05
% 2.13/1.32  BG Simplification    : 0.02
% 2.13/1.32  Subsumption          : 0.04
% 2.13/1.32  Abstraction          : 0.01
% 2.13/1.32  MUC search           : 0.00
% 2.13/1.32  Cooper               : 0.00
% 2.13/1.32  Total                : 0.55
% 2.13/1.32  Index Insertion      : 0.00
% 2.13/1.32  Index Deletion       : 0.00
% 2.13/1.32  Index Matching       : 0.00
% 2.13/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
