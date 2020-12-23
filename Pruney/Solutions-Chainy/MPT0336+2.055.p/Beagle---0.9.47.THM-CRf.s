%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:07 EST 2020

% Result     : Theorem 4.76s
% Output     : CNFRefutation 4.76s
% Verified   : 
% Statistics : Number of formulae       :   68 (  94 expanded)
%              Number of leaves         :   31 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 136 expanded)
%              Number of equality atoms :   30 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_49,axiom,(
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

tff(f_67,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_278,plain,(
    ! [A_71,B_72,C_73] :
      ( ~ r1_xboole_0(A_71,B_72)
      | ~ r2_hidden(C_73,B_72)
      | ~ r2_hidden(C_73,A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_291,plain,(
    ! [C_74] : ~ r2_hidden(C_74,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_278])).

tff(c_317,plain,(
    ! [B_76] : r1_xboole_0(k1_xboole_0,B_76) ),
    inference(resolution,[status(thm)],[c_12,c_291])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_328,plain,(
    ! [B_76] : k3_xboole_0(k1_xboole_0,B_76) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_317,c_4])).

tff(c_42,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_173,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = k1_xboole_0
      | ~ r1_xboole_0(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_189,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_173])).

tff(c_496,plain,(
    ! [A_85,B_86,C_87] : k3_xboole_0(k3_xboole_0(A_85,B_86),C_87) = k3_xboole_0(A_85,k3_xboole_0(B_86,C_87)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_558,plain,(
    ! [C_87] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_3',C_87)) = k3_xboole_0(k1_xboole_0,C_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_496])).

tff(c_591,plain,(
    ! [C_87] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_3',C_87)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_558])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1191,plain,(
    ! [A_104,B_105,C_106] :
      ( k3_xboole_0(A_104,k2_xboole_0(B_105,C_106)) = k3_xboole_0(A_104,C_106)
      | ~ r1_xboole_0(A_104,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_146,plain,(
    ! [A_53,B_54] :
      ( r1_xboole_0(A_53,B_54)
      | k3_xboole_0(A_53,B_54) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_153,plain,(
    k3_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_146,c_40])).

tff(c_156,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_2','#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_153])).

tff(c_1228,plain,
    ( k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1191,c_156])).

tff(c_1275,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_2,c_1228])).

tff(c_1284,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1275])).

tff(c_46,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_47,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_96,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_100,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_47,c_96])).

tff(c_107,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k3_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_2])).

tff(c_36,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(k1_tarski(A_40),B_41)
      | r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_186,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(k1_tarski(A_40),B_41) = k1_xboole_0
      | r2_hidden(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_36,c_173])).

tff(c_489,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_186])).

tff(c_1290,plain,(
    r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_1284,c_489])).

tff(c_44,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3490,plain,(
    ! [C_146,B_147,A_148] :
      ( ~ r2_hidden(C_146,B_147)
      | ~ r2_hidden(C_146,A_148)
      | k3_xboole_0(A_148,B_147) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_278])).

tff(c_3509,plain,(
    ! [A_149] :
      ( ~ r2_hidden('#skF_5',A_149)
      | k3_xboole_0(A_149,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_3490])).

tff(c_3512,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1290,c_3509])).

tff(c_3526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_2,c_3512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:58:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.76/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.76/1.99  
% 4.76/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.76/1.99  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.76/1.99  
% 4.76/1.99  %Foreground sorts:
% 4.76/1.99  
% 4.76/1.99  
% 4.76/1.99  %Background operators:
% 4.76/1.99  
% 4.76/1.99  
% 4.76/1.99  %Foreground operators:
% 4.76/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.76/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.76/1.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.76/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.76/1.99  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.76/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.76/1.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.76/1.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.76/1.99  tff('#skF_5', type, '#skF_5': $i).
% 4.76/1.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.76/1.99  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.76/1.99  tff('#skF_2', type, '#skF_2': $i).
% 4.76/1.99  tff('#skF_3', type, '#skF_3': $i).
% 4.76/1.99  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.76/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.76/1.99  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.76/1.99  tff('#skF_4', type, '#skF_4': $i).
% 4.76/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.76/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.76/1.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.76/1.99  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.76/1.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.76/1.99  
% 4.76/2.00  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.76/2.00  tff(f_67, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 4.76/2.00  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.76/2.00  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 4.76/2.00  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 4.76/2.00  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.76/2.00  tff(f_71, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 4.76/2.00  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.76/2.00  tff(f_88, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.76/2.00  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.76/2.00  tff(c_18, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.76/2.00  tff(c_278, plain, (![A_71, B_72, C_73]: (~r1_xboole_0(A_71, B_72) | ~r2_hidden(C_73, B_72) | ~r2_hidden(C_73, A_71))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.76/2.00  tff(c_291, plain, (![C_74]: (~r2_hidden(C_74, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_278])).
% 4.76/2.00  tff(c_317, plain, (![B_76]: (r1_xboole_0(k1_xboole_0, B_76))), inference(resolution, [status(thm)], [c_12, c_291])).
% 4.76/2.00  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.76/2.00  tff(c_328, plain, (![B_76]: (k3_xboole_0(k1_xboole_0, B_76)=k1_xboole_0)), inference(resolution, [status(thm)], [c_317, c_4])).
% 4.76/2.00  tff(c_42, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.76/2.00  tff(c_173, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=k1_xboole_0 | ~r1_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.76/2.00  tff(c_189, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_173])).
% 4.76/2.00  tff(c_496, plain, (![A_85, B_86, C_87]: (k3_xboole_0(k3_xboole_0(A_85, B_86), C_87)=k3_xboole_0(A_85, k3_xboole_0(B_86, C_87)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.76/2.00  tff(c_558, plain, (![C_87]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_3', C_87))=k3_xboole_0(k1_xboole_0, C_87))), inference(superposition, [status(thm), theory('equality')], [c_189, c_496])).
% 4.76/2.00  tff(c_591, plain, (![C_87]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_3', C_87))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_328, c_558])).
% 4.76/2.00  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.76/2.00  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.76/2.00  tff(c_1191, plain, (![A_104, B_105, C_106]: (k3_xboole_0(A_104, k2_xboole_0(B_105, C_106))=k3_xboole_0(A_104, C_106) | ~r1_xboole_0(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.76/2.00  tff(c_146, plain, (![A_53, B_54]: (r1_xboole_0(A_53, B_54) | k3_xboole_0(A_53, B_54)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.76/2.00  tff(c_40, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.76/2.00  tff(c_153, plain, (k3_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_146, c_40])).
% 4.76/2.00  tff(c_156, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_2', '#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_153])).
% 4.76/2.00  tff(c_1228, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0 | ~r1_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1191, c_156])).
% 4.76/2.00  tff(c_1275, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_2, c_1228])).
% 4.76/2.00  tff(c_1284, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1275])).
% 4.76/2.00  tff(c_46, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.76/2.00  tff(c_47, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46])).
% 4.76/2.00  tff(c_96, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=A_48 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.76/2.00  tff(c_100, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_47, c_96])).
% 4.76/2.00  tff(c_107, plain, (k3_xboole_0(k1_tarski('#skF_5'), k3_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_100, c_2])).
% 4.76/2.00  tff(c_36, plain, (![A_40, B_41]: (r1_xboole_0(k1_tarski(A_40), B_41) | r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.76/2.00  tff(c_186, plain, (![A_40, B_41]: (k3_xboole_0(k1_tarski(A_40), B_41)=k1_xboole_0 | r2_hidden(A_40, B_41))), inference(resolution, [status(thm)], [c_36, c_173])).
% 4.76/2.00  tff(c_489, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_107, c_186])).
% 4.76/2.00  tff(c_1290, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1284, c_489])).
% 4.76/2.00  tff(c_44, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.76/2.00  tff(c_3490, plain, (![C_146, B_147, A_148]: (~r2_hidden(C_146, B_147) | ~r2_hidden(C_146, A_148) | k3_xboole_0(A_148, B_147)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_278])).
% 4.76/2.00  tff(c_3509, plain, (![A_149]: (~r2_hidden('#skF_5', A_149) | k3_xboole_0(A_149, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_3490])).
% 4.76/2.00  tff(c_3512, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1290, c_3509])).
% 4.76/2.00  tff(c_3526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_591, c_2, c_3512])).
% 4.76/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.76/2.00  
% 4.76/2.00  Inference rules
% 4.76/2.00  ----------------------
% 4.76/2.00  #Ref     : 0
% 4.76/2.00  #Sup     : 851
% 4.76/2.00  #Fact    : 0
% 4.76/2.00  #Define  : 0
% 4.76/2.00  #Split   : 1
% 4.76/2.00  #Chain   : 0
% 4.76/2.00  #Close   : 0
% 4.76/2.00  
% 4.76/2.00  Ordering : KBO
% 4.76/2.00  
% 4.76/2.00  Simplification rules
% 4.76/2.00  ----------------------
% 4.76/2.00  #Subsume      : 22
% 4.76/2.00  #Demod        : 820
% 4.76/2.00  #Tautology    : 606
% 4.76/2.00  #SimpNegUnit  : 8
% 4.76/2.00  #BackRed      : 0
% 4.76/2.00  
% 4.76/2.00  #Partial instantiations: 0
% 4.76/2.00  #Strategies tried      : 1
% 4.76/2.00  
% 4.76/2.00  Timing (in seconds)
% 4.76/2.00  ----------------------
% 4.76/2.00  Preprocessing        : 0.42
% 4.76/2.00  Parsing              : 0.23
% 4.76/2.00  CNF conversion       : 0.02
% 4.76/2.00  Main loop            : 0.77
% 4.76/2.00  Inferencing          : 0.24
% 4.76/2.00  Reduction            : 0.36
% 4.76/2.00  Demodulation         : 0.31
% 4.76/2.00  BG Simplification    : 0.03
% 4.76/2.00  Subsumption          : 0.10
% 4.76/2.00  Abstraction          : 0.03
% 4.76/2.00  MUC search           : 0.00
% 4.76/2.00  Cooper               : 0.00
% 4.76/2.00  Total                : 1.22
% 4.76/2.00  Index Insertion      : 0.00
% 4.76/2.00  Index Deletion       : 0.00
% 4.76/2.00  Index Matching       : 0.00
% 4.76/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
