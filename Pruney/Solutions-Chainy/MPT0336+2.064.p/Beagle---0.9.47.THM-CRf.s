%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:09 EST 2020

% Result     : Theorem 5.14s
% Output     : CNFRefutation 5.45s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 125 expanded)
%              Number of leaves         :   30 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 193 expanded)
%              Number of equality atoms :   27 (  59 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_79,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_53,axiom,(
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

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_40,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_123,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = k1_xboole_0
      | ~ r1_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_143,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_123])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_142,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_123])).

tff(c_28,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1053,plain,(
    ! [A_99,C_100,B_101] :
      ( r1_xboole_0(k2_tarski(A_99,C_100),B_101)
      | r2_hidden(C_100,B_101)
      | r2_hidden(A_99,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2090,plain,(
    ! [A_124,B_125] :
      ( r1_xboole_0(k1_tarski(A_124),B_125)
      | r2_hidden(A_124,B_125)
      | r2_hidden(A_124,B_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1053])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2116,plain,(
    ! [B_126,A_127] :
      ( r1_xboole_0(B_126,k1_tarski(A_127))
      | r2_hidden(A_127,B_126) ) ),
    inference(resolution,[status(thm)],[c_2090,c_8])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2125,plain,(
    ! [B_126,A_127] :
      ( k3_xboole_0(B_126,k1_tarski(A_127)) = k1_xboole_0
      | r2_hidden(A_127,B_126) ) ),
    inference(resolution,[status(thm)],[c_2116,c_4])).

tff(c_44,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_45,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_165,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_169,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_45,c_165])).

tff(c_480,plain,(
    ! [A_85,B_86,C_87] : k3_xboole_0(k3_xboole_0(A_85,B_86),C_87) = k3_xboole_0(A_85,k3_xboole_0(B_86,C_87)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2426,plain,(
    ! [A_135,B_136,C_137] : k3_xboole_0(k3_xboole_0(A_135,B_136),C_137) = k3_xboole_0(B_136,k3_xboole_0(A_135,C_137)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_480])).

tff(c_2669,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_3',k1_tarski('#skF_5'))) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_2426])).

tff(c_2769,plain,
    ( k3_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_2')
    | r2_hidden('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2125,c_2669])).

tff(c_2777,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_2769])).

tff(c_2778,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2777])).

tff(c_42,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_382,plain,(
    ! [A_71,B_72,C_73] :
      ( ~ r1_xboole_0(A_71,B_72)
      | ~ r2_hidden(C_73,B_72)
      | ~ r2_hidden(C_73,A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1587,plain,(
    ! [C_112,B_113,A_114] :
      ( ~ r2_hidden(C_112,B_113)
      | ~ r2_hidden(C_112,A_114)
      | k3_xboole_0(A_114,B_113) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_382])).

tff(c_1596,plain,(
    ! [A_114] :
      ( ~ r2_hidden('#skF_5',A_114)
      | k3_xboole_0(A_114,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_1587])).

tff(c_2784,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2778,c_1596])).

tff(c_2794,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_2,c_2784])).

tff(c_2795,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2777])).

tff(c_105,plain,(
    ! [A_39,B_40] :
      ( r1_xboole_0(A_39,B_40)
      | k3_xboole_0(A_39,B_40) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    ! [B_40,A_39] :
      ( r1_xboole_0(B_40,A_39)
      | k3_xboole_0(A_39,B_40) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_105,c_8])).

tff(c_56,plain,(
    ! [B_34,A_35] :
      ( r1_xboole_0(B_34,A_35)
      | ~ r1_xboole_0(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_56])).

tff(c_860,plain,(
    ! [A_94,C_95,B_96] :
      ( ~ r1_xboole_0(A_94,C_95)
      | ~ r1_xboole_0(A_94,B_96)
      | r1_xboole_0(A_94,k2_xboole_0(B_96,C_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5619,plain,(
    ! [B_162,C_163,A_164] :
      ( r1_xboole_0(k2_xboole_0(B_162,C_163),A_164)
      | ~ r1_xboole_0(A_164,C_163)
      | ~ r1_xboole_0(A_164,B_162) ) ),
    inference(resolution,[status(thm)],[c_860,c_8])).

tff(c_38,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_5641,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_5619,c_38])).

tff(c_5653,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5641])).

tff(c_5656,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111,c_5653])).

tff(c_5663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2795,c_2,c_5656])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.14/2.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.14/2.03  
% 5.14/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.14/2.03  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.14/2.03  
% 5.14/2.03  %Foreground sorts:
% 5.14/2.03  
% 5.14/2.03  
% 5.14/2.03  %Background operators:
% 5.14/2.03  
% 5.14/2.03  
% 5.14/2.03  %Foreground operators:
% 5.14/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.14/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.14/2.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.14/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.14/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.14/2.03  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.14/2.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.14/2.03  tff('#skF_5', type, '#skF_5': $i).
% 5.14/2.03  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.14/2.03  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.14/2.03  tff('#skF_2', type, '#skF_2': $i).
% 5.14/2.03  tff('#skF_3', type, '#skF_3': $i).
% 5.14/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.14/2.03  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.14/2.03  tff('#skF_4', type, '#skF_4': $i).
% 5.14/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.14/2.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.14/2.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.14/2.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.14/2.03  
% 5.45/2.04  tff(f_104, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 5.45/2.04  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.45/2.04  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.45/2.04  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.45/2.04  tff(f_79, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.45/2.04  tff(f_95, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 5.45/2.04  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.45/2.04  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.45/2.04  tff(f_55, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 5.45/2.04  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.45/2.04  tff(f_77, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 5.45/2.04  tff(c_40, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.45/2.04  tff(c_123, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=k1_xboole_0 | ~r1_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.45/2.04  tff(c_143, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_123])).
% 5.45/2.04  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.45/2.04  tff(c_20, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.45/2.04  tff(c_142, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_123])).
% 5.45/2.04  tff(c_28, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.45/2.04  tff(c_1053, plain, (![A_99, C_100, B_101]: (r1_xboole_0(k2_tarski(A_99, C_100), B_101) | r2_hidden(C_100, B_101) | r2_hidden(A_99, B_101))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.45/2.04  tff(c_2090, plain, (![A_124, B_125]: (r1_xboole_0(k1_tarski(A_124), B_125) | r2_hidden(A_124, B_125) | r2_hidden(A_124, B_125))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1053])).
% 5.45/2.04  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.45/2.04  tff(c_2116, plain, (![B_126, A_127]: (r1_xboole_0(B_126, k1_tarski(A_127)) | r2_hidden(A_127, B_126))), inference(resolution, [status(thm)], [c_2090, c_8])).
% 5.45/2.04  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.45/2.04  tff(c_2125, plain, (![B_126, A_127]: (k3_xboole_0(B_126, k1_tarski(A_127))=k1_xboole_0 | r2_hidden(A_127, B_126))), inference(resolution, [status(thm)], [c_2116, c_4])).
% 5.45/2.04  tff(c_44, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.45/2.04  tff(c_45, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_44])).
% 5.45/2.04  tff(c_165, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=A_46 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.45/2.04  tff(c_169, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_45, c_165])).
% 5.45/2.04  tff(c_480, plain, (![A_85, B_86, C_87]: (k3_xboole_0(k3_xboole_0(A_85, B_86), C_87)=k3_xboole_0(A_85, k3_xboole_0(B_86, C_87)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.45/2.04  tff(c_2426, plain, (![A_135, B_136, C_137]: (k3_xboole_0(k3_xboole_0(A_135, B_136), C_137)=k3_xboole_0(B_136, k3_xboole_0(A_135, C_137)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_480])).
% 5.45/2.04  tff(c_2669, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_3', k1_tarski('#skF_5')))=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_169, c_2426])).
% 5.45/2.04  tff(c_2769, plain, (k3_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_2') | r2_hidden('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2125, c_2669])).
% 5.45/2.04  tff(c_2777, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_2769])).
% 5.45/2.04  tff(c_2778, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_2777])).
% 5.45/2.04  tff(c_42, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.45/2.04  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.45/2.04  tff(c_382, plain, (![A_71, B_72, C_73]: (~r1_xboole_0(A_71, B_72) | ~r2_hidden(C_73, B_72) | ~r2_hidden(C_73, A_71))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.45/2.04  tff(c_1587, plain, (![C_112, B_113, A_114]: (~r2_hidden(C_112, B_113) | ~r2_hidden(C_112, A_114) | k3_xboole_0(A_114, B_113)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_382])).
% 5.45/2.04  tff(c_1596, plain, (![A_114]: (~r2_hidden('#skF_5', A_114) | k3_xboole_0(A_114, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_1587])).
% 5.45/2.04  tff(c_2784, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2778, c_1596])).
% 5.45/2.04  tff(c_2794, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_2, c_2784])).
% 5.45/2.04  tff(c_2795, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2777])).
% 5.45/2.04  tff(c_105, plain, (![A_39, B_40]: (r1_xboole_0(A_39, B_40) | k3_xboole_0(A_39, B_40)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.45/2.04  tff(c_111, plain, (![B_40, A_39]: (r1_xboole_0(B_40, A_39) | k3_xboole_0(A_39, B_40)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_105, c_8])).
% 5.45/2.04  tff(c_56, plain, (![B_34, A_35]: (r1_xboole_0(B_34, A_35) | ~r1_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.45/2.04  tff(c_62, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_56])).
% 5.45/2.04  tff(c_860, plain, (![A_94, C_95, B_96]: (~r1_xboole_0(A_94, C_95) | ~r1_xboole_0(A_94, B_96) | r1_xboole_0(A_94, k2_xboole_0(B_96, C_95)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.45/2.04  tff(c_5619, plain, (![B_162, C_163, A_164]: (r1_xboole_0(k2_xboole_0(B_162, C_163), A_164) | ~r1_xboole_0(A_164, C_163) | ~r1_xboole_0(A_164, B_162))), inference(resolution, [status(thm)], [c_860, c_8])).
% 5.45/2.04  tff(c_38, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.45/2.04  tff(c_5641, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_5619, c_38])).
% 5.45/2.04  tff(c_5653, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5641])).
% 5.45/2.04  tff(c_5656, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_111, c_5653])).
% 5.45/2.04  tff(c_5663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2795, c_2, c_5656])).
% 5.45/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.45/2.04  
% 5.45/2.04  Inference rules
% 5.45/2.04  ----------------------
% 5.45/2.04  #Ref     : 0
% 5.45/2.04  #Sup     : 1432
% 5.45/2.04  #Fact    : 0
% 5.45/2.04  #Define  : 0
% 5.45/2.04  #Split   : 2
% 5.45/2.04  #Chain   : 0
% 5.45/2.04  #Close   : 0
% 5.45/2.04  
% 5.45/2.04  Ordering : KBO
% 5.45/2.04  
% 5.45/2.04  Simplification rules
% 5.45/2.04  ----------------------
% 5.45/2.04  #Subsume      : 30
% 5.45/2.04  #Demod        : 1405
% 5.45/2.04  #Tautology    : 1036
% 5.45/2.04  #SimpNegUnit  : 0
% 5.45/2.04  #BackRed      : 5
% 5.45/2.04  
% 5.45/2.04  #Partial instantiations: 0
% 5.45/2.04  #Strategies tried      : 1
% 5.45/2.04  
% 5.45/2.04  Timing (in seconds)
% 5.45/2.04  ----------------------
% 5.45/2.05  Preprocessing        : 0.30
% 5.45/2.05  Parsing              : 0.16
% 5.45/2.05  CNF conversion       : 0.02
% 5.45/2.05  Main loop            : 0.94
% 5.45/2.05  Inferencing          : 0.27
% 5.45/2.05  Reduction            : 0.45
% 5.45/2.05  Demodulation         : 0.39
% 5.45/2.05  BG Simplification    : 0.03
% 5.45/2.05  Subsumption          : 0.13
% 5.45/2.05  Abstraction          : 0.04
% 5.45/2.05  MUC search           : 0.00
% 5.45/2.05  Cooper               : 0.00
% 5.45/2.05  Total                : 1.27
% 5.45/2.05  Index Insertion      : 0.00
% 5.45/2.05  Index Deletion       : 0.00
% 5.45/2.05  Index Matching       : 0.00
% 5.45/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
