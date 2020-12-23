%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:54 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 130 expanded)
%              Number of leaves         :   35 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :   98 ( 232 expanded)
%              Number of equality atoms :   52 ( 121 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_74,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_70,plain,(
    k1_tarski('#skF_4') = k1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_121,plain,(
    ! [A_69,B_70] :
      ( k9_relat_1(A_69,k1_tarski(B_70)) = k11_relat_1(A_69,B_70)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_134,plain,(
    ! [A_73] :
      ( k9_relat_1(A_73,k1_relat_1('#skF_5')) = k11_relat_1(A_73,'#skF_4')
      | ~ v1_relat_1(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_121])).

tff(c_52,plain,(
    ! [A_26] :
      ( k9_relat_1(A_26,k1_relat_1(A_26)) = k2_relat_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_141,plain,
    ( k11_relat_1('#skF_5','#skF_4') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_52])).

tff(c_151,plain,(
    k11_relat_1('#skF_5','#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_141])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_171,plain,(
    ! [A_78,B_79,C_80,D_81] : k3_enumset1(A_78,A_78,B_79,C_80,D_81) = k2_enumset1(A_78,B_79,C_80,D_81) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [E_18,C_16,G_22,D_17,A_14] : r2_hidden(G_22,k3_enumset1(A_14,G_22,C_16,D_17,E_18)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_195,plain,(
    ! [A_82,B_83,C_84,D_85] : r2_hidden(A_82,k2_enumset1(A_82,B_83,C_84,D_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_22])).

tff(c_199,plain,(
    ! [A_86,B_87,C_88] : r2_hidden(A_86,k1_enumset1(A_86,B_87,C_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_195])).

tff(c_203,plain,(
    ! [A_89,B_90] : r2_hidden(A_89,k2_tarski(A_89,B_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_199])).

tff(c_213,plain,(
    ! [A_94] : r2_hidden(A_94,k1_tarski(A_94)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_203])).

tff(c_216,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_213])).

tff(c_60,plain,(
    ! [B_31,A_30] :
      ( k11_relat_1(B_31,A_30) != k1_xboole_0
      | ~ r2_hidden(A_30,k1_relat_1(B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_219,plain,
    ( k11_relat_1('#skF_5','#skF_4') != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_216,c_60])).

tff(c_222,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_151,c_219])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_1'(A_11,B_12),A_11)
      | k1_xboole_0 = A_11
      | k1_tarski(B_12) = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_72,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_54,plain,(
    ! [A_27,B_28,C_29] :
      ( r2_hidden(k4_tarski(A_27,B_28),C_29)
      | ~ r2_hidden(B_28,k11_relat_1(C_29,A_27))
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_317,plain,(
    ! [C_111,A_112,B_113] :
      ( k1_funct_1(C_111,A_112) = B_113
      | ~ r2_hidden(k4_tarski(A_112,B_113),C_111)
      | ~ v1_funct_1(C_111)
      | ~ v1_relat_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_525,plain,(
    ! [C_126,A_127,B_128] :
      ( k1_funct_1(C_126,A_127) = B_128
      | ~ v1_funct_1(C_126)
      | ~ r2_hidden(B_128,k11_relat_1(C_126,A_127))
      | ~ v1_relat_1(C_126) ) ),
    inference(resolution,[status(thm)],[c_54,c_317])).

tff(c_536,plain,(
    ! [B_128] :
      ( k1_funct_1('#skF_5','#skF_4') = B_128
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden(B_128,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_525])).

tff(c_546,plain,(
    ! [B_129] :
      ( k1_funct_1('#skF_5','#skF_4') = B_129
      | ~ r2_hidden(B_129,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_536])).

tff(c_558,plain,(
    ! [B_12] :
      ( '#skF_1'(k2_relat_1('#skF_5'),B_12) = k1_funct_1('#skF_5','#skF_4')
      | k2_relat_1('#skF_5') = k1_xboole_0
      | k2_relat_1('#skF_5') = k1_tarski(B_12) ) ),
    inference(resolution,[status(thm)],[c_12,c_546])).

tff(c_564,plain,(
    ! [B_130] :
      ( '#skF_1'(k2_relat_1('#skF_5'),B_130) = k1_funct_1('#skF_5','#skF_4')
      | k2_relat_1('#skF_5') = k1_tarski(B_130) ) ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_558])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( '#skF_1'(A_11,B_12) != B_12
      | k1_xboole_0 = A_11
      | k1_tarski(B_12) = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_572,plain,(
    ! [B_130] :
      ( k1_funct_1('#skF_5','#skF_4') != B_130
      | k2_relat_1('#skF_5') = k1_xboole_0
      | k2_relat_1('#skF_5') = k1_tarski(B_130)
      | k2_relat_1('#skF_5') = k1_tarski(B_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_10])).

tff(c_580,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_4')) = k2_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_572])).

tff(c_68,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_4')) != k2_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.42  
% 2.66/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.42  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.66/1.42  
% 2.66/1.42  %Foreground sorts:
% 2.66/1.42  
% 2.66/1.42  
% 2.66/1.42  %Background operators:
% 2.66/1.42  
% 2.66/1.42  
% 2.66/1.42  %Foreground operators:
% 2.66/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.66/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.66/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.66/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.66/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.66/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.66/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.66/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.66/1.42  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.66/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.66/1.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.66/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.66/1.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.66/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.66/1.42  
% 2.66/1.44  tff(f_109, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.66/1.44  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.66/1.44  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.66/1.44  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.66/1.44  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.66/1.44  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.66/1.44  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.66/1.44  tff(f_68, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 2.66/1.44  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 2.66/1.44  tff(f_47, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 2.66/1.44  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.66/1.44  tff(f_100, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.66/1.44  tff(c_74, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.66/1.44  tff(c_70, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.66/1.44  tff(c_121, plain, (![A_69, B_70]: (k9_relat_1(A_69, k1_tarski(B_70))=k11_relat_1(A_69, B_70) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.66/1.44  tff(c_134, plain, (![A_73]: (k9_relat_1(A_73, k1_relat_1('#skF_5'))=k11_relat_1(A_73, '#skF_4') | ~v1_relat_1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_70, c_121])).
% 2.66/1.44  tff(c_52, plain, (![A_26]: (k9_relat_1(A_26, k1_relat_1(A_26))=k2_relat_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.66/1.44  tff(c_141, plain, (k11_relat_1('#skF_5', '#skF_4')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_134, c_52])).
% 2.66/1.44  tff(c_151, plain, (k11_relat_1('#skF_5', '#skF_4')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_141])).
% 2.66/1.44  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.66/1.44  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.66/1.44  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.44  tff(c_171, plain, (![A_78, B_79, C_80, D_81]: (k3_enumset1(A_78, A_78, B_79, C_80, D_81)=k2_enumset1(A_78, B_79, C_80, D_81))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.66/1.44  tff(c_22, plain, (![E_18, C_16, G_22, D_17, A_14]: (r2_hidden(G_22, k3_enumset1(A_14, G_22, C_16, D_17, E_18)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.66/1.44  tff(c_195, plain, (![A_82, B_83, C_84, D_85]: (r2_hidden(A_82, k2_enumset1(A_82, B_83, C_84, D_85)))), inference(superposition, [status(thm), theory('equality')], [c_171, c_22])).
% 2.66/1.44  tff(c_199, plain, (![A_86, B_87, C_88]: (r2_hidden(A_86, k1_enumset1(A_86, B_87, C_88)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_195])).
% 2.66/1.44  tff(c_203, plain, (![A_89, B_90]: (r2_hidden(A_89, k2_tarski(A_89, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_199])).
% 2.66/1.44  tff(c_213, plain, (![A_94]: (r2_hidden(A_94, k1_tarski(A_94)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_203])).
% 2.66/1.44  tff(c_216, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_213])).
% 2.66/1.44  tff(c_60, plain, (![B_31, A_30]: (k11_relat_1(B_31, A_30)!=k1_xboole_0 | ~r2_hidden(A_30, k1_relat_1(B_31)) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.66/1.44  tff(c_219, plain, (k11_relat_1('#skF_5', '#skF_4')!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_216, c_60])).
% 2.66/1.44  tff(c_222, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_74, c_151, c_219])).
% 2.66/1.44  tff(c_12, plain, (![A_11, B_12]: (r2_hidden('#skF_1'(A_11, B_12), A_11) | k1_xboole_0=A_11 | k1_tarski(B_12)=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.66/1.44  tff(c_72, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.66/1.44  tff(c_54, plain, (![A_27, B_28, C_29]: (r2_hidden(k4_tarski(A_27, B_28), C_29) | ~r2_hidden(B_28, k11_relat_1(C_29, A_27)) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.66/1.44  tff(c_317, plain, (![C_111, A_112, B_113]: (k1_funct_1(C_111, A_112)=B_113 | ~r2_hidden(k4_tarski(A_112, B_113), C_111) | ~v1_funct_1(C_111) | ~v1_relat_1(C_111))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.66/1.44  tff(c_525, plain, (![C_126, A_127, B_128]: (k1_funct_1(C_126, A_127)=B_128 | ~v1_funct_1(C_126) | ~r2_hidden(B_128, k11_relat_1(C_126, A_127)) | ~v1_relat_1(C_126))), inference(resolution, [status(thm)], [c_54, c_317])).
% 2.66/1.44  tff(c_536, plain, (![B_128]: (k1_funct_1('#skF_5', '#skF_4')=B_128 | ~v1_funct_1('#skF_5') | ~r2_hidden(B_128, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_525])).
% 2.66/1.44  tff(c_546, plain, (![B_129]: (k1_funct_1('#skF_5', '#skF_4')=B_129 | ~r2_hidden(B_129, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_536])).
% 2.66/1.44  tff(c_558, plain, (![B_12]: ('#skF_1'(k2_relat_1('#skF_5'), B_12)=k1_funct_1('#skF_5', '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')=k1_tarski(B_12))), inference(resolution, [status(thm)], [c_12, c_546])).
% 2.66/1.44  tff(c_564, plain, (![B_130]: ('#skF_1'(k2_relat_1('#skF_5'), B_130)=k1_funct_1('#skF_5', '#skF_4') | k2_relat_1('#skF_5')=k1_tarski(B_130))), inference(negUnitSimplification, [status(thm)], [c_222, c_558])).
% 2.66/1.44  tff(c_10, plain, (![A_11, B_12]: ('#skF_1'(A_11, B_12)!=B_12 | k1_xboole_0=A_11 | k1_tarski(B_12)=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.66/1.44  tff(c_572, plain, (![B_130]: (k1_funct_1('#skF_5', '#skF_4')!=B_130 | k2_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')=k1_tarski(B_130) | k2_relat_1('#skF_5')=k1_tarski(B_130))), inference(superposition, [status(thm), theory('equality')], [c_564, c_10])).
% 2.66/1.44  tff(c_580, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_4'))=k2_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_222, c_572])).
% 2.66/1.44  tff(c_68, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_4'))!=k2_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.66/1.44  tff(c_583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_580, c_68])).
% 2.66/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.44  
% 2.66/1.44  Inference rules
% 2.66/1.44  ----------------------
% 2.66/1.44  #Ref     : 0
% 2.66/1.44  #Sup     : 106
% 2.66/1.44  #Fact    : 0
% 2.66/1.44  #Define  : 0
% 2.66/1.44  #Split   : 0
% 2.66/1.44  #Chain   : 0
% 2.66/1.44  #Close   : 0
% 2.66/1.44  
% 2.66/1.44  Ordering : KBO
% 2.66/1.44  
% 2.66/1.44  Simplification rules
% 2.66/1.44  ----------------------
% 2.66/1.44  #Subsume      : 0
% 2.66/1.44  #Demod        : 14
% 2.66/1.44  #Tautology    : 29
% 2.66/1.44  #SimpNegUnit  : 3
% 2.66/1.44  #BackRed      : 1
% 2.66/1.44  
% 2.66/1.44  #Partial instantiations: 0
% 2.66/1.44  #Strategies tried      : 1
% 2.66/1.44  
% 2.66/1.44  Timing (in seconds)
% 2.66/1.44  ----------------------
% 2.66/1.44  Preprocessing        : 0.32
% 2.66/1.44  Parsing              : 0.15
% 2.66/1.44  CNF conversion       : 0.03
% 2.66/1.44  Main loop            : 0.29
% 2.66/1.44  Inferencing          : 0.10
% 2.66/1.44  Reduction            : 0.09
% 2.66/1.44  Demodulation         : 0.06
% 2.66/1.44  BG Simplification    : 0.02
% 2.66/1.44  Subsumption          : 0.06
% 2.66/1.44  Abstraction          : 0.02
% 2.66/1.44  MUC search           : 0.00
% 2.66/1.44  Cooper               : 0.00
% 2.66/1.44  Total                : 0.65
% 2.66/1.44  Index Insertion      : 0.00
% 2.66/1.44  Index Deletion       : 0.00
% 2.66/1.44  Index Matching       : 0.00
% 2.66/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
