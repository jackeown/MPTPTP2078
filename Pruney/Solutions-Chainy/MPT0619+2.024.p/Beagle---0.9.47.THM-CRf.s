%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:54 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 111 expanded)
%              Number of leaves         :   31 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :   86 ( 208 expanded)
%              Number of equality atoms :   43 ( 103 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_50,plain,(
    k1_tarski('#skF_4') = k1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_131,plain,(
    ! [A_45,B_46] :
      ( k9_relat_1(A_45,k1_tarski(B_46)) = k11_relat_1(A_45,B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_150,plain,(
    ! [A_50] :
      ( k9_relat_1(A_50,k1_relat_1('#skF_5')) = k11_relat_1(A_50,'#skF_4')
      | ~ v1_relat_1(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_131])).

tff(c_32,plain,(
    ! [A_19] :
      ( k9_relat_1(A_19,k1_relat_1(A_19)) = k2_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_157,plain,
    ( k11_relat_1('#skF_5','#skF_4') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_32])).

tff(c_167,plain,(
    k11_relat_1('#skF_5','#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_157])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_68,plain,(
    ! [D_29,B_30] : r2_hidden(D_29,k2_tarski(D_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    ! [A_33] : r2_hidden(A_33,k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_68])).

tff(c_79,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_76])).

tff(c_218,plain,(
    ! [B_56,A_57] :
      ( k11_relat_1(B_56,A_57) != k1_xboole_0
      | ~ r2_hidden(A_57,k1_relat_1(B_56))
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_228,plain,
    ( k11_relat_1('#skF_5','#skF_4') != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_79,c_218])).

tff(c_233,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_167,c_228])).

tff(c_28,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),A_13)
      | k1_xboole_0 = A_13
      | k1_tarski(B_14) = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_34,plain,(
    ! [A_20,B_21,C_22] :
      ( r2_hidden(k4_tarski(A_20,B_21),C_22)
      | ~ r2_hidden(B_21,k11_relat_1(C_22,A_20))
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_366,plain,(
    ! [C_67,A_68,B_69] :
      ( k1_funct_1(C_67,A_68) = B_69
      | ~ r2_hidden(k4_tarski(A_68,B_69),C_67)
      | ~ v1_funct_1(C_67)
      | ~ v1_relat_1(C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_476,plain,(
    ! [C_79,A_80,B_81] :
      ( k1_funct_1(C_79,A_80) = B_81
      | ~ v1_funct_1(C_79)
      | ~ r2_hidden(B_81,k11_relat_1(C_79,A_80))
      | ~ v1_relat_1(C_79) ) ),
    inference(resolution,[status(thm)],[c_34,c_366])).

tff(c_490,plain,(
    ! [B_81] :
      ( k1_funct_1('#skF_5','#skF_4') = B_81
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden(B_81,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_476])).

tff(c_497,plain,(
    ! [B_82] :
      ( k1_funct_1('#skF_5','#skF_4') = B_82
      | ~ r2_hidden(B_82,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_490])).

tff(c_505,plain,(
    ! [B_14] :
      ( '#skF_3'(k2_relat_1('#skF_5'),B_14) = k1_funct_1('#skF_5','#skF_4')
      | k2_relat_1('#skF_5') = k1_xboole_0
      | k2_relat_1('#skF_5') = k1_tarski(B_14) ) ),
    inference(resolution,[status(thm)],[c_28,c_497])).

tff(c_992,plain,(
    ! [B_1277] :
      ( '#skF_3'(k2_relat_1('#skF_5'),B_1277) = k1_funct_1('#skF_5','#skF_4')
      | k2_relat_1('#skF_5') = k1_tarski(B_1277) ) ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_505])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( '#skF_3'(A_13,B_14) != B_14
      | k1_xboole_0 = A_13
      | k1_tarski(B_14) = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1000,plain,(
    ! [B_1277] :
      ( k1_funct_1('#skF_5','#skF_4') != B_1277
      | k2_relat_1('#skF_5') = k1_xboole_0
      | k2_relat_1('#skF_5') = k1_tarski(B_1277)
      | k2_relat_1('#skF_5') = k1_tarski(B_1277) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_992,c_26])).

tff(c_1027,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_4')) = k2_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_1000])).

tff(c_48,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_4')) != k2_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1030,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1027,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.43  
% 2.99/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.43  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.99/1.43  
% 2.99/1.43  %Foreground sorts:
% 2.99/1.43  
% 2.99/1.43  
% 2.99/1.43  %Background operators:
% 2.99/1.43  
% 2.99/1.43  
% 2.99/1.43  %Foreground operators:
% 2.99/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.99/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.99/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.99/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.99/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.99/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.99/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.99/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.99/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.99/1.43  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.99/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.99/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.99/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.99/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.99/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.99/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.99/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.99/1.44  
% 2.99/1.45  tff(f_95, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.99/1.45  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.99/1.45  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.99/1.45  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.99/1.45  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.99/1.45  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.99/1.45  tff(f_54, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.99/1.45  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 2.99/1.45  tff(f_86, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.99/1.45  tff(c_54, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.99/1.45  tff(c_50, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.99/1.45  tff(c_131, plain, (![A_45, B_46]: (k9_relat_1(A_45, k1_tarski(B_46))=k11_relat_1(A_45, B_46) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.99/1.45  tff(c_150, plain, (![A_50]: (k9_relat_1(A_50, k1_relat_1('#skF_5'))=k11_relat_1(A_50, '#skF_4') | ~v1_relat_1(A_50))), inference(superposition, [status(thm), theory('equality')], [c_50, c_131])).
% 2.99/1.45  tff(c_32, plain, (![A_19]: (k9_relat_1(A_19, k1_relat_1(A_19))=k2_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.99/1.45  tff(c_157, plain, (k11_relat_1('#skF_5', '#skF_4')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_150, c_32])).
% 2.99/1.45  tff(c_167, plain, (k11_relat_1('#skF_5', '#skF_4')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_157])).
% 2.99/1.45  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.99/1.45  tff(c_68, plain, (![D_29, B_30]: (r2_hidden(D_29, k2_tarski(D_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.99/1.45  tff(c_76, plain, (![A_33]: (r2_hidden(A_33, k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_68])).
% 2.99/1.45  tff(c_79, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_76])).
% 2.99/1.45  tff(c_218, plain, (![B_56, A_57]: (k11_relat_1(B_56, A_57)!=k1_xboole_0 | ~r2_hidden(A_57, k1_relat_1(B_56)) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.99/1.45  tff(c_228, plain, (k11_relat_1('#skF_5', '#skF_4')!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_79, c_218])).
% 2.99/1.45  tff(c_233, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_167, c_228])).
% 2.99/1.45  tff(c_28, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), A_13) | k1_xboole_0=A_13 | k1_tarski(B_14)=A_13)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.99/1.45  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.99/1.45  tff(c_34, plain, (![A_20, B_21, C_22]: (r2_hidden(k4_tarski(A_20, B_21), C_22) | ~r2_hidden(B_21, k11_relat_1(C_22, A_20)) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.99/1.45  tff(c_366, plain, (![C_67, A_68, B_69]: (k1_funct_1(C_67, A_68)=B_69 | ~r2_hidden(k4_tarski(A_68, B_69), C_67) | ~v1_funct_1(C_67) | ~v1_relat_1(C_67))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.99/1.45  tff(c_476, plain, (![C_79, A_80, B_81]: (k1_funct_1(C_79, A_80)=B_81 | ~v1_funct_1(C_79) | ~r2_hidden(B_81, k11_relat_1(C_79, A_80)) | ~v1_relat_1(C_79))), inference(resolution, [status(thm)], [c_34, c_366])).
% 2.99/1.45  tff(c_490, plain, (![B_81]: (k1_funct_1('#skF_5', '#skF_4')=B_81 | ~v1_funct_1('#skF_5') | ~r2_hidden(B_81, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_167, c_476])).
% 2.99/1.45  tff(c_497, plain, (![B_82]: (k1_funct_1('#skF_5', '#skF_4')=B_82 | ~r2_hidden(B_82, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_490])).
% 2.99/1.45  tff(c_505, plain, (![B_14]: ('#skF_3'(k2_relat_1('#skF_5'), B_14)=k1_funct_1('#skF_5', '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')=k1_tarski(B_14))), inference(resolution, [status(thm)], [c_28, c_497])).
% 2.99/1.45  tff(c_992, plain, (![B_1277]: ('#skF_3'(k2_relat_1('#skF_5'), B_1277)=k1_funct_1('#skF_5', '#skF_4') | k2_relat_1('#skF_5')=k1_tarski(B_1277))), inference(negUnitSimplification, [status(thm)], [c_233, c_505])).
% 2.99/1.45  tff(c_26, plain, (![A_13, B_14]: ('#skF_3'(A_13, B_14)!=B_14 | k1_xboole_0=A_13 | k1_tarski(B_14)=A_13)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.99/1.45  tff(c_1000, plain, (![B_1277]: (k1_funct_1('#skF_5', '#skF_4')!=B_1277 | k2_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')=k1_tarski(B_1277) | k2_relat_1('#skF_5')=k1_tarski(B_1277))), inference(superposition, [status(thm), theory('equality')], [c_992, c_26])).
% 2.99/1.45  tff(c_1027, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_4'))=k2_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_233, c_1000])).
% 2.99/1.45  tff(c_48, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_4'))!=k2_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.99/1.45  tff(c_1030, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1027, c_48])).
% 2.99/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.45  
% 2.99/1.45  Inference rules
% 2.99/1.45  ----------------------
% 2.99/1.45  #Ref     : 0
% 2.99/1.45  #Sup     : 196
% 2.99/1.45  #Fact    : 0
% 2.99/1.45  #Define  : 0
% 2.99/1.45  #Split   : 2
% 2.99/1.45  #Chain   : 0
% 2.99/1.45  #Close   : 0
% 2.99/1.45  
% 2.99/1.45  Ordering : KBO
% 2.99/1.45  
% 2.99/1.45  Simplification rules
% 2.99/1.45  ----------------------
% 2.99/1.45  #Subsume      : 33
% 2.99/1.45  #Demod        : 45
% 2.99/1.45  #Tautology    : 57
% 2.99/1.45  #SimpNegUnit  : 6
% 2.99/1.45  #BackRed      : 5
% 2.99/1.45  
% 2.99/1.45  #Partial instantiations: 672
% 2.99/1.45  #Strategies tried      : 1
% 2.99/1.45  
% 2.99/1.45  Timing (in seconds)
% 2.99/1.45  ----------------------
% 2.99/1.45  Preprocessing        : 0.32
% 2.99/1.45  Parsing              : 0.16
% 2.99/1.45  CNF conversion       : 0.02
% 2.99/1.45  Main loop            : 0.36
% 2.99/1.45  Inferencing          : 0.15
% 2.99/1.45  Reduction            : 0.10
% 2.99/1.45  Demodulation         : 0.07
% 2.99/1.45  BG Simplification    : 0.02
% 2.99/1.45  Subsumption          : 0.07
% 2.99/1.45  Abstraction          : 0.02
% 2.99/1.45  MUC search           : 0.00
% 2.99/1.45  Cooper               : 0.00
% 2.99/1.45  Total                : 0.71
% 2.99/1.45  Index Insertion      : 0.00
% 2.99/1.45  Index Deletion       : 0.00
% 2.99/1.45  Index Matching       : 0.00
% 2.99/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
