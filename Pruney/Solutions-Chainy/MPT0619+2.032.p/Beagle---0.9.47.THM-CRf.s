%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:55 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 130 expanded)
%              Number of leaves         :   34 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  102 ( 250 expanded)
%              Number of equality atoms :   42 ( 105 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_44,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_115,plain,(
    ! [A_51,B_52] :
      ( k9_relat_1(A_51,k1_tarski(B_52)) = k11_relat_1(A_51,B_52)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_128,plain,(
    ! [A_55] :
      ( k9_relat_1(A_55,k1_relat_1('#skF_3')) = k11_relat_1(A_55,'#skF_2')
      | ~ v1_relat_1(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_115])).

tff(c_22,plain,(
    ! [A_20] :
      ( k9_relat_1(A_20,k1_relat_1(A_20)) = k2_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_135,plain,
    ( k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_22])).

tff(c_145,plain,(
    k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_135])).

tff(c_34,plain,(
    ! [A_28] :
      ( k7_relat_1(A_28,k1_relat_1(A_28)) = A_28
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_89,plain,(
    ! [B_37,A_38] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_37,A_38)),A_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_155,plain,(
    ! [A_58] :
      ( r1_tarski(k1_relat_1(A_58),k1_relat_1(A_58))
      | ~ v1_relat_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_89])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_93,plain,(
    ! [B_39,C_40,A_41] :
      ( r2_hidden(B_39,C_40)
      | ~ r1_tarski(k2_tarski(A_41,B_39),C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_97,plain,(
    ! [A_42,C_43] :
      ( r2_hidden(A_42,C_43)
      | ~ r1_tarski(k1_tarski(A_42),C_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_93])).

tff(c_100,plain,(
    ! [C_43] :
      ( r2_hidden('#skF_2',C_43)
      | ~ r1_tarski(k1_relat_1('#skF_3'),C_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_97])).

tff(c_159,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_155,c_100])).

tff(c_162,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_159])).

tff(c_163,plain,(
    ! [B_59,A_60] :
      ( k11_relat_1(B_59,A_60) != k1_xboole_0
      | ~ r2_hidden(A_60,k1_relat_1(B_59))
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_166,plain,
    ( k11_relat_1('#skF_3','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_162,c_163])).

tff(c_173,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_145,c_166])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_1'(A_14,B_15),A_14)
      | k1_xboole_0 = A_14
      | k1_tarski(B_15) = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_24,plain,(
    ! [A_21,B_22,C_23] :
      ( r2_hidden(k4_tarski(A_21,B_22),C_23)
      | ~ r2_hidden(B_22,k11_relat_1(C_23,A_21))
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_240,plain,(
    ! [C_82,A_83,B_84] :
      ( k1_funct_1(C_82,A_83) = B_84
      | ~ r2_hidden(k4_tarski(A_83,B_84),C_82)
      | ~ v1_funct_1(C_82)
      | ~ v1_relat_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_263,plain,(
    ! [C_88,A_89,B_90] :
      ( k1_funct_1(C_88,A_89) = B_90
      | ~ v1_funct_1(C_88)
      | ~ r2_hidden(B_90,k11_relat_1(C_88,A_89))
      | ~ v1_relat_1(C_88) ) ),
    inference(resolution,[status(thm)],[c_24,c_240])).

tff(c_274,plain,(
    ! [B_90] :
      ( k1_funct_1('#skF_3','#skF_2') = B_90
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden(B_90,k2_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_263])).

tff(c_307,plain,(
    ! [B_93] :
      ( k1_funct_1('#skF_3','#skF_2') = B_93
      | ~ r2_hidden(B_93,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_274])).

tff(c_319,plain,(
    ! [B_15] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_15) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_15) ) ),
    inference(resolution,[status(thm)],[c_18,c_307])).

tff(c_325,plain,(
    ! [B_94] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_94) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_tarski(B_94) ) ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_319])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( '#skF_1'(A_14,B_15) != B_15
      | k1_xboole_0 = A_14
      | k1_tarski(B_15) = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_333,plain,(
    ! [B_94] :
      ( k1_funct_1('#skF_3','#skF_2') != B_94
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_94)
      | k2_relat_1('#skF_3') = k1_tarski(B_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_16])).

tff(c_341,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) = k2_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_333])).

tff(c_42,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k2_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.24  
% 2.24/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.24  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.24/1.24  
% 2.24/1.24  %Foreground sorts:
% 2.24/1.24  
% 2.24/1.24  
% 2.24/1.24  %Background operators:
% 2.24/1.24  
% 2.24/1.24  
% 2.24/1.24  %Foreground operators:
% 2.24/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.24/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.24/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.24/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.24/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.24/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.24  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.24/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.24/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.24/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.24/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.24/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.24/1.24  
% 2.33/1.26  tff(f_102, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.33/1.26  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.33/1.26  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.33/1.26  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.33/1.26  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.33/1.26  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.33/1.26  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.33/1.26  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.33/1.26  tff(f_53, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.33/1.26  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 2.33/1.26  tff(f_93, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.33/1.26  tff(c_48, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.33/1.26  tff(c_44, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.33/1.26  tff(c_115, plain, (![A_51, B_52]: (k9_relat_1(A_51, k1_tarski(B_52))=k11_relat_1(A_51, B_52) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.33/1.26  tff(c_128, plain, (![A_55]: (k9_relat_1(A_55, k1_relat_1('#skF_3'))=k11_relat_1(A_55, '#skF_2') | ~v1_relat_1(A_55))), inference(superposition, [status(thm), theory('equality')], [c_44, c_115])).
% 2.33/1.26  tff(c_22, plain, (![A_20]: (k9_relat_1(A_20, k1_relat_1(A_20))=k2_relat_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.33/1.26  tff(c_135, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_128, c_22])).
% 2.33/1.26  tff(c_145, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_135])).
% 2.33/1.26  tff(c_34, plain, (![A_28]: (k7_relat_1(A_28, k1_relat_1(A_28))=A_28 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.33/1.26  tff(c_89, plain, (![B_37, A_38]: (r1_tarski(k1_relat_1(k7_relat_1(B_37, A_38)), A_38) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.33/1.26  tff(c_155, plain, (![A_58]: (r1_tarski(k1_relat_1(A_58), k1_relat_1(A_58)) | ~v1_relat_1(A_58) | ~v1_relat_1(A_58))), inference(superposition, [status(thm), theory('equality')], [c_34, c_89])).
% 2.33/1.26  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.33/1.26  tff(c_93, plain, (![B_39, C_40, A_41]: (r2_hidden(B_39, C_40) | ~r1_tarski(k2_tarski(A_41, B_39), C_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.33/1.26  tff(c_97, plain, (![A_42, C_43]: (r2_hidden(A_42, C_43) | ~r1_tarski(k1_tarski(A_42), C_43))), inference(superposition, [status(thm), theory('equality')], [c_2, c_93])).
% 2.33/1.26  tff(c_100, plain, (![C_43]: (r2_hidden('#skF_2', C_43) | ~r1_tarski(k1_relat_1('#skF_3'), C_43))), inference(superposition, [status(thm), theory('equality')], [c_44, c_97])).
% 2.33/1.26  tff(c_159, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_155, c_100])).
% 2.33/1.26  tff(c_162, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_159])).
% 2.33/1.26  tff(c_163, plain, (![B_59, A_60]: (k11_relat_1(B_59, A_60)!=k1_xboole_0 | ~r2_hidden(A_60, k1_relat_1(B_59)) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.33/1.26  tff(c_166, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_162, c_163])).
% 2.33/1.26  tff(c_173, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_145, c_166])).
% 2.33/1.26  tff(c_18, plain, (![A_14, B_15]: (r2_hidden('#skF_1'(A_14, B_15), A_14) | k1_xboole_0=A_14 | k1_tarski(B_15)=A_14)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.33/1.26  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.33/1.26  tff(c_24, plain, (![A_21, B_22, C_23]: (r2_hidden(k4_tarski(A_21, B_22), C_23) | ~r2_hidden(B_22, k11_relat_1(C_23, A_21)) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.33/1.26  tff(c_240, plain, (![C_82, A_83, B_84]: (k1_funct_1(C_82, A_83)=B_84 | ~r2_hidden(k4_tarski(A_83, B_84), C_82) | ~v1_funct_1(C_82) | ~v1_relat_1(C_82))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.33/1.26  tff(c_263, plain, (![C_88, A_89, B_90]: (k1_funct_1(C_88, A_89)=B_90 | ~v1_funct_1(C_88) | ~r2_hidden(B_90, k11_relat_1(C_88, A_89)) | ~v1_relat_1(C_88))), inference(resolution, [status(thm)], [c_24, c_240])).
% 2.33/1.26  tff(c_274, plain, (![B_90]: (k1_funct_1('#skF_3', '#skF_2')=B_90 | ~v1_funct_1('#skF_3') | ~r2_hidden(B_90, k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_263])).
% 2.33/1.26  tff(c_307, plain, (![B_93]: (k1_funct_1('#skF_3', '#skF_2')=B_93 | ~r2_hidden(B_93, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_274])).
% 2.33/1.26  tff(c_319, plain, (![B_15]: ('#skF_1'(k2_relat_1('#skF_3'), B_15)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_15))), inference(resolution, [status(thm)], [c_18, c_307])).
% 2.33/1.26  tff(c_325, plain, (![B_94]: ('#skF_1'(k2_relat_1('#skF_3'), B_94)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_tarski(B_94))), inference(negUnitSimplification, [status(thm)], [c_173, c_319])).
% 2.33/1.26  tff(c_16, plain, (![A_14, B_15]: ('#skF_1'(A_14, B_15)!=B_15 | k1_xboole_0=A_14 | k1_tarski(B_15)=A_14)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.33/1.26  tff(c_333, plain, (![B_94]: (k1_funct_1('#skF_3', '#skF_2')!=B_94 | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_94) | k2_relat_1('#skF_3')=k1_tarski(B_94))), inference(superposition, [status(thm), theory('equality')], [c_325, c_16])).
% 2.33/1.26  tff(c_341, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))=k2_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_173, c_333])).
% 2.33/1.26  tff(c_42, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k2_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.33/1.26  tff(c_344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_341, c_42])).
% 2.33/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.26  
% 2.33/1.26  Inference rules
% 2.33/1.26  ----------------------
% 2.33/1.26  #Ref     : 0
% 2.33/1.26  #Sup     : 63
% 2.33/1.26  #Fact    : 0
% 2.33/1.26  #Define  : 0
% 2.33/1.26  #Split   : 0
% 2.33/1.26  #Chain   : 0
% 2.33/1.26  #Close   : 0
% 2.33/1.26  
% 2.33/1.26  Ordering : KBO
% 2.33/1.26  
% 2.33/1.26  Simplification rules
% 2.33/1.26  ----------------------
% 2.33/1.26  #Subsume      : 2
% 2.33/1.26  #Demod        : 14
% 2.33/1.26  #Tautology    : 32
% 2.33/1.26  #SimpNegUnit  : 3
% 2.33/1.26  #BackRed      : 1
% 2.33/1.26  
% 2.33/1.26  #Partial instantiations: 0
% 2.33/1.26  #Strategies tried      : 1
% 2.33/1.26  
% 2.33/1.26  Timing (in seconds)
% 2.33/1.26  ----------------------
% 2.33/1.26  Preprocessing        : 0.31
% 2.33/1.26  Parsing              : 0.16
% 2.33/1.26  CNF conversion       : 0.02
% 2.33/1.26  Main loop            : 0.20
% 2.33/1.26  Inferencing          : 0.08
% 2.33/1.26  Reduction            : 0.06
% 2.33/1.26  Demodulation         : 0.04
% 2.33/1.26  BG Simplification    : 0.02
% 2.33/1.26  Subsumption          : 0.03
% 2.33/1.26  Abstraction          : 0.01
% 2.33/1.26  MUC search           : 0.00
% 2.33/1.26  Cooper               : 0.00
% 2.33/1.26  Total                : 0.54
% 2.33/1.26  Index Insertion      : 0.00
% 2.33/1.26  Index Deletion       : 0.00
% 2.33/1.26  Index Matching       : 0.00
% 2.33/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
