%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:55 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 131 expanded)
%              Number of leaves         :   36 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :   98 ( 232 expanded)
%              Number of equality atoms :   52 ( 121 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_76,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_72,plain,(
    k1_tarski('#skF_4') = k1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_123,plain,(
    ! [A_74,B_75] :
      ( k9_relat_1(A_74,k1_tarski(B_75)) = k11_relat_1(A_74,B_75)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_136,plain,(
    ! [A_78] :
      ( k9_relat_1(A_78,k1_relat_1('#skF_5')) = k11_relat_1(A_78,'#skF_4')
      | ~ v1_relat_1(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_123])).

tff(c_54,plain,(
    ! [A_31] :
      ( k9_relat_1(A_31,k1_relat_1(A_31)) = k2_relat_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_143,plain,
    ( k11_relat_1('#skF_5','#skF_4') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_54])).

tff(c_153,plain,(
    k11_relat_1('#skF_5','#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_76,c_143])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_173,plain,(
    ! [A_83,B_84,C_85,D_86] : k3_enumset1(A_83,A_83,B_84,C_85,D_86) = k2_enumset1(A_83,B_84,C_85,D_86) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [A_19,G_27,D_22,B_20,E_23] : r2_hidden(G_27,k3_enumset1(A_19,B_20,G_27,D_22,E_23)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_197,plain,(
    ! [B_87,A_88,C_89,D_90] : r2_hidden(B_87,k2_enumset1(A_88,B_87,C_89,D_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_22])).

tff(c_201,plain,(
    ! [A_91,B_92,C_93] : r2_hidden(A_91,k1_enumset1(A_91,B_92,C_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_197])).

tff(c_205,plain,(
    ! [A_94,B_95] : r2_hidden(A_94,k2_tarski(A_94,B_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_201])).

tff(c_215,plain,(
    ! [A_99] : r2_hidden(A_99,k1_tarski(A_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_205])).

tff(c_218,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_215])).

tff(c_62,plain,(
    ! [B_36,A_35] :
      ( k11_relat_1(B_36,A_35) != k1_xboole_0
      | ~ r2_hidden(A_35,k1_relat_1(B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_221,plain,
    ( k11_relat_1('#skF_5','#skF_4') != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_218,c_62])).

tff(c_224,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_153,c_221])).

tff(c_14,plain,(
    ! [A_16,B_17] :
      ( r2_hidden('#skF_1'(A_16,B_17),A_16)
      | k1_xboole_0 = A_16
      | k1_tarski(B_17) = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_74,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_56,plain,(
    ! [A_32,B_33,C_34] :
      ( r2_hidden(k4_tarski(A_32,B_33),C_34)
      | ~ r2_hidden(B_33,k11_relat_1(C_34,A_32))
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_432,plain,(
    ! [C_131,A_132,B_133] :
      ( k1_funct_1(C_131,A_132) = B_133
      | ~ r2_hidden(k4_tarski(A_132,B_133),C_131)
      | ~ v1_funct_1(C_131)
      | ~ v1_relat_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_530,plain,(
    ! [C_137,A_138,B_139] :
      ( k1_funct_1(C_137,A_138) = B_139
      | ~ v1_funct_1(C_137)
      | ~ r2_hidden(B_139,k11_relat_1(C_137,A_138))
      | ~ v1_relat_1(C_137) ) ),
    inference(resolution,[status(thm)],[c_56,c_432])).

tff(c_537,plain,(
    ! [B_139] :
      ( k1_funct_1('#skF_5','#skF_4') = B_139
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden(B_139,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_530])).

tff(c_546,plain,(
    ! [B_140] :
      ( k1_funct_1('#skF_5','#skF_4') = B_140
      | ~ r2_hidden(B_140,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_537])).

tff(c_554,plain,(
    ! [B_17] :
      ( '#skF_1'(k2_relat_1('#skF_5'),B_17) = k1_funct_1('#skF_5','#skF_4')
      | k2_relat_1('#skF_5') = k1_xboole_0
      | k2_relat_1('#skF_5') = k1_tarski(B_17) ) ),
    inference(resolution,[status(thm)],[c_14,c_546])).

tff(c_559,plain,(
    ! [B_141] :
      ( '#skF_1'(k2_relat_1('#skF_5'),B_141) = k1_funct_1('#skF_5','#skF_4')
      | k2_relat_1('#skF_5') = k1_tarski(B_141) ) ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_554])).

tff(c_12,plain,(
    ! [A_16,B_17] :
      ( '#skF_1'(A_16,B_17) != B_17
      | k1_xboole_0 = A_16
      | k1_tarski(B_17) = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_567,plain,(
    ! [B_141] :
      ( k1_funct_1('#skF_5','#skF_4') != B_141
      | k2_relat_1('#skF_5') = k1_xboole_0
      | k2_relat_1('#skF_5') = k1_tarski(B_141)
      | k2_relat_1('#skF_5') = k1_tarski(B_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_559,c_12])).

tff(c_575,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_4')) = k2_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_567])).

tff(c_70,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_4')) != k2_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_578,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:08:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.38  
% 2.75/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.38  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.75/1.38  
% 2.75/1.38  %Foreground sorts:
% 2.75/1.38  
% 2.75/1.38  
% 2.75/1.38  %Background operators:
% 2.75/1.38  
% 2.75/1.38  
% 2.75/1.38  %Foreground operators:
% 2.75/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.75/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.75/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.75/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.75/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.75/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.75/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.38  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.75/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.75/1.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.75/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.75/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.75/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.75/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.75/1.38  
% 2.75/1.40  tff(f_111, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.75/1.40  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.75/1.40  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.75/1.40  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.75/1.40  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.75/1.40  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.75/1.40  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.75/1.40  tff(f_70, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 2.75/1.40  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.75/1.40  tff(f_49, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.75/1.40  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 2.75/1.40  tff(f_102, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.75/1.40  tff(c_76, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.75/1.40  tff(c_72, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.75/1.40  tff(c_123, plain, (![A_74, B_75]: (k9_relat_1(A_74, k1_tarski(B_75))=k11_relat_1(A_74, B_75) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.75/1.40  tff(c_136, plain, (![A_78]: (k9_relat_1(A_78, k1_relat_1('#skF_5'))=k11_relat_1(A_78, '#skF_4') | ~v1_relat_1(A_78))), inference(superposition, [status(thm), theory('equality')], [c_72, c_123])).
% 2.75/1.40  tff(c_54, plain, (![A_31]: (k9_relat_1(A_31, k1_relat_1(A_31))=k2_relat_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.75/1.40  tff(c_143, plain, (k11_relat_1('#skF_5', '#skF_4')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_136, c_54])).
% 2.75/1.40  tff(c_153, plain, (k11_relat_1('#skF_5', '#skF_4')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_76, c_143])).
% 2.75/1.40  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.75/1.40  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.75/1.40  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.75/1.40  tff(c_173, plain, (![A_83, B_84, C_85, D_86]: (k3_enumset1(A_83, A_83, B_84, C_85, D_86)=k2_enumset1(A_83, B_84, C_85, D_86))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.75/1.40  tff(c_22, plain, (![A_19, G_27, D_22, B_20, E_23]: (r2_hidden(G_27, k3_enumset1(A_19, B_20, G_27, D_22, E_23)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.75/1.40  tff(c_197, plain, (![B_87, A_88, C_89, D_90]: (r2_hidden(B_87, k2_enumset1(A_88, B_87, C_89, D_90)))), inference(superposition, [status(thm), theory('equality')], [c_173, c_22])).
% 2.75/1.40  tff(c_201, plain, (![A_91, B_92, C_93]: (r2_hidden(A_91, k1_enumset1(A_91, B_92, C_93)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_197])).
% 2.75/1.40  tff(c_205, plain, (![A_94, B_95]: (r2_hidden(A_94, k2_tarski(A_94, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_201])).
% 2.75/1.40  tff(c_215, plain, (![A_99]: (r2_hidden(A_99, k1_tarski(A_99)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_205])).
% 2.75/1.40  tff(c_218, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_215])).
% 2.75/1.40  tff(c_62, plain, (![B_36, A_35]: (k11_relat_1(B_36, A_35)!=k1_xboole_0 | ~r2_hidden(A_35, k1_relat_1(B_36)) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.75/1.40  tff(c_221, plain, (k11_relat_1('#skF_5', '#skF_4')!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_218, c_62])).
% 2.75/1.40  tff(c_224, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_76, c_153, c_221])).
% 2.75/1.40  tff(c_14, plain, (![A_16, B_17]: (r2_hidden('#skF_1'(A_16, B_17), A_16) | k1_xboole_0=A_16 | k1_tarski(B_17)=A_16)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.75/1.40  tff(c_74, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.75/1.40  tff(c_56, plain, (![A_32, B_33, C_34]: (r2_hidden(k4_tarski(A_32, B_33), C_34) | ~r2_hidden(B_33, k11_relat_1(C_34, A_32)) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.75/1.40  tff(c_432, plain, (![C_131, A_132, B_133]: (k1_funct_1(C_131, A_132)=B_133 | ~r2_hidden(k4_tarski(A_132, B_133), C_131) | ~v1_funct_1(C_131) | ~v1_relat_1(C_131))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.75/1.40  tff(c_530, plain, (![C_137, A_138, B_139]: (k1_funct_1(C_137, A_138)=B_139 | ~v1_funct_1(C_137) | ~r2_hidden(B_139, k11_relat_1(C_137, A_138)) | ~v1_relat_1(C_137))), inference(resolution, [status(thm)], [c_56, c_432])).
% 2.75/1.40  tff(c_537, plain, (![B_139]: (k1_funct_1('#skF_5', '#skF_4')=B_139 | ~v1_funct_1('#skF_5') | ~r2_hidden(B_139, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_153, c_530])).
% 2.75/1.40  tff(c_546, plain, (![B_140]: (k1_funct_1('#skF_5', '#skF_4')=B_140 | ~r2_hidden(B_140, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_537])).
% 2.75/1.40  tff(c_554, plain, (![B_17]: ('#skF_1'(k2_relat_1('#skF_5'), B_17)=k1_funct_1('#skF_5', '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')=k1_tarski(B_17))), inference(resolution, [status(thm)], [c_14, c_546])).
% 2.75/1.40  tff(c_559, plain, (![B_141]: ('#skF_1'(k2_relat_1('#skF_5'), B_141)=k1_funct_1('#skF_5', '#skF_4') | k2_relat_1('#skF_5')=k1_tarski(B_141))), inference(negUnitSimplification, [status(thm)], [c_224, c_554])).
% 2.75/1.40  tff(c_12, plain, (![A_16, B_17]: ('#skF_1'(A_16, B_17)!=B_17 | k1_xboole_0=A_16 | k1_tarski(B_17)=A_16)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.75/1.40  tff(c_567, plain, (![B_141]: (k1_funct_1('#skF_5', '#skF_4')!=B_141 | k2_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')=k1_tarski(B_141) | k2_relat_1('#skF_5')=k1_tarski(B_141))), inference(superposition, [status(thm), theory('equality')], [c_559, c_12])).
% 2.75/1.40  tff(c_575, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_4'))=k2_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_224, c_567])).
% 2.75/1.40  tff(c_70, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_4'))!=k2_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.75/1.40  tff(c_578, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_575, c_70])).
% 2.75/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.40  
% 2.75/1.40  Inference rules
% 2.75/1.40  ----------------------
% 2.75/1.40  #Ref     : 0
% 2.75/1.40  #Sup     : 105
% 2.75/1.40  #Fact    : 0
% 2.75/1.40  #Define  : 0
% 2.75/1.40  #Split   : 0
% 2.75/1.40  #Chain   : 0
% 2.75/1.40  #Close   : 0
% 2.75/1.40  
% 2.75/1.40  Ordering : KBO
% 2.75/1.40  
% 2.75/1.40  Simplification rules
% 2.75/1.40  ----------------------
% 2.75/1.40  #Subsume      : 1
% 2.75/1.40  #Demod        : 17
% 2.75/1.40  #Tautology    : 30
% 2.75/1.40  #SimpNegUnit  : 3
% 2.75/1.40  #BackRed      : 1
% 2.75/1.40  
% 2.75/1.40  #Partial instantiations: 0
% 2.75/1.40  #Strategies tried      : 1
% 2.75/1.40  
% 2.75/1.40  Timing (in seconds)
% 2.75/1.40  ----------------------
% 2.75/1.40  Preprocessing        : 0.35
% 2.75/1.40  Parsing              : 0.17
% 2.75/1.40  CNF conversion       : 0.03
% 2.75/1.40  Main loop            : 0.29
% 2.75/1.40  Inferencing          : 0.10
% 2.75/1.40  Reduction            : 0.09
% 2.75/1.40  Demodulation         : 0.06
% 2.75/1.40  BG Simplification    : 0.02
% 2.75/1.40  Subsumption          : 0.06
% 2.75/1.40  Abstraction          : 0.02
% 2.75/1.40  MUC search           : 0.00
% 2.75/1.40  Cooper               : 0.00
% 2.75/1.40  Total                : 0.67
% 2.75/1.40  Index Insertion      : 0.00
% 2.75/1.40  Index Deletion       : 0.00
% 2.75/1.40  Index Matching       : 0.00
% 2.75/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
