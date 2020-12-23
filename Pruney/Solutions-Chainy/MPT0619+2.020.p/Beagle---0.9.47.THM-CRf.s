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
% DateTime   : Thu Dec  3 10:02:54 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 124 expanded)
%              Number of leaves         :   34 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :   94 ( 224 expanded)
%              Number of equality atoms :   49 ( 115 expanded)
%              Maximal formula depth    :   14 (   4 average)
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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

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
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_74,axiom,(
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

tff(f_65,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_68,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_64,plain,(
    k1_tarski('#skF_4') = k1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_137,plain,(
    ! [A_63,B_64] :
      ( k9_relat_1(A_63,k1_tarski(B_64)) = k11_relat_1(A_63,B_64)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_158,plain,(
    ! [A_70] :
      ( k9_relat_1(A_70,k1_relat_1('#skF_5')) = k11_relat_1(A_70,'#skF_4')
      | ~ v1_relat_1(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_137])).

tff(c_46,plain,(
    ! [A_25] :
      ( k9_relat_1(A_25,k1_relat_1(A_25)) = k2_relat_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_165,plain,
    ( k11_relat_1('#skF_5','#skF_4') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_46])).

tff(c_175,plain,(
    k11_relat_1('#skF_5','#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_165])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_104,plain,(
    ! [A_54,B_55,C_56] : k2_enumset1(A_54,A_54,B_55,C_56) = k1_enumset1(A_54,B_55,C_56) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [F_21,B_15,C_16,D_17] : r2_hidden(F_21,k2_enumset1(F_21,B_15,C_16,D_17)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_125,plain,(
    ! [A_57,B_58,C_59] : r2_hidden(A_57,k1_enumset1(A_57,B_58,C_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_22])).

tff(c_129,plain,(
    ! [A_60,B_61] : r2_hidden(A_60,k2_tarski(A_60,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_125])).

tff(c_133,plain,(
    ! [A_62] : r2_hidden(A_62,k1_tarski(A_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_129])).

tff(c_136,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_133])).

tff(c_193,plain,(
    ! [B_80,A_81] :
      ( k11_relat_1(B_80,A_81) != k1_xboole_0
      | ~ r2_hidden(A_81,k1_relat_1(B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_203,plain,
    ( k11_relat_1('#skF_5','#skF_4') != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_136,c_193])).

tff(c_208,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_175,c_203])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_1'(A_11,B_12),A_11)
      | k1_xboole_0 = A_11
      | k1_tarski(B_12) = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_48,plain,(
    ! [A_26,B_27,C_28] :
      ( r2_hidden(k4_tarski(A_26,B_27),C_28)
      | ~ r2_hidden(B_27,k11_relat_1(C_28,A_26))
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_344,plain,(
    ! [C_95,A_96,B_97] :
      ( k1_funct_1(C_95,A_96) = B_97
      | ~ r2_hidden(k4_tarski(A_96,B_97),C_95)
      | ~ v1_funct_1(C_95)
      | ~ v1_relat_1(C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_440,plain,(
    ! [C_103,A_104,B_105] :
      ( k1_funct_1(C_103,A_104) = B_105
      | ~ v1_funct_1(C_103)
      | ~ r2_hidden(B_105,k11_relat_1(C_103,A_104))
      | ~ v1_relat_1(C_103) ) ),
    inference(resolution,[status(thm)],[c_48,c_344])).

tff(c_455,plain,(
    ! [B_105] :
      ( k1_funct_1('#skF_5','#skF_4') = B_105
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden(B_105,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_440])).

tff(c_461,plain,(
    ! [B_106] :
      ( k1_funct_1('#skF_5','#skF_4') = B_106
      | ~ r2_hidden(B_106,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_455])).

tff(c_473,plain,(
    ! [B_12] :
      ( '#skF_1'(k2_relat_1('#skF_5'),B_12) = k1_funct_1('#skF_5','#skF_4')
      | k2_relat_1('#skF_5') = k1_xboole_0
      | k2_relat_1('#skF_5') = k1_tarski(B_12) ) ),
    inference(resolution,[status(thm)],[c_12,c_461])).

tff(c_479,plain,(
    ! [B_107] :
      ( '#skF_1'(k2_relat_1('#skF_5'),B_107) = k1_funct_1('#skF_5','#skF_4')
      | k2_relat_1('#skF_5') = k1_tarski(B_107) ) ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_473])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( '#skF_1'(A_11,B_12) != B_12
      | k1_xboole_0 = A_11
      | k1_tarski(B_12) = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_487,plain,(
    ! [B_107] :
      ( k1_funct_1('#skF_5','#skF_4') != B_107
      | k2_relat_1('#skF_5') = k1_xboole_0
      | k2_relat_1('#skF_5') = k1_tarski(B_107)
      | k2_relat_1('#skF_5') = k1_tarski(B_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_10])).

tff(c_495,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_4')) = k2_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_487])).

tff(c_62,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_4')) != k2_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:35:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.35  
% 2.48/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.35  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.48/1.35  
% 2.48/1.35  %Foreground sorts:
% 2.48/1.35  
% 2.48/1.35  
% 2.48/1.35  %Background operators:
% 2.48/1.35  
% 2.48/1.35  
% 2.48/1.35  %Foreground operators:
% 2.48/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.48/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.48/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.48/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.48/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.48/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.48/1.35  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.48/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.48/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.48/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.48/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.48/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.48/1.35  
% 2.48/1.36  tff(f_106, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.48/1.36  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.48/1.36  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.48/1.36  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.48/1.36  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.48/1.36  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.48/1.36  tff(f_65, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 2.48/1.36  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.48/1.36  tff(f_47, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.48/1.36  tff(f_80, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 2.48/1.36  tff(f_97, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.48/1.36  tff(c_68, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.48/1.36  tff(c_64, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.48/1.36  tff(c_137, plain, (![A_63, B_64]: (k9_relat_1(A_63, k1_tarski(B_64))=k11_relat_1(A_63, B_64) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.48/1.36  tff(c_158, plain, (![A_70]: (k9_relat_1(A_70, k1_relat_1('#skF_5'))=k11_relat_1(A_70, '#skF_4') | ~v1_relat_1(A_70))), inference(superposition, [status(thm), theory('equality')], [c_64, c_137])).
% 2.48/1.36  tff(c_46, plain, (![A_25]: (k9_relat_1(A_25, k1_relat_1(A_25))=k2_relat_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.48/1.36  tff(c_165, plain, (k11_relat_1('#skF_5', '#skF_4')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_158, c_46])).
% 2.48/1.36  tff(c_175, plain, (k11_relat_1('#skF_5', '#skF_4')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_165])).
% 2.48/1.36  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.48/1.36  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.48/1.36  tff(c_104, plain, (![A_54, B_55, C_56]: (k2_enumset1(A_54, A_54, B_55, C_56)=k1_enumset1(A_54, B_55, C_56))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.36  tff(c_22, plain, (![F_21, B_15, C_16, D_17]: (r2_hidden(F_21, k2_enumset1(F_21, B_15, C_16, D_17)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.48/1.36  tff(c_125, plain, (![A_57, B_58, C_59]: (r2_hidden(A_57, k1_enumset1(A_57, B_58, C_59)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_22])).
% 2.48/1.36  tff(c_129, plain, (![A_60, B_61]: (r2_hidden(A_60, k2_tarski(A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_125])).
% 2.48/1.36  tff(c_133, plain, (![A_62]: (r2_hidden(A_62, k1_tarski(A_62)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_129])).
% 2.48/1.36  tff(c_136, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_133])).
% 2.48/1.36  tff(c_193, plain, (![B_80, A_81]: (k11_relat_1(B_80, A_81)!=k1_xboole_0 | ~r2_hidden(A_81, k1_relat_1(B_80)) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.48/1.36  tff(c_203, plain, (k11_relat_1('#skF_5', '#skF_4')!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_136, c_193])).
% 2.48/1.36  tff(c_208, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_68, c_175, c_203])).
% 2.48/1.36  tff(c_12, plain, (![A_11, B_12]: (r2_hidden('#skF_1'(A_11, B_12), A_11) | k1_xboole_0=A_11 | k1_tarski(B_12)=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.48/1.36  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.48/1.36  tff(c_48, plain, (![A_26, B_27, C_28]: (r2_hidden(k4_tarski(A_26, B_27), C_28) | ~r2_hidden(B_27, k11_relat_1(C_28, A_26)) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.48/1.36  tff(c_344, plain, (![C_95, A_96, B_97]: (k1_funct_1(C_95, A_96)=B_97 | ~r2_hidden(k4_tarski(A_96, B_97), C_95) | ~v1_funct_1(C_95) | ~v1_relat_1(C_95))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.48/1.36  tff(c_440, plain, (![C_103, A_104, B_105]: (k1_funct_1(C_103, A_104)=B_105 | ~v1_funct_1(C_103) | ~r2_hidden(B_105, k11_relat_1(C_103, A_104)) | ~v1_relat_1(C_103))), inference(resolution, [status(thm)], [c_48, c_344])).
% 2.48/1.36  tff(c_455, plain, (![B_105]: (k1_funct_1('#skF_5', '#skF_4')=B_105 | ~v1_funct_1('#skF_5') | ~r2_hidden(B_105, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_175, c_440])).
% 2.48/1.36  tff(c_461, plain, (![B_106]: (k1_funct_1('#skF_5', '#skF_4')=B_106 | ~r2_hidden(B_106, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_455])).
% 2.48/1.36  tff(c_473, plain, (![B_12]: ('#skF_1'(k2_relat_1('#skF_5'), B_12)=k1_funct_1('#skF_5', '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')=k1_tarski(B_12))), inference(resolution, [status(thm)], [c_12, c_461])).
% 2.48/1.36  tff(c_479, plain, (![B_107]: ('#skF_1'(k2_relat_1('#skF_5'), B_107)=k1_funct_1('#skF_5', '#skF_4') | k2_relat_1('#skF_5')=k1_tarski(B_107))), inference(negUnitSimplification, [status(thm)], [c_208, c_473])).
% 2.48/1.36  tff(c_10, plain, (![A_11, B_12]: ('#skF_1'(A_11, B_12)!=B_12 | k1_xboole_0=A_11 | k1_tarski(B_12)=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.48/1.36  tff(c_487, plain, (![B_107]: (k1_funct_1('#skF_5', '#skF_4')!=B_107 | k2_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')=k1_tarski(B_107) | k2_relat_1('#skF_5')=k1_tarski(B_107))), inference(superposition, [status(thm), theory('equality')], [c_479, c_10])).
% 2.48/1.36  tff(c_495, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_4'))=k2_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_208, c_487])).
% 2.48/1.36  tff(c_62, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_4'))!=k2_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.48/1.36  tff(c_498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_495, c_62])).
% 2.48/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.36  
% 2.48/1.36  Inference rules
% 2.48/1.36  ----------------------
% 2.48/1.36  #Ref     : 0
% 2.48/1.36  #Sup     : 90
% 2.48/1.36  #Fact    : 0
% 2.48/1.36  #Define  : 0
% 2.48/1.36  #Split   : 0
% 2.48/1.36  #Chain   : 0
% 2.48/1.36  #Close   : 0
% 2.48/1.36  
% 2.48/1.37  Ordering : KBO
% 2.48/1.37  
% 2.48/1.37  Simplification rules
% 2.48/1.37  ----------------------
% 2.48/1.37  #Subsume      : 1
% 2.48/1.37  #Demod        : 16
% 2.48/1.37  #Tautology    : 29
% 2.48/1.37  #SimpNegUnit  : 3
% 2.48/1.37  #BackRed      : 1
% 2.48/1.37  
% 2.48/1.37  #Partial instantiations: 0
% 2.48/1.37  #Strategies tried      : 1
% 2.48/1.37  
% 2.48/1.37  Timing (in seconds)
% 2.48/1.37  ----------------------
% 2.48/1.37  Preprocessing        : 0.34
% 2.48/1.37  Parsing              : 0.17
% 2.48/1.37  CNF conversion       : 0.02
% 2.48/1.37  Main loop            : 0.27
% 2.48/1.37  Inferencing          : 0.10
% 2.48/1.37  Reduction            : 0.08
% 2.48/1.37  Demodulation         : 0.06
% 2.48/1.37  BG Simplification    : 0.02
% 2.48/1.37  Subsumption          : 0.05
% 2.48/1.37  Abstraction          : 0.02
% 2.48/1.37  MUC search           : 0.00
% 2.48/1.37  Cooper               : 0.00
% 2.48/1.37  Total                : 0.64
% 2.48/1.37  Index Insertion      : 0.00
% 2.48/1.37  Index Deletion       : 0.00
% 2.48/1.37  Index Matching       : 0.00
% 2.48/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
