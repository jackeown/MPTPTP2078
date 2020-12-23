%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:52 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 117 expanded)
%              Number of leaves         :   32 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 218 expanded)
%              Number of equality atoms :   41 (  99 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_81,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_46,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_140,plain,(
    ! [A_54,B_55] :
      ( k9_relat_1(A_54,k1_tarski(B_55)) = k11_relat_1(A_54,B_55)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_152,plain,(
    ! [A_56] :
      ( k9_relat_1(A_56,k1_relat_1('#skF_3')) = k11_relat_1(A_56,'#skF_2')
      | ~ v1_relat_1(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_140])).

tff(c_28,plain,(
    ! [A_22] :
      ( k9_relat_1(A_22,k1_relat_1(A_22)) = k2_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_159,plain,
    ( k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_28])).

tff(c_169,plain,(
    k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_159])).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [B_35,C_36,A_37] :
      ( r2_hidden(B_35,C_36)
      | ~ r1_tarski(k2_tarski(A_37,B_35),C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_84,plain,(
    ! [B_38,A_39] : r2_hidden(B_38,k2_tarski(A_39,B_38)) ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_95,plain,(
    ! [A_42] : r2_hidden(A_42,k1_tarski(A_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_84])).

tff(c_98,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_95])).

tff(c_187,plain,(
    ! [B_60,A_61] :
      ( k11_relat_1(B_60,A_61) != k1_xboole_0
      | ~ r2_hidden(A_61,k1_relat_1(B_60))
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_190,plain,
    ( k11_relat_1('#skF_3','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_187])).

tff(c_193,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_169,c_190])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_1'(A_13,B_14),A_13)
      | k1_xboole_0 = A_13
      | k1_tarski(B_14) = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    ! [A_23,B_24,C_25] :
      ( r2_hidden(k4_tarski(A_23,B_24),C_25)
      | ~ r2_hidden(B_24,k11_relat_1(C_25,A_23))
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_411,plain,(
    ! [C_92,A_93,B_94] :
      ( k1_funct_1(C_92,A_93) = B_94
      | ~ r2_hidden(k4_tarski(A_93,B_94),C_92)
      | ~ v1_funct_1(C_92)
      | ~ v1_relat_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_449,plain,(
    ! [C_98,A_99,B_100] :
      ( k1_funct_1(C_98,A_99) = B_100
      | ~ v1_funct_1(C_98)
      | ~ r2_hidden(B_100,k11_relat_1(C_98,A_99))
      | ~ v1_relat_1(C_98) ) ),
    inference(resolution,[status(thm)],[c_30,c_411])).

tff(c_460,plain,(
    ! [B_100] :
      ( k1_funct_1('#skF_3','#skF_2') = B_100
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden(B_100,k2_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_449])).

tff(c_501,plain,(
    ! [B_103] :
      ( k1_funct_1('#skF_3','#skF_2') = B_103
      | ~ r2_hidden(B_103,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_460])).

tff(c_513,plain,(
    ! [B_14] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_14) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_501])).

tff(c_519,plain,(
    ! [B_104] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_104) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_tarski(B_104) ) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_513])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( '#skF_1'(A_13,B_14) != B_14
      | k1_xboole_0 = A_13
      | k1_tarski(B_14) = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_527,plain,(
    ! [B_104] :
      ( k1_funct_1('#skF_3','#skF_2') != B_104
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_104)
      | k2_relat_1('#skF_3') = k1_tarski(B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_16])).

tff(c_535,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) = k2_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_527])).

tff(c_44,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k2_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:17:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.35  
% 2.37/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.35  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.37/1.35  
% 2.37/1.35  %Foreground sorts:
% 2.37/1.35  
% 2.37/1.35  
% 2.37/1.35  %Background operators:
% 2.37/1.35  
% 2.37/1.35  
% 2.37/1.35  %Foreground operators:
% 2.37/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.37/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.37/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.37/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.37/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.37/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.37/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.37/1.35  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.37/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.37/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.37/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.37/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.37/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.37/1.35  
% 2.37/1.37  tff(f_100, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.37/1.37  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.37/1.37  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.37/1.37  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.37/1.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.37/1.37  tff(f_59, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.37/1.37  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.37/1.37  tff(f_53, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 2.37/1.37  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 2.37/1.37  tff(f_91, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.37/1.37  tff(c_50, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.37/1.37  tff(c_46, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.37/1.37  tff(c_140, plain, (![A_54, B_55]: (k9_relat_1(A_54, k1_tarski(B_55))=k11_relat_1(A_54, B_55) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.37/1.37  tff(c_152, plain, (![A_56]: (k9_relat_1(A_56, k1_relat_1('#skF_3'))=k11_relat_1(A_56, '#skF_2') | ~v1_relat_1(A_56))), inference(superposition, [status(thm), theory('equality')], [c_46, c_140])).
% 2.37/1.37  tff(c_28, plain, (![A_22]: (k9_relat_1(A_22, k1_relat_1(A_22))=k2_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.37/1.37  tff(c_159, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_152, c_28])).
% 2.37/1.37  tff(c_169, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_159])).
% 2.37/1.37  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.37/1.37  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.37/1.37  tff(c_75, plain, (![B_35, C_36, A_37]: (r2_hidden(B_35, C_36) | ~r1_tarski(k2_tarski(A_37, B_35), C_36))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.37/1.37  tff(c_84, plain, (![B_38, A_39]: (r2_hidden(B_38, k2_tarski(A_39, B_38)))), inference(resolution, [status(thm)], [c_6, c_75])).
% 2.37/1.37  tff(c_95, plain, (![A_42]: (r2_hidden(A_42, k1_tarski(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_84])).
% 2.37/1.37  tff(c_98, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_95])).
% 2.37/1.37  tff(c_187, plain, (![B_60, A_61]: (k11_relat_1(B_60, A_61)!=k1_xboole_0 | ~r2_hidden(A_61, k1_relat_1(B_60)) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.37/1.37  tff(c_190, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_187])).
% 2.37/1.37  tff(c_193, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_169, c_190])).
% 2.37/1.37  tff(c_18, plain, (![A_13, B_14]: (r2_hidden('#skF_1'(A_13, B_14), A_13) | k1_xboole_0=A_13 | k1_tarski(B_14)=A_13)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.37/1.37  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.37/1.37  tff(c_30, plain, (![A_23, B_24, C_25]: (r2_hidden(k4_tarski(A_23, B_24), C_25) | ~r2_hidden(B_24, k11_relat_1(C_25, A_23)) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.37/1.37  tff(c_411, plain, (![C_92, A_93, B_94]: (k1_funct_1(C_92, A_93)=B_94 | ~r2_hidden(k4_tarski(A_93, B_94), C_92) | ~v1_funct_1(C_92) | ~v1_relat_1(C_92))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.37/1.37  tff(c_449, plain, (![C_98, A_99, B_100]: (k1_funct_1(C_98, A_99)=B_100 | ~v1_funct_1(C_98) | ~r2_hidden(B_100, k11_relat_1(C_98, A_99)) | ~v1_relat_1(C_98))), inference(resolution, [status(thm)], [c_30, c_411])).
% 2.37/1.37  tff(c_460, plain, (![B_100]: (k1_funct_1('#skF_3', '#skF_2')=B_100 | ~v1_funct_1('#skF_3') | ~r2_hidden(B_100, k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_169, c_449])).
% 2.37/1.37  tff(c_501, plain, (![B_103]: (k1_funct_1('#skF_3', '#skF_2')=B_103 | ~r2_hidden(B_103, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_460])).
% 2.37/1.37  tff(c_513, plain, (![B_14]: ('#skF_1'(k2_relat_1('#skF_3'), B_14)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_14))), inference(resolution, [status(thm)], [c_18, c_501])).
% 2.37/1.37  tff(c_519, plain, (![B_104]: ('#skF_1'(k2_relat_1('#skF_3'), B_104)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_tarski(B_104))), inference(negUnitSimplification, [status(thm)], [c_193, c_513])).
% 2.37/1.37  tff(c_16, plain, (![A_13, B_14]: ('#skF_1'(A_13, B_14)!=B_14 | k1_xboole_0=A_13 | k1_tarski(B_14)=A_13)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.37/1.37  tff(c_527, plain, (![B_104]: (k1_funct_1('#skF_3', '#skF_2')!=B_104 | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_104) | k2_relat_1('#skF_3')=k1_tarski(B_104))), inference(superposition, [status(thm), theory('equality')], [c_519, c_16])).
% 2.37/1.37  tff(c_535, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))=k2_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_193, c_527])).
% 2.37/1.37  tff(c_44, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k2_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.37/1.37  tff(c_538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_535, c_44])).
% 2.37/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.37  
% 2.37/1.37  Inference rules
% 2.37/1.37  ----------------------
% 2.37/1.37  #Ref     : 0
% 2.37/1.37  #Sup     : 100
% 2.37/1.37  #Fact    : 0
% 2.37/1.37  #Define  : 0
% 2.37/1.37  #Split   : 0
% 2.37/1.37  #Chain   : 0
% 2.37/1.37  #Close   : 0
% 2.37/1.37  
% 2.37/1.37  Ordering : KBO
% 2.37/1.37  
% 2.37/1.37  Simplification rules
% 2.37/1.37  ----------------------
% 2.64/1.37  #Subsume      : 5
% 2.64/1.37  #Demod        : 33
% 2.64/1.37  #Tautology    : 42
% 2.64/1.37  #SimpNegUnit  : 5
% 2.64/1.37  #BackRed      : 1
% 2.64/1.37  
% 2.64/1.37  #Partial instantiations: 0
% 2.64/1.37  #Strategies tried      : 1
% 2.64/1.37  
% 2.64/1.37  Timing (in seconds)
% 2.64/1.37  ----------------------
% 2.64/1.37  Preprocessing        : 0.32
% 2.64/1.37  Parsing              : 0.17
% 2.64/1.37  CNF conversion       : 0.02
% 2.64/1.37  Main loop            : 0.26
% 2.64/1.37  Inferencing          : 0.10
% 2.64/1.37  Reduction            : 0.08
% 2.64/1.37  Demodulation         : 0.06
% 2.64/1.37  BG Simplification    : 0.02
% 2.64/1.37  Subsumption          : 0.05
% 2.64/1.37  Abstraction          : 0.01
% 2.64/1.37  MUC search           : 0.00
% 2.64/1.37  Cooper               : 0.00
% 2.64/1.37  Total                : 0.61
% 2.64/1.37  Index Insertion      : 0.00
% 2.64/1.37  Index Deletion       : 0.00
% 2.64/1.37  Index Matching       : 0.00
% 2.64/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
