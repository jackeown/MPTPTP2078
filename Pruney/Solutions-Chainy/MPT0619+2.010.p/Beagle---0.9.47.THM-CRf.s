%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:52 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 116 expanded)
%              Number of leaves         :   31 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 218 expanded)
%              Number of equality atoms :   41 (  99 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_44,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_138,plain,(
    ! [A_50,B_51] :
      ( k9_relat_1(A_50,k1_tarski(B_51)) = k11_relat_1(A_50,B_51)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_150,plain,(
    ! [A_52] :
      ( k9_relat_1(A_52,k1_relat_1('#skF_3')) = k11_relat_1(A_52,'#skF_2')
      | ~ v1_relat_1(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_138])).

tff(c_26,plain,(
    ! [A_18] :
      ( k9_relat_1(A_18,k1_relat_1(A_18)) = k2_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_157,plain,
    ( k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_26])).

tff(c_167,plain,(
    k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_157])).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    ! [A_32,C_33,B_34] :
      ( r2_hidden(A_32,C_33)
      | ~ r1_tarski(k2_tarski(A_32,B_34),C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_98,plain,(
    ! [A_37,B_38] : r2_hidden(A_37,k2_tarski(A_37,B_38)) ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_102,plain,(
    ! [A_39] : r2_hidden(A_39,k1_tarski(A_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_98])).

tff(c_105,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_102])).

tff(c_187,plain,(
    ! [B_60,A_61] :
      ( k11_relat_1(B_60,A_61) != k1_xboole_0
      | ~ r2_hidden(A_61,k1_relat_1(B_60))
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_197,plain,
    ( k11_relat_1('#skF_3','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_105,c_187])).

tff(c_202,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_167,c_197])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_1'(A_12,B_13),A_12)
      | k1_xboole_0 = A_12
      | k1_tarski(B_13) = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    ! [A_19,B_20,C_21] :
      ( r2_hidden(k4_tarski(A_19,B_20),C_21)
      | ~ r2_hidden(B_20,k11_relat_1(C_21,A_19))
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_400,plain,(
    ! [C_84,A_85,B_86] :
      ( k1_funct_1(C_84,A_85) = B_86
      | ~ r2_hidden(k4_tarski(A_85,B_86),C_84)
      | ~ v1_funct_1(C_84)
      | ~ v1_relat_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_438,plain,(
    ! [C_90,A_91,B_92] :
      ( k1_funct_1(C_90,A_91) = B_92
      | ~ v1_funct_1(C_90)
      | ~ r2_hidden(B_92,k11_relat_1(C_90,A_91))
      | ~ v1_relat_1(C_90) ) ),
    inference(resolution,[status(thm)],[c_28,c_400])).

tff(c_449,plain,(
    ! [B_92] :
      ( k1_funct_1('#skF_3','#skF_2') = B_92
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden(B_92,k2_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_438])).

tff(c_454,plain,(
    ! [B_93] :
      ( k1_funct_1('#skF_3','#skF_2') = B_93
      | ~ r2_hidden(B_93,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_449])).

tff(c_462,plain,(
    ! [B_13] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_13) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_13) ) ),
    inference(resolution,[status(thm)],[c_22,c_454])).

tff(c_467,plain,(
    ! [B_94] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_94) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_tarski(B_94) ) ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_462])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( '#skF_1'(A_12,B_13) != B_13
      | k1_xboole_0 = A_12
      | k1_tarski(B_13) = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_475,plain,(
    ! [B_94] :
      ( k1_funct_1('#skF_3','#skF_2') != B_94
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_94)
      | k2_relat_1('#skF_3') = k1_tarski(B_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_20])).

tff(c_524,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) = k2_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_475])).

tff(c_42,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k2_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:05 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.47  
% 2.78/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.47  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.78/1.47  
% 2.78/1.47  %Foreground sorts:
% 2.78/1.47  
% 2.78/1.47  
% 2.78/1.47  %Background operators:
% 2.78/1.47  
% 2.78/1.47  
% 2.78/1.47  %Foreground operators:
% 2.78/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.78/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.78/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.78/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.78/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.78/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.47  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.78/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.78/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.78/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.78/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.78/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.78/1.48  
% 2.78/1.49  tff(f_98, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.78/1.49  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.78/1.49  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.78/1.49  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.78/1.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.78/1.49  tff(f_43, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.78/1.49  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 2.78/1.49  tff(f_57, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.78/1.49  tff(f_72, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.78/1.49  tff(f_89, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.78/1.49  tff(c_48, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.78/1.49  tff(c_44, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.78/1.49  tff(c_138, plain, (![A_50, B_51]: (k9_relat_1(A_50, k1_tarski(B_51))=k11_relat_1(A_50, B_51) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.78/1.49  tff(c_150, plain, (![A_52]: (k9_relat_1(A_52, k1_relat_1('#skF_3'))=k11_relat_1(A_52, '#skF_2') | ~v1_relat_1(A_52))), inference(superposition, [status(thm), theory('equality')], [c_44, c_138])).
% 2.78/1.49  tff(c_26, plain, (![A_18]: (k9_relat_1(A_18, k1_relat_1(A_18))=k2_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.78/1.49  tff(c_157, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_150, c_26])).
% 2.78/1.49  tff(c_167, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_157])).
% 2.78/1.49  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.78/1.49  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.78/1.49  tff(c_82, plain, (![A_32, C_33, B_34]: (r2_hidden(A_32, C_33) | ~r1_tarski(k2_tarski(A_32, B_34), C_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.78/1.49  tff(c_98, plain, (![A_37, B_38]: (r2_hidden(A_37, k2_tarski(A_37, B_38)))), inference(resolution, [status(thm)], [c_6, c_82])).
% 2.78/1.49  tff(c_102, plain, (![A_39]: (r2_hidden(A_39, k1_tarski(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_98])).
% 2.78/1.49  tff(c_105, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_102])).
% 2.78/1.49  tff(c_187, plain, (![B_60, A_61]: (k11_relat_1(B_60, A_61)!=k1_xboole_0 | ~r2_hidden(A_61, k1_relat_1(B_60)) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.78/1.49  tff(c_197, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_105, c_187])).
% 2.78/1.49  tff(c_202, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_167, c_197])).
% 2.78/1.49  tff(c_22, plain, (![A_12, B_13]: (r2_hidden('#skF_1'(A_12, B_13), A_12) | k1_xboole_0=A_12 | k1_tarski(B_13)=A_12)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.78/1.49  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.78/1.49  tff(c_28, plain, (![A_19, B_20, C_21]: (r2_hidden(k4_tarski(A_19, B_20), C_21) | ~r2_hidden(B_20, k11_relat_1(C_21, A_19)) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.78/1.49  tff(c_400, plain, (![C_84, A_85, B_86]: (k1_funct_1(C_84, A_85)=B_86 | ~r2_hidden(k4_tarski(A_85, B_86), C_84) | ~v1_funct_1(C_84) | ~v1_relat_1(C_84))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.78/1.49  tff(c_438, plain, (![C_90, A_91, B_92]: (k1_funct_1(C_90, A_91)=B_92 | ~v1_funct_1(C_90) | ~r2_hidden(B_92, k11_relat_1(C_90, A_91)) | ~v1_relat_1(C_90))), inference(resolution, [status(thm)], [c_28, c_400])).
% 2.78/1.49  tff(c_449, plain, (![B_92]: (k1_funct_1('#skF_3', '#skF_2')=B_92 | ~v1_funct_1('#skF_3') | ~r2_hidden(B_92, k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_167, c_438])).
% 2.78/1.49  tff(c_454, plain, (![B_93]: (k1_funct_1('#skF_3', '#skF_2')=B_93 | ~r2_hidden(B_93, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_449])).
% 2.78/1.49  tff(c_462, plain, (![B_13]: ('#skF_1'(k2_relat_1('#skF_3'), B_13)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_13))), inference(resolution, [status(thm)], [c_22, c_454])).
% 2.78/1.49  tff(c_467, plain, (![B_94]: ('#skF_1'(k2_relat_1('#skF_3'), B_94)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_tarski(B_94))), inference(negUnitSimplification, [status(thm)], [c_202, c_462])).
% 2.78/1.49  tff(c_20, plain, (![A_12, B_13]: ('#skF_1'(A_12, B_13)!=B_13 | k1_xboole_0=A_12 | k1_tarski(B_13)=A_12)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.78/1.49  tff(c_475, plain, (![B_94]: (k1_funct_1('#skF_3', '#skF_2')!=B_94 | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_94) | k2_relat_1('#skF_3')=k1_tarski(B_94))), inference(superposition, [status(thm), theory('equality')], [c_467, c_20])).
% 2.78/1.49  tff(c_524, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))=k2_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_202, c_475])).
% 2.78/1.49  tff(c_42, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k2_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.78/1.49  tff(c_527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_524, c_42])).
% 2.78/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.49  
% 2.78/1.49  Inference rules
% 2.78/1.49  ----------------------
% 2.78/1.49  #Ref     : 0
% 2.78/1.49  #Sup     : 98
% 2.78/1.49  #Fact    : 0
% 2.78/1.49  #Define  : 0
% 2.78/1.49  #Split   : 0
% 2.78/1.49  #Chain   : 0
% 2.78/1.49  #Close   : 0
% 2.78/1.49  
% 2.78/1.49  Ordering : KBO
% 2.78/1.49  
% 2.78/1.49  Simplification rules
% 2.78/1.49  ----------------------
% 2.78/1.49  #Subsume      : 5
% 2.78/1.49  #Demod        : 33
% 2.78/1.49  #Tautology    : 40
% 2.78/1.49  #SimpNegUnit  : 5
% 2.78/1.49  #BackRed      : 1
% 2.78/1.49  
% 2.78/1.49  #Partial instantiations: 0
% 2.78/1.49  #Strategies tried      : 1
% 2.78/1.49  
% 2.78/1.49  Timing (in seconds)
% 2.78/1.49  ----------------------
% 2.78/1.49  Preprocessing        : 0.37
% 2.78/1.49  Parsing              : 0.19
% 2.78/1.49  CNF conversion       : 0.02
% 2.78/1.49  Main loop            : 0.27
% 2.78/1.49  Inferencing          : 0.10
% 2.78/1.49  Reduction            : 0.08
% 2.78/1.49  Demodulation         : 0.06
% 2.78/1.49  BG Simplification    : 0.02
% 2.78/1.49  Subsumption          : 0.05
% 2.78/1.49  Abstraction          : 0.02
% 2.78/1.49  MUC search           : 0.00
% 2.78/1.49  Cooper               : 0.00
% 2.78/1.49  Total                : 0.67
% 2.78/1.49  Index Insertion      : 0.00
% 2.78/1.49  Index Deletion       : 0.00
% 2.78/1.49  Index Matching       : 0.00
% 2.78/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
