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
% DateTime   : Thu Dec  3 10:04:12 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   59 (  99 expanded)
%              Number of leaves         :   32 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 142 expanded)
%              Number of equality atoms :   19 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_67,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,k6_relat_1(B))))
      <=> ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_109,plain,(
    ! [A_46,B_47] : k1_setfam_1(k2_tarski(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_124,plain,(
    ! [B_48,A_49] : k1_setfam_1(k2_tarski(B_48,A_49)) = k3_xboole_0(A_49,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_109])).

tff(c_14,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_130,plain,(
    ! [B_48,A_49] : k3_xboole_0(B_48,A_49) = k3_xboole_0(A_49,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_14])).

tff(c_42,plain,(
    r2_hidden('#skF_1',k3_xboole_0(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_147,plain,(
    r2_hidden('#skF_1',k3_xboole_0('#skF_2',k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_42])).

tff(c_26,plain,(
    ! [A_29] : v1_relat_1(k6_relat_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [A_29] : v1_funct_1(k6_relat_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_25] : k1_relat_1(k6_relat_1(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36,plain,(
    ! [B_34,A_33] : k5_relat_1(k6_relat_1(B_34),k6_relat_1(A_33)) = k6_relat_1(k3_xboole_0(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_220,plain,(
    ! [A_72,C_73,B_74] :
      ( r2_hidden(A_72,k1_relat_1(C_73))
      | ~ r2_hidden(A_72,k1_relat_1(k5_relat_1(C_73,k6_relat_1(B_74))))
      | ~ v1_funct_1(C_73)
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_223,plain,(
    ! [A_72,B_34,A_33] :
      ( r2_hidden(A_72,k1_relat_1(k6_relat_1(B_34)))
      | ~ r2_hidden(A_72,k1_relat_1(k6_relat_1(k3_xboole_0(A_33,B_34))))
      | ~ v1_funct_1(k6_relat_1(B_34))
      | ~ v1_relat_1(k6_relat_1(B_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_220])).

tff(c_226,plain,(
    ! [A_75,B_76,A_77] :
      ( r2_hidden(A_75,B_76)
      | ~ r2_hidden(A_75,k3_xboole_0(A_77,B_76)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_16,c_16,c_223])).

tff(c_246,plain,(
    ! [A_81,A_82,B_83] :
      ( r2_hidden(A_81,A_82)
      | ~ r2_hidden(A_81,k3_xboole_0(A_82,B_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_226])).

tff(c_256,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_147,c_246])).

tff(c_46,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_236,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_147,c_226])).

tff(c_20,plain,(
    ! [A_26,C_28,B_27] :
      ( r2_hidden(A_26,k1_relat_1(k7_relat_1(C_28,B_27)))
      | ~ r2_hidden(A_26,k1_relat_1(C_28))
      | ~ r2_hidden(A_26,B_27)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_348,plain,(
    ! [C_108,B_109,A_110] :
      ( k1_funct_1(k7_relat_1(C_108,B_109),A_110) = k1_funct_1(C_108,A_110)
      | ~ r2_hidden(A_110,k1_relat_1(k7_relat_1(C_108,B_109)))
      | ~ v1_funct_1(C_108)
      | ~ v1_relat_1(C_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_402,plain,(
    ! [C_121,B_122,A_123] :
      ( k1_funct_1(k7_relat_1(C_121,B_122),A_123) = k1_funct_1(C_121,A_123)
      | ~ v1_funct_1(C_121)
      | ~ r2_hidden(A_123,k1_relat_1(C_121))
      | ~ r2_hidden(A_123,B_122)
      | ~ v1_relat_1(C_121) ) ),
    inference(resolution,[status(thm)],[c_20,c_348])).

tff(c_411,plain,(
    ! [B_122] :
      ( k1_funct_1(k7_relat_1('#skF_3',B_122),'#skF_1') = k1_funct_1('#skF_3','#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden('#skF_1',B_122)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_236,c_402])).

tff(c_422,plain,(
    ! [B_124] :
      ( k1_funct_1(k7_relat_1('#skF_3',B_124),'#skF_1') = k1_funct_1('#skF_3','#skF_1')
      | ~ r2_hidden('#skF_1',B_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_411])).

tff(c_40,plain,(
    k1_funct_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k1_funct_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_428,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_40])).

tff(c_436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_428])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.38  
% 2.35/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.38  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.35/1.38  
% 2.35/1.38  %Foreground sorts:
% 2.35/1.38  
% 2.35/1.38  
% 2.35/1.38  %Background operators:
% 2.35/1.38  
% 2.35/1.38  
% 2.35/1.38  %Foreground operators:
% 2.35/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.35/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.35/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.35/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.35/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.35/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.35/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.35/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.35/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.35/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.35/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.35/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.35/1.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.35/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.35/1.38  
% 2.66/1.40  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.66/1.40  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.66/1.40  tff(f_84, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_funct_1)).
% 2.66/1.40  tff(f_55, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.66/1.40  tff(f_43, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.66/1.40  tff(f_67, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.66/1.40  tff(f_65, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, k6_relat_1(B)))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_1)).
% 2.66/1.40  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 2.66/1.40  tff(f_75, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_funct_1)).
% 2.66/1.40  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.66/1.40  tff(c_109, plain, (![A_46, B_47]: (k1_setfam_1(k2_tarski(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.66/1.40  tff(c_124, plain, (![B_48, A_49]: (k1_setfam_1(k2_tarski(B_48, A_49))=k3_xboole_0(A_49, B_48))), inference(superposition, [status(thm), theory('equality')], [c_2, c_109])).
% 2.66/1.40  tff(c_14, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.66/1.40  tff(c_130, plain, (![B_48, A_49]: (k3_xboole_0(B_48, A_49)=k3_xboole_0(A_49, B_48))), inference(superposition, [status(thm), theory('equality')], [c_124, c_14])).
% 2.66/1.40  tff(c_42, plain, (r2_hidden('#skF_1', k3_xboole_0(k1_relat_1('#skF_3'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.66/1.40  tff(c_147, plain, (r2_hidden('#skF_1', k3_xboole_0('#skF_2', k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_42])).
% 2.66/1.40  tff(c_26, plain, (![A_29]: (v1_relat_1(k6_relat_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.66/1.40  tff(c_28, plain, (![A_29]: (v1_funct_1(k6_relat_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.66/1.40  tff(c_16, plain, (![A_25]: (k1_relat_1(k6_relat_1(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.66/1.40  tff(c_36, plain, (![B_34, A_33]: (k5_relat_1(k6_relat_1(B_34), k6_relat_1(A_33))=k6_relat_1(k3_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.66/1.40  tff(c_220, plain, (![A_72, C_73, B_74]: (r2_hidden(A_72, k1_relat_1(C_73)) | ~r2_hidden(A_72, k1_relat_1(k5_relat_1(C_73, k6_relat_1(B_74)))) | ~v1_funct_1(C_73) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.66/1.40  tff(c_223, plain, (![A_72, B_34, A_33]: (r2_hidden(A_72, k1_relat_1(k6_relat_1(B_34))) | ~r2_hidden(A_72, k1_relat_1(k6_relat_1(k3_xboole_0(A_33, B_34)))) | ~v1_funct_1(k6_relat_1(B_34)) | ~v1_relat_1(k6_relat_1(B_34)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_220])).
% 2.66/1.40  tff(c_226, plain, (![A_75, B_76, A_77]: (r2_hidden(A_75, B_76) | ~r2_hidden(A_75, k3_xboole_0(A_77, B_76)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_16, c_16, c_223])).
% 2.66/1.40  tff(c_246, plain, (![A_81, A_82, B_83]: (r2_hidden(A_81, A_82) | ~r2_hidden(A_81, k3_xboole_0(A_82, B_83)))), inference(superposition, [status(thm), theory('equality')], [c_130, c_226])).
% 2.66/1.40  tff(c_256, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_147, c_246])).
% 2.66/1.40  tff(c_46, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.66/1.40  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.66/1.40  tff(c_236, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_147, c_226])).
% 2.66/1.40  tff(c_20, plain, (![A_26, C_28, B_27]: (r2_hidden(A_26, k1_relat_1(k7_relat_1(C_28, B_27))) | ~r2_hidden(A_26, k1_relat_1(C_28)) | ~r2_hidden(A_26, B_27) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.66/1.40  tff(c_348, plain, (![C_108, B_109, A_110]: (k1_funct_1(k7_relat_1(C_108, B_109), A_110)=k1_funct_1(C_108, A_110) | ~r2_hidden(A_110, k1_relat_1(k7_relat_1(C_108, B_109))) | ~v1_funct_1(C_108) | ~v1_relat_1(C_108))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.66/1.40  tff(c_402, plain, (![C_121, B_122, A_123]: (k1_funct_1(k7_relat_1(C_121, B_122), A_123)=k1_funct_1(C_121, A_123) | ~v1_funct_1(C_121) | ~r2_hidden(A_123, k1_relat_1(C_121)) | ~r2_hidden(A_123, B_122) | ~v1_relat_1(C_121))), inference(resolution, [status(thm)], [c_20, c_348])).
% 2.66/1.40  tff(c_411, plain, (![B_122]: (k1_funct_1(k7_relat_1('#skF_3', B_122), '#skF_1')=k1_funct_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~r2_hidden('#skF_1', B_122) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_236, c_402])).
% 2.66/1.40  tff(c_422, plain, (![B_124]: (k1_funct_1(k7_relat_1('#skF_3', B_124), '#skF_1')=k1_funct_1('#skF_3', '#skF_1') | ~r2_hidden('#skF_1', B_124))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_411])).
% 2.66/1.40  tff(c_40, plain, (k1_funct_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k1_funct_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.66/1.40  tff(c_428, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_422, c_40])).
% 2.66/1.40  tff(c_436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_256, c_428])).
% 2.66/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.40  
% 2.66/1.40  Inference rules
% 2.66/1.40  ----------------------
% 2.66/1.40  #Ref     : 0
% 2.66/1.40  #Sup     : 94
% 2.66/1.40  #Fact    : 0
% 2.66/1.40  #Define  : 0
% 2.66/1.40  #Split   : 0
% 2.66/1.40  #Chain   : 0
% 2.66/1.40  #Close   : 0
% 2.66/1.40  
% 2.66/1.40  Ordering : KBO
% 2.66/1.40  
% 2.66/1.40  Simplification rules
% 2.66/1.40  ----------------------
% 2.66/1.40  #Subsume      : 18
% 2.66/1.40  #Demod        : 20
% 2.66/1.40  #Tautology    : 45
% 2.66/1.40  #SimpNegUnit  : 0
% 2.66/1.40  #BackRed      : 1
% 2.66/1.40  
% 2.66/1.40  #Partial instantiations: 0
% 2.66/1.40  #Strategies tried      : 1
% 2.66/1.40  
% 2.66/1.40  Timing (in seconds)
% 2.66/1.40  ----------------------
% 2.66/1.40  Preprocessing        : 0.30
% 2.66/1.40  Parsing              : 0.16
% 2.66/1.40  CNF conversion       : 0.02
% 2.66/1.40  Main loop            : 0.32
% 2.66/1.40  Inferencing          : 0.12
% 2.66/1.40  Reduction            : 0.11
% 2.66/1.40  Demodulation         : 0.09
% 2.66/1.40  BG Simplification    : 0.02
% 2.66/1.40  Subsumption          : 0.05
% 2.66/1.40  Abstraction          : 0.02
% 2.66/1.40  MUC search           : 0.00
% 2.66/1.40  Cooper               : 0.00
% 2.66/1.40  Total                : 0.65
% 2.66/1.40  Index Insertion      : 0.00
% 2.66/1.40  Index Deletion       : 0.00
% 2.66/1.40  Index Matching       : 0.00
% 2.66/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
