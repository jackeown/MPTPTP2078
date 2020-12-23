%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:21 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   54 (  76 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   67 ( 107 expanded)
%              Number of equality atoms :   20 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_40,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_98,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_113,plain,(
    ! [B_34,A_35] : k1_setfam_1(k2_tarski(B_34,A_35)) = k3_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_98])).

tff(c_14,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_119,plain,(
    ! [B_34,A_35] : k3_xboole_0(B_34,A_35) = k3_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_14])).

tff(c_30,plain,(
    r2_hidden('#skF_2',k3_xboole_0(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_136,plain,(
    r2_hidden('#skF_2',k3_xboole_0('#skF_3',k1_relat_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_30])).

tff(c_204,plain,(
    ! [C_47,B_48,A_49] :
      ( r2_hidden(C_47,B_48)
      | ~ r2_hidden(C_47,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_211,plain,(
    ! [B_50] :
      ( r2_hidden('#skF_2',B_50)
      | ~ r1_tarski(k3_xboole_0('#skF_3',k1_relat_1('#skF_4')),B_50) ) ),
    inference(resolution,[status(thm)],[c_136,c_204])).

tff(c_227,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_211])).

tff(c_26,plain,(
    ! [B_21,A_20] :
      ( k1_funct_1(k6_relat_1(B_21),A_20) = A_20
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_15] : v1_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_228,plain,(
    ! [B_51,C_52,A_53] :
      ( k1_funct_1(k5_relat_1(B_51,C_52),A_53) = k1_funct_1(C_52,k1_funct_1(B_51,A_53))
      | ~ r2_hidden(A_53,k1_relat_1(B_51))
      | ~ v1_funct_1(C_52)
      | ~ v1_relat_1(C_52)
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_233,plain,(
    ! [A_14,C_52,A_53] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_14),C_52),A_53) = k1_funct_1(C_52,k1_funct_1(k6_relat_1(A_14),A_53))
      | ~ r2_hidden(A_53,A_14)
      | ~ v1_funct_1(C_52)
      | ~ v1_relat_1(C_52)
      | ~ v1_funct_1(k6_relat_1(A_14))
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_228])).

tff(c_433,plain,(
    ! [A_90,C_91,A_92] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_90),C_91),A_92) = k1_funct_1(C_91,k1_funct_1(k6_relat_1(A_90),A_92))
      | ~ r2_hidden(A_92,A_90)
      | ~ v1_funct_1(C_91)
      | ~ v1_relat_1(C_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_233])).

tff(c_28,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_3'),'#skF_4'),'#skF_2') != k1_funct_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_439,plain,
    ( k1_funct_1('#skF_4',k1_funct_1(k6_relat_1('#skF_3'),'#skF_2')) != k1_funct_1('#skF_4','#skF_2')
    | ~ r2_hidden('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_28])).

tff(c_445,plain,(
    k1_funct_1('#skF_4',k1_funct_1(k6_relat_1('#skF_3'),'#skF_2')) != k1_funct_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_227,c_439])).

tff(c_449,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_445])).

tff(c_453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:05:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.37  
% 2.55/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.38  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.55/1.38  
% 2.55/1.38  %Foreground sorts:
% 2.55/1.38  
% 2.55/1.38  
% 2.55/1.38  %Background operators:
% 2.55/1.38  
% 2.55/1.38  
% 2.55/1.38  %Foreground operators:
% 2.55/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.55/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.55/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.55/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.55/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.55/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.55/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.55/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.55/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.55/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.55/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.55/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.55/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.55/1.38  
% 2.55/1.39  tff(f_34, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.55/1.39  tff(f_36, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.55/1.39  tff(f_40, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.55/1.39  tff(f_74, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_1)).
% 2.55/1.39  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.55/1.39  tff(f_65, axiom, (![A, B]: (r2_hidden(A, B) => (k1_funct_1(k6_relat_1(B), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_1)).
% 2.55/1.39  tff(f_48, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.55/1.39  tff(f_44, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.55/1.39  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 2.55/1.39  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.55/1.39  tff(c_10, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.55/1.39  tff(c_98, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.55/1.39  tff(c_113, plain, (![B_34, A_35]: (k1_setfam_1(k2_tarski(B_34, A_35))=k3_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_10, c_98])).
% 2.55/1.39  tff(c_14, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.55/1.39  tff(c_119, plain, (![B_34, A_35]: (k3_xboole_0(B_34, A_35)=k3_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_113, c_14])).
% 2.55/1.39  tff(c_30, plain, (r2_hidden('#skF_2', k3_xboole_0(k1_relat_1('#skF_4'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.55/1.39  tff(c_136, plain, (r2_hidden('#skF_2', k3_xboole_0('#skF_3', k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_30])).
% 2.55/1.39  tff(c_204, plain, (![C_47, B_48, A_49]: (r2_hidden(C_47, B_48) | ~r2_hidden(C_47, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.39  tff(c_211, plain, (![B_50]: (r2_hidden('#skF_2', B_50) | ~r1_tarski(k3_xboole_0('#skF_3', k1_relat_1('#skF_4')), B_50))), inference(resolution, [status(thm)], [c_136, c_204])).
% 2.55/1.39  tff(c_227, plain, (r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_8, c_211])).
% 2.55/1.39  tff(c_26, plain, (![B_21, A_20]: (k1_funct_1(k6_relat_1(B_21), A_20)=A_20 | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.55/1.39  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.55/1.39  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.55/1.39  tff(c_20, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.55/1.39  tff(c_22, plain, (![A_15]: (v1_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.55/1.39  tff(c_16, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.55/1.39  tff(c_228, plain, (![B_51, C_52, A_53]: (k1_funct_1(k5_relat_1(B_51, C_52), A_53)=k1_funct_1(C_52, k1_funct_1(B_51, A_53)) | ~r2_hidden(A_53, k1_relat_1(B_51)) | ~v1_funct_1(C_52) | ~v1_relat_1(C_52) | ~v1_funct_1(B_51) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.55/1.39  tff(c_233, plain, (![A_14, C_52, A_53]: (k1_funct_1(k5_relat_1(k6_relat_1(A_14), C_52), A_53)=k1_funct_1(C_52, k1_funct_1(k6_relat_1(A_14), A_53)) | ~r2_hidden(A_53, A_14) | ~v1_funct_1(C_52) | ~v1_relat_1(C_52) | ~v1_funct_1(k6_relat_1(A_14)) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_228])).
% 2.55/1.39  tff(c_433, plain, (![A_90, C_91, A_92]: (k1_funct_1(k5_relat_1(k6_relat_1(A_90), C_91), A_92)=k1_funct_1(C_91, k1_funct_1(k6_relat_1(A_90), A_92)) | ~r2_hidden(A_92, A_90) | ~v1_funct_1(C_91) | ~v1_relat_1(C_91))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_233])).
% 2.55/1.39  tff(c_28, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_3'), '#skF_4'), '#skF_2')!=k1_funct_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.55/1.39  tff(c_439, plain, (k1_funct_1('#skF_4', k1_funct_1(k6_relat_1('#skF_3'), '#skF_2'))!=k1_funct_1('#skF_4', '#skF_2') | ~r2_hidden('#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_433, c_28])).
% 2.55/1.39  tff(c_445, plain, (k1_funct_1('#skF_4', k1_funct_1(k6_relat_1('#skF_3'), '#skF_2'))!=k1_funct_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_227, c_439])).
% 2.55/1.39  tff(c_449, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_445])).
% 2.55/1.39  tff(c_453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_227, c_449])).
% 2.55/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.39  
% 2.55/1.39  Inference rules
% 2.55/1.39  ----------------------
% 2.55/1.39  #Ref     : 0
% 2.55/1.39  #Sup     : 101
% 2.55/1.39  #Fact    : 0
% 2.55/1.39  #Define  : 0
% 2.55/1.39  #Split   : 0
% 2.55/1.39  #Chain   : 0
% 2.55/1.39  #Close   : 0
% 2.55/1.39  
% 2.55/1.39  Ordering : KBO
% 2.55/1.39  
% 2.55/1.39  Simplification rules
% 2.55/1.39  ----------------------
% 2.55/1.39  #Subsume      : 14
% 2.55/1.39  #Demod        : 23
% 2.55/1.39  #Tautology    : 45
% 2.55/1.39  #SimpNegUnit  : 0
% 2.55/1.39  #BackRed      : 1
% 2.55/1.39  
% 2.55/1.39  #Partial instantiations: 0
% 2.55/1.39  #Strategies tried      : 1
% 2.55/1.39  
% 2.55/1.39  Timing (in seconds)
% 2.55/1.39  ----------------------
% 2.55/1.39  Preprocessing        : 0.30
% 2.55/1.39  Parsing              : 0.16
% 2.55/1.39  CNF conversion       : 0.02
% 2.55/1.39  Main loop            : 0.27
% 2.55/1.39  Inferencing          : 0.10
% 2.55/1.39  Reduction            : 0.09
% 2.55/1.39  Demodulation         : 0.07
% 2.55/1.39  BG Simplification    : 0.01
% 2.55/1.39  Subsumption          : 0.05
% 2.55/1.39  Abstraction          : 0.02
% 2.55/1.39  MUC search           : 0.00
% 2.55/1.39  Cooper               : 0.00
% 2.55/1.39  Total                : 0.59
% 2.55/1.39  Index Insertion      : 0.00
% 2.55/1.39  Index Deletion       : 0.00
% 2.55/1.39  Index Matching       : 0.00
% 2.55/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
