%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:21 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   57 (  79 expanded)
%              Number of leaves         :   32 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 ( 107 expanded)
%              Number of equality atoms :   23 (  39 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_38,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_46,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_22,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_113,plain,(
    ! [A_38,B_39] : k1_setfam_1(k2_tarski(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_137,plain,(
    ! [A_42,B_43] : k1_setfam_1(k2_tarski(A_42,B_43)) = k3_xboole_0(B_43,A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_113])).

tff(c_30,plain,(
    ! [A_20,B_21] : k1_setfam_1(k2_tarski(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_143,plain,(
    ! [B_43,A_42] : k3_xboole_0(B_43,A_42) = k3_xboole_0(A_42,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_30])).

tff(c_46,plain,(
    r2_hidden('#skF_3',k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_160,plain,(
    r2_hidden('#skF_3',k3_xboole_0('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_46])).

tff(c_20,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_245,plain,(
    ! [D_53,B_54,A_55] :
      ( ~ r2_hidden(D_53,B_54)
      | r2_hidden(D_53,k2_xboole_0(A_55,B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_252,plain,(
    ! [D_56,A_57,B_58] :
      ( ~ r2_hidden(D_56,k3_xboole_0(A_57,B_58))
      | r2_hidden(D_56,A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_245])).

tff(c_262,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_160,c_252])).

tff(c_42,plain,(
    ! [B_29,A_28] :
      ( k1_funct_1(k6_relat_1(B_29),A_28) = A_28
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_50,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_36,plain,(
    ! [A_23] : v1_relat_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_38,plain,(
    ! [A_23] : v1_funct_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_32,plain,(
    ! [A_22] : k1_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_336,plain,(
    ! [B_81,C_82,A_83] :
      ( k1_funct_1(k5_relat_1(B_81,C_82),A_83) = k1_funct_1(C_82,k1_funct_1(B_81,A_83))
      | ~ r2_hidden(A_83,k1_relat_1(B_81))
      | ~ v1_funct_1(C_82)
      | ~ v1_relat_1(C_82)
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_340,plain,(
    ! [A_22,C_82,A_83] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_22),C_82),A_83) = k1_funct_1(C_82,k1_funct_1(k6_relat_1(A_22),A_83))
      | ~ r2_hidden(A_83,A_22)
      | ~ v1_funct_1(C_82)
      | ~ v1_relat_1(C_82)
      | ~ v1_funct_1(k6_relat_1(A_22))
      | ~ v1_relat_1(k6_relat_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_336])).

tff(c_1505,plain,(
    ! [A_148,C_149,A_150] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_148),C_149),A_150) = k1_funct_1(C_149,k1_funct_1(k6_relat_1(A_148),A_150))
      | ~ r2_hidden(A_150,A_148)
      | ~ v1_funct_1(C_149)
      | ~ v1_relat_1(C_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_340])).

tff(c_44,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'),'#skF_5'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1511,plain,
    ( k1_funct_1('#skF_5',k1_funct_1(k6_relat_1('#skF_4'),'#skF_3')) != k1_funct_1('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1505,c_44])).

tff(c_1517,plain,(
    k1_funct_1('#skF_5',k1_funct_1(k6_relat_1('#skF_4'),'#skF_3')) != k1_funct_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_262,c_1511])).

tff(c_1521,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1517])).

tff(c_1525,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_1521])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:54:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.56  
% 3.55/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.56  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 3.55/1.56  
% 3.55/1.56  %Foreground sorts:
% 3.55/1.56  
% 3.55/1.56  
% 3.55/1.56  %Background operators:
% 3.55/1.56  
% 3.55/1.56  
% 3.55/1.56  %Foreground operators:
% 3.55/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.55/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.55/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.55/1.56  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.55/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.55/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.55/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.55/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.55/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.55/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.55/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.55/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.55/1.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.55/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.55/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.55/1.56  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.55/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.55/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.55/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.55/1.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.55/1.56  
% 3.55/1.57  tff(f_38, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.55/1.57  tff(f_46, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.55/1.57  tff(f_80, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_1)).
% 3.55/1.57  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.55/1.57  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.55/1.57  tff(f_71, axiom, (![A, B]: (r2_hidden(A, B) => (k1_funct_1(k6_relat_1(B), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_1)).
% 3.55/1.57  tff(f_54, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.55/1.57  tff(f_50, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.55/1.57  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 3.55/1.57  tff(c_22, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.55/1.57  tff(c_113, plain, (![A_38, B_39]: (k1_setfam_1(k2_tarski(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.55/1.57  tff(c_137, plain, (![A_42, B_43]: (k1_setfam_1(k2_tarski(A_42, B_43))=k3_xboole_0(B_43, A_42))), inference(superposition, [status(thm), theory('equality')], [c_22, c_113])).
% 3.55/1.57  tff(c_30, plain, (![A_20, B_21]: (k1_setfam_1(k2_tarski(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.55/1.57  tff(c_143, plain, (![B_43, A_42]: (k3_xboole_0(B_43, A_42)=k3_xboole_0(A_42, B_43))), inference(superposition, [status(thm), theory('equality')], [c_137, c_30])).
% 3.55/1.57  tff(c_46, plain, (r2_hidden('#skF_3', k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.55/1.57  tff(c_160, plain, (r2_hidden('#skF_3', k3_xboole_0('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_46])).
% 3.55/1.57  tff(c_20, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k3_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.55/1.57  tff(c_245, plain, (![D_53, B_54, A_55]: (~r2_hidden(D_53, B_54) | r2_hidden(D_53, k2_xboole_0(A_55, B_54)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.55/1.57  tff(c_252, plain, (![D_56, A_57, B_58]: (~r2_hidden(D_56, k3_xboole_0(A_57, B_58)) | r2_hidden(D_56, A_57))), inference(superposition, [status(thm), theory('equality')], [c_20, c_245])).
% 3.55/1.57  tff(c_262, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_160, c_252])).
% 3.55/1.57  tff(c_42, plain, (![B_29, A_28]: (k1_funct_1(k6_relat_1(B_29), A_28)=A_28 | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.55/1.57  tff(c_50, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.55/1.57  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.55/1.57  tff(c_36, plain, (![A_23]: (v1_relat_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.55/1.57  tff(c_38, plain, (![A_23]: (v1_funct_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.55/1.57  tff(c_32, plain, (![A_22]: (k1_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.55/1.57  tff(c_336, plain, (![B_81, C_82, A_83]: (k1_funct_1(k5_relat_1(B_81, C_82), A_83)=k1_funct_1(C_82, k1_funct_1(B_81, A_83)) | ~r2_hidden(A_83, k1_relat_1(B_81)) | ~v1_funct_1(C_82) | ~v1_relat_1(C_82) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.55/1.57  tff(c_340, plain, (![A_22, C_82, A_83]: (k1_funct_1(k5_relat_1(k6_relat_1(A_22), C_82), A_83)=k1_funct_1(C_82, k1_funct_1(k6_relat_1(A_22), A_83)) | ~r2_hidden(A_83, A_22) | ~v1_funct_1(C_82) | ~v1_relat_1(C_82) | ~v1_funct_1(k6_relat_1(A_22)) | ~v1_relat_1(k6_relat_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_336])).
% 3.55/1.57  tff(c_1505, plain, (![A_148, C_149, A_150]: (k1_funct_1(k5_relat_1(k6_relat_1(A_148), C_149), A_150)=k1_funct_1(C_149, k1_funct_1(k6_relat_1(A_148), A_150)) | ~r2_hidden(A_150, A_148) | ~v1_funct_1(C_149) | ~v1_relat_1(C_149))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_340])).
% 3.55/1.57  tff(c_44, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'), '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.55/1.57  tff(c_1511, plain, (k1_funct_1('#skF_5', k1_funct_1(k6_relat_1('#skF_4'), '#skF_3'))!=k1_funct_1('#skF_5', '#skF_3') | ~r2_hidden('#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1505, c_44])).
% 3.55/1.57  tff(c_1517, plain, (k1_funct_1('#skF_5', k1_funct_1(k6_relat_1('#skF_4'), '#skF_3'))!=k1_funct_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_262, c_1511])).
% 3.55/1.57  tff(c_1521, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_42, c_1517])).
% 3.55/1.57  tff(c_1525, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_262, c_1521])).
% 3.55/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.57  
% 3.55/1.57  Inference rules
% 3.55/1.57  ----------------------
% 3.55/1.57  #Ref     : 0
% 3.55/1.57  #Sup     : 309
% 3.55/1.57  #Fact    : 6
% 3.55/1.57  #Define  : 0
% 3.55/1.57  #Split   : 0
% 3.55/1.57  #Chain   : 0
% 3.55/1.57  #Close   : 0
% 3.55/1.57  
% 3.55/1.57  Ordering : KBO
% 3.55/1.57  
% 3.55/1.57  Simplification rules
% 3.55/1.57  ----------------------
% 3.55/1.57  #Subsume      : 34
% 3.55/1.57  #Demod        : 66
% 3.55/1.57  #Tautology    : 116
% 3.55/1.57  #SimpNegUnit  : 0
% 3.55/1.57  #BackRed      : 3
% 3.55/1.57  
% 3.55/1.57  #Partial instantiations: 0
% 3.55/1.57  #Strategies tried      : 1
% 3.55/1.57  
% 3.55/1.57  Timing (in seconds)
% 3.55/1.57  ----------------------
% 3.55/1.57  Preprocessing        : 0.30
% 3.55/1.57  Parsing              : 0.15
% 3.55/1.57  CNF conversion       : 0.02
% 3.55/1.57  Main loop            : 0.49
% 3.55/1.58  Inferencing          : 0.18
% 3.55/1.58  Reduction            : 0.15
% 3.55/1.58  Demodulation         : 0.11
% 3.55/1.58  BG Simplification    : 0.03
% 3.55/1.58  Subsumption          : 0.10
% 3.55/1.58  Abstraction          : 0.04
% 3.55/1.58  MUC search           : 0.00
% 3.55/1.58  Cooper               : 0.00
% 3.55/1.58  Total                : 0.82
% 3.55/1.58  Index Insertion      : 0.00
% 3.55/1.58  Index Deletion       : 0.00
% 3.55/1.58  Index Matching       : 0.00
% 3.55/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
