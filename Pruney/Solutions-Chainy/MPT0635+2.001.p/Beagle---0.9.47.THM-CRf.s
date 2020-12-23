%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:20 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   61 (  86 expanded)
%              Number of leaves         :   34 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   84 ( 129 expanded)
%              Number of equality atoms :   25 (  39 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_36,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_40,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k6_relat_1(A)
      <=> ! [C,D] :
            ( r2_hidden(k4_tarski(C,D),B)
          <=> ( r2_hidden(C,A)
              & C = D ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_20,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_135,plain,(
    ! [A_38,B_39] : k1_setfam_1(k2_tarski(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_150,plain,(
    ! [B_40,A_41] : k1_setfam_1(k2_tarski(B_40,A_41)) = k3_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_135])).

tff(c_24,plain,(
    ! [A_11,B_12] : k1_setfam_1(k2_tarski(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_156,plain,(
    ! [B_40,A_41] : k3_xboole_0(B_40,A_41) = k3_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_24])).

tff(c_62,plain,(
    r2_hidden('#skF_7',k3_xboole_0(k1_relat_1('#skF_9'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_173,plain,(
    r2_hidden('#skF_7',k3_xboole_0('#skF_8',k1_relat_1('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_62])).

tff(c_207,plain,(
    ! [D_44,A_45,B_46] :
      ( r2_hidden(D_44,A_45)
      | ~ r2_hidden(D_44,k3_xboole_0(A_45,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_217,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_173,c_207])).

tff(c_48,plain,(
    ! [A_22] : v1_relat_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_50,plain,(
    ! [A_22] : v1_funct_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_38,plain,(
    ! [D_20,A_13] :
      ( r2_hidden(k4_tarski(D_20,D_20),k6_relat_1(A_13))
      | ~ r2_hidden(D_20,A_13)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_72,plain,(
    ! [D_20,A_13] :
      ( r2_hidden(k4_tarski(D_20,D_20),k6_relat_1(A_13))
      | ~ r2_hidden(D_20,A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38])).

tff(c_257,plain,(
    ! [C_61,A_62,B_63] :
      ( k1_funct_1(C_61,A_62) = B_63
      | ~ r2_hidden(k4_tarski(A_62,B_63),C_61)
      | ~ v1_funct_1(C_61)
      | ~ v1_relat_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_264,plain,(
    ! [A_13,D_20] :
      ( k1_funct_1(k6_relat_1(A_13),D_20) = D_20
      | ~ v1_funct_1(k6_relat_1(A_13))
      | ~ v1_relat_1(k6_relat_1(A_13))
      | ~ r2_hidden(D_20,A_13) ) ),
    inference(resolution,[status(thm)],[c_72,c_257])).

tff(c_268,plain,(
    ! [A_13,D_20] :
      ( k1_funct_1(k6_relat_1(A_13),D_20) = D_20
      | ~ r2_hidden(D_20,A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_264])).

tff(c_66,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_64,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_44,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1066,plain,(
    ! [B_146,C_147,A_148] :
      ( k1_funct_1(k5_relat_1(B_146,C_147),A_148) = k1_funct_1(C_147,k1_funct_1(B_146,A_148))
      | ~ r2_hidden(A_148,k1_relat_1(B_146))
      | ~ v1_funct_1(C_147)
      | ~ v1_relat_1(C_147)
      | ~ v1_funct_1(B_146)
      | ~ v1_relat_1(B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1156,plain,(
    ! [A_21,C_147,A_148] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_21),C_147),A_148) = k1_funct_1(C_147,k1_funct_1(k6_relat_1(A_21),A_148))
      | ~ r2_hidden(A_148,A_21)
      | ~ v1_funct_1(C_147)
      | ~ v1_relat_1(C_147)
      | ~ v1_funct_1(k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1066])).

tff(c_1469,plain,(
    ! [A_176,C_177,A_178] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_176),C_177),A_178) = k1_funct_1(C_177,k1_funct_1(k6_relat_1(A_176),A_178))
      | ~ r2_hidden(A_178,A_176)
      | ~ v1_funct_1(C_177)
      | ~ v1_relat_1(C_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_1156])).

tff(c_60,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_8'),'#skF_9'),'#skF_7') != k1_funct_1('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1482,plain,
    ( k1_funct_1('#skF_9',k1_funct_1(k6_relat_1('#skF_8'),'#skF_7')) != k1_funct_1('#skF_9','#skF_7')
    | ~ r2_hidden('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1469,c_60])).

tff(c_1488,plain,(
    k1_funct_1('#skF_9',k1_funct_1(k6_relat_1('#skF_8'),'#skF_7')) != k1_funct_1('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_217,c_1482])).

tff(c_1492,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_1488])).

tff(c_1496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_1492])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:05:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.86/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.68  
% 3.86/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.68  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4
% 3.86/1.68  
% 3.86/1.68  %Foreground sorts:
% 3.86/1.68  
% 3.86/1.68  
% 3.86/1.68  %Background operators:
% 3.86/1.68  
% 3.86/1.68  
% 3.86/1.68  %Foreground operators:
% 3.86/1.68  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.86/1.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.86/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.86/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.86/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.86/1.68  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.86/1.68  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.86/1.68  tff('#skF_7', type, '#skF_7': $i).
% 3.86/1.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.86/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.86/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.86/1.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.86/1.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.86/1.68  tff('#skF_9', type, '#skF_9': $i).
% 3.86/1.68  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.86/1.68  tff('#skF_8', type, '#skF_8': $i).
% 3.86/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.86/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.86/1.68  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.86/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.86/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.86/1.68  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.86/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.86/1.68  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.86/1.68  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.86/1.68  
% 4.09/1.69  tff(f_36, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.09/1.69  tff(f_40, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.09/1.69  tff(f_91, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_1)).
% 4.09/1.69  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.09/1.69  tff(f_59, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.09/1.69  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => ((B = k6_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> (r2_hidden(C, A) & (C = D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_relat_1)).
% 4.09/1.69  tff(f_82, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 4.09/1.69  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.09/1.69  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 4.09/1.69  tff(c_20, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.09/1.69  tff(c_135, plain, (![A_38, B_39]: (k1_setfam_1(k2_tarski(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.09/1.69  tff(c_150, plain, (![B_40, A_41]: (k1_setfam_1(k2_tarski(B_40, A_41))=k3_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_20, c_135])).
% 4.09/1.69  tff(c_24, plain, (![A_11, B_12]: (k1_setfam_1(k2_tarski(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.09/1.69  tff(c_156, plain, (![B_40, A_41]: (k3_xboole_0(B_40, A_41)=k3_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_150, c_24])).
% 4.09/1.69  tff(c_62, plain, (r2_hidden('#skF_7', k3_xboole_0(k1_relat_1('#skF_9'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.09/1.69  tff(c_173, plain, (r2_hidden('#skF_7', k3_xboole_0('#skF_8', k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_62])).
% 4.09/1.69  tff(c_207, plain, (![D_44, A_45, B_46]: (r2_hidden(D_44, A_45) | ~r2_hidden(D_44, k3_xboole_0(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.09/1.69  tff(c_217, plain, (r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_173, c_207])).
% 4.09/1.69  tff(c_48, plain, (![A_22]: (v1_relat_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.09/1.69  tff(c_50, plain, (![A_22]: (v1_funct_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.09/1.69  tff(c_38, plain, (![D_20, A_13]: (r2_hidden(k4_tarski(D_20, D_20), k6_relat_1(A_13)) | ~r2_hidden(D_20, A_13) | ~v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.09/1.69  tff(c_72, plain, (![D_20, A_13]: (r2_hidden(k4_tarski(D_20, D_20), k6_relat_1(A_13)) | ~r2_hidden(D_20, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38])).
% 4.09/1.69  tff(c_257, plain, (![C_61, A_62, B_63]: (k1_funct_1(C_61, A_62)=B_63 | ~r2_hidden(k4_tarski(A_62, B_63), C_61) | ~v1_funct_1(C_61) | ~v1_relat_1(C_61))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.09/1.69  tff(c_264, plain, (![A_13, D_20]: (k1_funct_1(k6_relat_1(A_13), D_20)=D_20 | ~v1_funct_1(k6_relat_1(A_13)) | ~v1_relat_1(k6_relat_1(A_13)) | ~r2_hidden(D_20, A_13))), inference(resolution, [status(thm)], [c_72, c_257])).
% 4.09/1.69  tff(c_268, plain, (![A_13, D_20]: (k1_funct_1(k6_relat_1(A_13), D_20)=D_20 | ~r2_hidden(D_20, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_264])).
% 4.09/1.69  tff(c_66, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.09/1.69  tff(c_64, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.09/1.69  tff(c_44, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.09/1.69  tff(c_1066, plain, (![B_146, C_147, A_148]: (k1_funct_1(k5_relat_1(B_146, C_147), A_148)=k1_funct_1(C_147, k1_funct_1(B_146, A_148)) | ~r2_hidden(A_148, k1_relat_1(B_146)) | ~v1_funct_1(C_147) | ~v1_relat_1(C_147) | ~v1_funct_1(B_146) | ~v1_relat_1(B_146))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.09/1.69  tff(c_1156, plain, (![A_21, C_147, A_148]: (k1_funct_1(k5_relat_1(k6_relat_1(A_21), C_147), A_148)=k1_funct_1(C_147, k1_funct_1(k6_relat_1(A_21), A_148)) | ~r2_hidden(A_148, A_21) | ~v1_funct_1(C_147) | ~v1_relat_1(C_147) | ~v1_funct_1(k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1066])).
% 4.09/1.69  tff(c_1469, plain, (![A_176, C_177, A_178]: (k1_funct_1(k5_relat_1(k6_relat_1(A_176), C_177), A_178)=k1_funct_1(C_177, k1_funct_1(k6_relat_1(A_176), A_178)) | ~r2_hidden(A_178, A_176) | ~v1_funct_1(C_177) | ~v1_relat_1(C_177))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_1156])).
% 4.09/1.69  tff(c_60, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_8'), '#skF_9'), '#skF_7')!=k1_funct_1('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.09/1.69  tff(c_1482, plain, (k1_funct_1('#skF_9', k1_funct_1(k6_relat_1('#skF_8'), '#skF_7'))!=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden('#skF_7', '#skF_8') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1469, c_60])).
% 4.09/1.69  tff(c_1488, plain, (k1_funct_1('#skF_9', k1_funct_1(k6_relat_1('#skF_8'), '#skF_7'))!=k1_funct_1('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_217, c_1482])).
% 4.09/1.69  tff(c_1492, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_268, c_1488])).
% 4.09/1.69  tff(c_1496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_1492])).
% 4.09/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.69  
% 4.09/1.69  Inference rules
% 4.09/1.69  ----------------------
% 4.09/1.69  #Ref     : 0
% 4.09/1.69  #Sup     : 325
% 4.09/1.69  #Fact    : 0
% 4.09/1.69  #Define  : 0
% 4.09/1.69  #Split   : 0
% 4.09/1.69  #Chain   : 0
% 4.09/1.69  #Close   : 0
% 4.09/1.69  
% 4.09/1.69  Ordering : KBO
% 4.09/1.69  
% 4.09/1.69  Simplification rules
% 4.09/1.69  ----------------------
% 4.09/1.69  #Subsume      : 102
% 4.09/1.69  #Demod        : 155
% 4.09/1.69  #Tautology    : 56
% 4.09/1.69  #SimpNegUnit  : 0
% 4.09/1.69  #BackRed      : 1
% 4.09/1.69  
% 4.09/1.69  #Partial instantiations: 0
% 4.09/1.69  #Strategies tried      : 1
% 4.09/1.69  
% 4.09/1.69  Timing (in seconds)
% 4.09/1.69  ----------------------
% 4.09/1.69  Preprocessing        : 0.34
% 4.09/1.70  Parsing              : 0.18
% 4.09/1.70  CNF conversion       : 0.02
% 4.09/1.70  Main loop            : 0.59
% 4.09/1.70  Inferencing          : 0.20
% 4.09/1.70  Reduction            : 0.20
% 4.09/1.70  Demodulation         : 0.16
% 4.09/1.70  BG Simplification    : 0.03
% 4.09/1.70  Subsumption          : 0.12
% 4.09/1.70  Abstraction          : 0.04
% 4.09/1.70  MUC search           : 0.00
% 4.09/1.70  Cooper               : 0.00
% 4.09/1.70  Total                : 0.95
% 4.09/1.70  Index Insertion      : 0.00
% 4.09/1.70  Index Deletion       : 0.00
% 4.09/1.70  Index Matching       : 0.00
% 4.09/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
