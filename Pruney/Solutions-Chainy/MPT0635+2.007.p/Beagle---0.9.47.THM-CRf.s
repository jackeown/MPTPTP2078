%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:21 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   61 (  88 expanded)
%              Number of leaves         :   30 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   92 ( 152 expanded)
%              Number of equality atoms :   20 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    r2_hidden('#skF_3',k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_54,plain,(
    r2_hidden('#skF_3',k3_xboole_0('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_160,plain,(
    ! [C_53,B_54,A_55] :
      ( r2_hidden(C_53,B_54)
      | ~ r2_hidden(C_53,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_167,plain,(
    ! [B_56] :
      ( r2_hidden('#skF_3',B_56)
      | ~ r1_tarski(k3_xboole_0('#skF_4',k1_relat_1('#skF_5')),B_56) ) ),
    inference(resolution,[status(thm)],[c_54,c_160])).

tff(c_183,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_167])).

tff(c_24,plain,(
    ! [A_22] : v1_relat_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [A_22] : v1_funct_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    ! [A_27,C_31] :
      ( k1_funct_1(k6_relat_1(A_27),C_31) = C_31
      | ~ r2_hidden(C_31,A_27)
      | ~ v1_funct_1(k6_relat_1(A_27))
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_48,plain,(
    ! [A_27,C_31] :
      ( k1_funct_1(k6_relat_1(A_27),C_31) = C_31
      | ~ r2_hidden(C_31,A_27)
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_34])).

tff(c_50,plain,(
    ! [A_27,C_31] :
      ( k1_funct_1(k6_relat_1(A_27),C_31) = C_31
      | ~ r2_hidden(C_31,A_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_48])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_144,plain,(
    ! [A_48,B_49] :
      ( ~ r2_hidden('#skF_1'(A_48,B_49),B_49)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_149,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_144])).

tff(c_44,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,(
    ! [A_27] :
      ( k1_relat_1(k6_relat_1(A_27)) = A_27
      | ~ v1_funct_1(k6_relat_1(A_27))
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_46,plain,(
    ! [A_27] :
      ( k1_relat_1(k6_relat_1(A_27)) = A_27
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_36])).

tff(c_52,plain,(
    ! [A_27] : k1_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_46])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_186,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_3',B_4)
      | ~ r1_tarski('#skF_4',B_4) ) ),
    inference(resolution,[status(thm)],[c_183,c_4])).

tff(c_387,plain,(
    ! [B_101,C_102,A_103] :
      ( k1_funct_1(k5_relat_1(B_101,C_102),A_103) = k1_funct_1(C_102,k1_funct_1(B_101,A_103))
      | ~ r2_hidden(A_103,k1_relat_1(B_101))
      | ~ v1_funct_1(C_102)
      | ~ v1_relat_1(C_102)
      | ~ v1_funct_1(B_101)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_482,plain,(
    ! [B_112,C_113] :
      ( k1_funct_1(k5_relat_1(B_112,C_113),'#skF_3') = k1_funct_1(C_113,k1_funct_1(B_112,'#skF_3'))
      | ~ v1_funct_1(C_113)
      | ~ v1_relat_1(C_113)
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112)
      | ~ r1_tarski('#skF_4',k1_relat_1(B_112)) ) ),
    inference(resolution,[status(thm)],[c_186,c_387])).

tff(c_484,plain,(
    ! [A_27,C_113] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_27),C_113),'#skF_3') = k1_funct_1(C_113,k1_funct_1(k6_relat_1(A_27),'#skF_3'))
      | ~ v1_funct_1(C_113)
      | ~ v1_relat_1(C_113)
      | ~ v1_funct_1(k6_relat_1(A_27))
      | ~ v1_relat_1(k6_relat_1(A_27))
      | ~ r1_tarski('#skF_4',A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_482])).

tff(c_574,plain,(
    ! [A_133,C_134] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_133),C_134),'#skF_3') = k1_funct_1(C_134,k1_funct_1(k6_relat_1(A_133),'#skF_3'))
      | ~ v1_funct_1(C_134)
      | ~ v1_relat_1(C_134)
      | ~ r1_tarski('#skF_4',A_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_484])).

tff(c_38,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'),'#skF_5'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_580,plain,
    ( k1_funct_1('#skF_5',k1_funct_1(k6_relat_1('#skF_4'),'#skF_3')) != k1_funct_1('#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_38])).

tff(c_586,plain,(
    k1_funct_1('#skF_5',k1_funct_1(k6_relat_1('#skF_4'),'#skF_3')) != k1_funct_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_44,c_42,c_580])).

tff(c_590,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_586])).

tff(c_594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_590])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n020.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 11:55:22 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.47  
% 2.73/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.47  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.10/1.47  
% 3.10/1.47  %Foreground sorts:
% 3.10/1.47  
% 3.10/1.47  
% 3.10/1.47  %Background operators:
% 3.10/1.47  
% 3.10/1.47  
% 3.10/1.47  %Foreground operators:
% 3.10/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.10/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.10/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.10/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.10/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.10/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.10/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.10/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.10/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.10/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.10/1.47  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.10/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.10/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.10/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.10/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.10/1.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.10/1.47  
% 3.10/1.48  tff(f_36, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.10/1.48  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.10/1.48  tff(f_87, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_1)).
% 3.10/1.48  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.10/1.48  tff(f_52, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.10/1.48  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 3.10/1.48  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 3.10/1.48  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.10/1.48  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.10/1.48  tff(c_40, plain, (r2_hidden('#skF_3', k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.10/1.48  tff(c_54, plain, (r2_hidden('#skF_3', k3_xboole_0('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40])).
% 3.10/1.48  tff(c_160, plain, (![C_53, B_54, A_55]: (r2_hidden(C_53, B_54) | ~r2_hidden(C_53, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.10/1.48  tff(c_167, plain, (![B_56]: (r2_hidden('#skF_3', B_56) | ~r1_tarski(k3_xboole_0('#skF_4', k1_relat_1('#skF_5')), B_56))), inference(resolution, [status(thm)], [c_54, c_160])).
% 3.10/1.48  tff(c_183, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_10, c_167])).
% 3.10/1.48  tff(c_24, plain, (![A_22]: (v1_relat_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.10/1.48  tff(c_26, plain, (![A_22]: (v1_funct_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.10/1.48  tff(c_34, plain, (![A_27, C_31]: (k1_funct_1(k6_relat_1(A_27), C_31)=C_31 | ~r2_hidden(C_31, A_27) | ~v1_funct_1(k6_relat_1(A_27)) | ~v1_relat_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.10/1.48  tff(c_48, plain, (![A_27, C_31]: (k1_funct_1(k6_relat_1(A_27), C_31)=C_31 | ~r2_hidden(C_31, A_27) | ~v1_relat_1(k6_relat_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_34])).
% 3.10/1.48  tff(c_50, plain, (![A_27, C_31]: (k1_funct_1(k6_relat_1(A_27), C_31)=C_31 | ~r2_hidden(C_31, A_27))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_48])).
% 3.10/1.48  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.10/1.48  tff(c_144, plain, (![A_48, B_49]: (~r2_hidden('#skF_1'(A_48, B_49), B_49) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.10/1.48  tff(c_149, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_8, c_144])).
% 3.10/1.48  tff(c_44, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.10/1.48  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.10/1.48  tff(c_36, plain, (![A_27]: (k1_relat_1(k6_relat_1(A_27))=A_27 | ~v1_funct_1(k6_relat_1(A_27)) | ~v1_relat_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.10/1.48  tff(c_46, plain, (![A_27]: (k1_relat_1(k6_relat_1(A_27))=A_27 | ~v1_relat_1(k6_relat_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_36])).
% 3.10/1.48  tff(c_52, plain, (![A_27]: (k1_relat_1(k6_relat_1(A_27))=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_46])).
% 3.10/1.48  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.10/1.48  tff(c_186, plain, (![B_4]: (r2_hidden('#skF_3', B_4) | ~r1_tarski('#skF_4', B_4))), inference(resolution, [status(thm)], [c_183, c_4])).
% 3.10/1.48  tff(c_387, plain, (![B_101, C_102, A_103]: (k1_funct_1(k5_relat_1(B_101, C_102), A_103)=k1_funct_1(C_102, k1_funct_1(B_101, A_103)) | ~r2_hidden(A_103, k1_relat_1(B_101)) | ~v1_funct_1(C_102) | ~v1_relat_1(C_102) | ~v1_funct_1(B_101) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.10/1.48  tff(c_482, plain, (![B_112, C_113]: (k1_funct_1(k5_relat_1(B_112, C_113), '#skF_3')=k1_funct_1(C_113, k1_funct_1(B_112, '#skF_3')) | ~v1_funct_1(C_113) | ~v1_relat_1(C_113) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112) | ~r1_tarski('#skF_4', k1_relat_1(B_112)))), inference(resolution, [status(thm)], [c_186, c_387])).
% 3.10/1.48  tff(c_484, plain, (![A_27, C_113]: (k1_funct_1(k5_relat_1(k6_relat_1(A_27), C_113), '#skF_3')=k1_funct_1(C_113, k1_funct_1(k6_relat_1(A_27), '#skF_3')) | ~v1_funct_1(C_113) | ~v1_relat_1(C_113) | ~v1_funct_1(k6_relat_1(A_27)) | ~v1_relat_1(k6_relat_1(A_27)) | ~r1_tarski('#skF_4', A_27))), inference(superposition, [status(thm), theory('equality')], [c_52, c_482])).
% 3.10/1.48  tff(c_574, plain, (![A_133, C_134]: (k1_funct_1(k5_relat_1(k6_relat_1(A_133), C_134), '#skF_3')=k1_funct_1(C_134, k1_funct_1(k6_relat_1(A_133), '#skF_3')) | ~v1_funct_1(C_134) | ~v1_relat_1(C_134) | ~r1_tarski('#skF_4', A_133))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_484])).
% 3.10/1.48  tff(c_38, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'), '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.10/1.48  tff(c_580, plain, (k1_funct_1('#skF_5', k1_funct_1(k6_relat_1('#skF_4'), '#skF_3'))!=k1_funct_1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r1_tarski('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_574, c_38])).
% 3.10/1.48  tff(c_586, plain, (k1_funct_1('#skF_5', k1_funct_1(k6_relat_1('#skF_4'), '#skF_3'))!=k1_funct_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_44, c_42, c_580])).
% 3.10/1.48  tff(c_590, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_50, c_586])).
% 3.10/1.48  tff(c_594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_183, c_590])).
% 3.10/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.48  
% 3.10/1.48  Inference rules
% 3.10/1.48  ----------------------
% 3.10/1.48  #Ref     : 0
% 3.10/1.48  #Sup     : 132
% 3.10/1.48  #Fact    : 0
% 3.10/1.48  #Define  : 0
% 3.10/1.48  #Split   : 0
% 3.10/1.48  #Chain   : 0
% 3.10/1.48  #Close   : 0
% 3.10/1.48  
% 3.10/1.48  Ordering : KBO
% 3.10/1.48  
% 3.10/1.48  Simplification rules
% 3.10/1.48  ----------------------
% 3.10/1.48  #Subsume      : 29
% 3.10/1.48  #Demod        : 47
% 3.10/1.48  #Tautology    : 42
% 3.10/1.48  #SimpNegUnit  : 0
% 3.10/1.48  #BackRed      : 0
% 3.10/1.48  
% 3.10/1.48  #Partial instantiations: 0
% 3.10/1.48  #Strategies tried      : 1
% 3.10/1.48  
% 3.10/1.48  Timing (in seconds)
% 3.10/1.48  ----------------------
% 3.10/1.49  Preprocessing        : 0.34
% 3.10/1.49  Parsing              : 0.18
% 3.10/1.49  CNF conversion       : 0.02
% 3.10/1.49  Main loop            : 0.35
% 3.10/1.49  Inferencing          : 0.12
% 3.10/1.49  Reduction            : 0.11
% 3.10/1.49  Demodulation         : 0.08
% 3.10/1.49  BG Simplification    : 0.02
% 3.10/1.49  Subsumption          : 0.07
% 3.10/1.49  Abstraction          : 0.02
% 3.10/1.49  MUC search           : 0.00
% 3.10/1.49  Cooper               : 0.00
% 3.10/1.49  Total                : 0.72
% 3.10/1.49  Index Insertion      : 0.00
% 3.10/1.49  Index Deletion       : 0.00
% 3.10/1.49  Index Matching       : 0.00
% 3.10/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
