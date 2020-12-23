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
% DateTime   : Thu Dec  3 10:03:21 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   48 (  63 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 (  95 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    r2_hidden('#skF_2',k3_xboole_0(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_33,plain,(
    r2_hidden('#skF_2',k3_xboole_0('#skF_3',k1_relat_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_130,plain,(
    ! [C_39,B_40,A_41] :
      ( r2_hidden(C_39,B_40)
      | ~ r2_hidden(C_39,A_41)
      | ~ r1_tarski(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_137,plain,(
    ! [B_42] :
      ( r2_hidden('#skF_2',B_42)
      | ~ r1_tarski(k3_xboole_0('#skF_3',k1_relat_1('#skF_4')),B_42) ) ),
    inference(resolution,[status(thm)],[c_33,c_130])).

tff(c_153,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_137])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( k1_funct_1(k6_relat_1(B_19),A_18) = A_18
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_18,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    ! [A_13] : v1_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    ! [A_12] : k1_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_188,plain,(
    ! [B_49,C_50,A_51] :
      ( k1_funct_1(k5_relat_1(B_49,C_50),A_51) = k1_funct_1(C_50,k1_funct_1(B_49,A_51))
      | ~ r2_hidden(A_51,k1_relat_1(B_49))
      | ~ v1_funct_1(C_50)
      | ~ v1_relat_1(C_50)
      | ~ v1_funct_1(B_49)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_198,plain,(
    ! [A_12,C_50,A_51] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_12),C_50),A_51) = k1_funct_1(C_50,k1_funct_1(k6_relat_1(A_12),A_51))
      | ~ r2_hidden(A_51,A_12)
      | ~ v1_funct_1(C_50)
      | ~ v1_relat_1(C_50)
      | ~ v1_funct_1(k6_relat_1(A_12))
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_188])).

tff(c_302,plain,(
    ! [A_72,C_73,A_74] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_72),C_73),A_74) = k1_funct_1(C_73,k1_funct_1(k6_relat_1(A_72),A_74))
      | ~ r2_hidden(A_74,A_72)
      | ~ v1_funct_1(C_73)
      | ~ v1_relat_1(C_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_198])).

tff(c_26,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_3'),'#skF_4'),'#skF_2') != k1_funct_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_308,plain,
    ( k1_funct_1('#skF_4',k1_funct_1(k6_relat_1('#skF_3'),'#skF_2')) != k1_funct_1('#skF_4','#skF_2')
    | ~ r2_hidden('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_26])).

tff(c_314,plain,(
    k1_funct_1('#skF_4',k1_funct_1(k6_relat_1('#skF_3'),'#skF_2')) != k1_funct_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_153,c_308])).

tff(c_318,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_314])).

tff(c_322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_318])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.46  
% 2.23/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.46  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.23/1.46  
% 2.23/1.46  %Foreground sorts:
% 2.23/1.46  
% 2.23/1.46  
% 2.23/1.46  %Background operators:
% 2.23/1.46  
% 2.23/1.46  
% 2.23/1.46  %Foreground operators:
% 2.23/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.23/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.23/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.23/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.23/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.23/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.23/1.46  
% 2.55/1.47  tff(f_36, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.55/1.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.55/1.47  tff(f_72, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_1)).
% 2.55/1.47  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.55/1.47  tff(f_63, axiom, (![A, B]: (r2_hidden(A, B) => (k1_funct_1(k6_relat_1(B), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_1)).
% 2.55/1.47  tff(f_46, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.55/1.47  tff(f_42, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.55/1.47  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 2.55/1.47  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.55/1.47  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.55/1.47  tff(c_28, plain, (r2_hidden('#skF_2', k3_xboole_0(k1_relat_1('#skF_4'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.55/1.47  tff(c_33, plain, (r2_hidden('#skF_2', k3_xboole_0('#skF_3', k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 2.55/1.47  tff(c_130, plain, (![C_39, B_40, A_41]: (r2_hidden(C_39, B_40) | ~r2_hidden(C_39, A_41) | ~r1_tarski(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.55/1.47  tff(c_137, plain, (![B_42]: (r2_hidden('#skF_2', B_42) | ~r1_tarski(k3_xboole_0('#skF_3', k1_relat_1('#skF_4')), B_42))), inference(resolution, [status(thm)], [c_33, c_130])).
% 2.55/1.47  tff(c_153, plain, (r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_10, c_137])).
% 2.55/1.47  tff(c_24, plain, (![B_19, A_18]: (k1_funct_1(k6_relat_1(B_19), A_18)=A_18 | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.55/1.47  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.55/1.47  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.55/1.47  tff(c_18, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.55/1.47  tff(c_20, plain, (![A_13]: (v1_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.55/1.47  tff(c_14, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.55/1.47  tff(c_188, plain, (![B_49, C_50, A_51]: (k1_funct_1(k5_relat_1(B_49, C_50), A_51)=k1_funct_1(C_50, k1_funct_1(B_49, A_51)) | ~r2_hidden(A_51, k1_relat_1(B_49)) | ~v1_funct_1(C_50) | ~v1_relat_1(C_50) | ~v1_funct_1(B_49) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.55/1.47  tff(c_198, plain, (![A_12, C_50, A_51]: (k1_funct_1(k5_relat_1(k6_relat_1(A_12), C_50), A_51)=k1_funct_1(C_50, k1_funct_1(k6_relat_1(A_12), A_51)) | ~r2_hidden(A_51, A_12) | ~v1_funct_1(C_50) | ~v1_relat_1(C_50) | ~v1_funct_1(k6_relat_1(A_12)) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_188])).
% 2.55/1.47  tff(c_302, plain, (![A_72, C_73, A_74]: (k1_funct_1(k5_relat_1(k6_relat_1(A_72), C_73), A_74)=k1_funct_1(C_73, k1_funct_1(k6_relat_1(A_72), A_74)) | ~r2_hidden(A_74, A_72) | ~v1_funct_1(C_73) | ~v1_relat_1(C_73))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_198])).
% 2.55/1.47  tff(c_26, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_3'), '#skF_4'), '#skF_2')!=k1_funct_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.55/1.47  tff(c_308, plain, (k1_funct_1('#skF_4', k1_funct_1(k6_relat_1('#skF_3'), '#skF_2'))!=k1_funct_1('#skF_4', '#skF_2') | ~r2_hidden('#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_302, c_26])).
% 2.55/1.47  tff(c_314, plain, (k1_funct_1('#skF_4', k1_funct_1(k6_relat_1('#skF_3'), '#skF_2'))!=k1_funct_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_153, c_308])).
% 2.55/1.47  tff(c_318, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_314])).
% 2.55/1.47  tff(c_322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_153, c_318])).
% 2.55/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.47  
% 2.55/1.47  Inference rules
% 2.55/1.47  ----------------------
% 2.55/1.47  #Ref     : 0
% 2.55/1.47  #Sup     : 68
% 2.55/1.47  #Fact    : 0
% 2.55/1.47  #Define  : 0
% 2.55/1.47  #Split   : 0
% 2.55/1.47  #Chain   : 0
% 2.55/1.47  #Close   : 0
% 2.55/1.47  
% 2.55/1.47  Ordering : KBO
% 2.55/1.47  
% 2.55/1.47  Simplification rules
% 2.55/1.47  ----------------------
% 2.55/1.47  #Subsume      : 8
% 2.55/1.47  #Demod        : 17
% 2.55/1.47  #Tautology    : 28
% 2.55/1.47  #SimpNegUnit  : 0
% 2.55/1.47  #BackRed      : 0
% 2.55/1.47  
% 2.55/1.47  #Partial instantiations: 0
% 2.55/1.47  #Strategies tried      : 1
% 2.55/1.47  
% 2.55/1.47  Timing (in seconds)
% 2.55/1.47  ----------------------
% 2.55/1.47  Preprocessing        : 0.37
% 2.55/1.47  Parsing              : 0.18
% 2.55/1.47  CNF conversion       : 0.04
% 2.55/1.47  Main loop            : 0.28
% 2.55/1.47  Inferencing          : 0.11
% 2.55/1.47  Reduction            : 0.09
% 2.55/1.47  Demodulation         : 0.07
% 2.55/1.47  BG Simplification    : 0.02
% 2.55/1.47  Subsumption          : 0.05
% 2.55/1.47  Abstraction          : 0.01
% 2.55/1.47  MUC search           : 0.00
% 2.55/1.47  Cooper               : 0.00
% 2.55/1.47  Total                : 0.68
% 2.55/1.48  Index Insertion      : 0.00
% 2.55/1.48  Index Deletion       : 0.00
% 2.55/1.48  Index Matching       : 0.00
% 2.55/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
