%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:21 EST 2020

% Result     : Theorem 5.39s
% Output     : CNFRefutation 5.39s
% Verified   : 
% Statistics : Number of formulae       :   52 (  76 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 109 expanded)
%              Number of equality atoms :   22 (  43 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_36,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_40,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_76,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k1_relat_1(k5_relat_1(k6_relat_1(A),B)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_20,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_87,plain,(
    ! [A_28,B_29] : k1_setfam_1(k2_tarski(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_102,plain,(
    ! [B_30,A_31] : k1_setfam_1(k2_tarski(B_30,A_31)) = k3_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_87])).

tff(c_24,plain,(
    ! [A_11,B_12] : k1_setfam_1(k2_tarski(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_108,plain,(
    ! [B_30,A_31] : k3_xboole_0(B_30,A_31) = k3_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_24])).

tff(c_38,plain,(
    r2_hidden('#skF_3',k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_125,plain,(
    r2_hidden('#skF_3',k3_xboole_0('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_38])).

tff(c_160,plain,(
    ! [D_34,A_35,B_36] :
      ( r2_hidden(D_34,A_35)
      | ~ r2_hidden(D_34,k3_xboole_0(A_35,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_170,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_125,c_160])).

tff(c_32,plain,(
    ! [B_19,A_18] :
      ( k1_funct_1(k6_relat_1(B_19),A_18) = A_18
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    ! [A_13] : v1_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    ! [A_20,B_21] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(A_20),B_21)) = k3_xboole_0(k1_relat_1(B_21),A_20)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_600,plain,(
    ! [C_90,B_91,A_92] :
      ( k1_funct_1(k5_relat_1(C_90,B_91),A_92) = k1_funct_1(B_91,k1_funct_1(C_90,A_92))
      | ~ r2_hidden(A_92,k1_relat_1(k5_relat_1(C_90,B_91)))
      | ~ v1_funct_1(C_90)
      | ~ v1_relat_1(C_90)
      | ~ v1_funct_1(B_91)
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_655,plain,(
    ! [A_20,B_21,A_92] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_20),B_21),A_92) = k1_funct_1(B_21,k1_funct_1(k6_relat_1(A_20),A_92))
      | ~ r2_hidden(A_92,k3_xboole_0(k1_relat_1(B_21),A_20))
      | ~ v1_funct_1(k6_relat_1(A_20))
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_600])).

tff(c_1215,plain,(
    ! [A_132,B_133,A_134] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_132),B_133),A_134) = k1_funct_1(B_133,k1_funct_1(k6_relat_1(A_132),A_134))
      | ~ r2_hidden(A_134,k3_xboole_0(k1_relat_1(B_133),A_132))
      | ~ v1_funct_1(B_133)
      | ~ v1_relat_1(B_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_655])).

tff(c_2622,plain,(
    ! [B_215,B_216,A_217] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(B_215),B_216),A_217) = k1_funct_1(B_216,k1_funct_1(k6_relat_1(B_215),A_217))
      | ~ r2_hidden(A_217,k3_xboole_0(B_215,k1_relat_1(B_216)))
      | ~ v1_funct_1(B_216)
      | ~ v1_relat_1(B_216) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_1215])).

tff(c_2860,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'),'#skF_5'),'#skF_3') = k1_funct_1('#skF_5',k1_funct_1(k6_relat_1('#skF_4'),'#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_125,c_2622])).

tff(c_2928,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'),'#skF_5'),'#skF_3') = k1_funct_1('#skF_5',k1_funct_1(k6_relat_1('#skF_4'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2860])).

tff(c_36,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'),'#skF_5'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2929,plain,(
    k1_funct_1('#skF_5',k1_funct_1(k6_relat_1('#skF_4'),'#skF_3')) != k1_funct_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2928,c_36])).

tff(c_2936,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2929])).

tff(c_2940,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_2936])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:11:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.39/2.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.39/2.00  
% 5.39/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.39/2.00  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 5.39/2.00  
% 5.39/2.00  %Foreground sorts:
% 5.39/2.00  
% 5.39/2.00  
% 5.39/2.00  %Background operators:
% 5.39/2.00  
% 5.39/2.00  
% 5.39/2.00  %Foreground operators:
% 5.39/2.00  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.39/2.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.39/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.39/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.39/2.00  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.39/2.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.39/2.00  tff('#skF_5', type, '#skF_5': $i).
% 5.39/2.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.39/2.00  tff('#skF_3', type, '#skF_3': $i).
% 5.39/2.00  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.39/2.00  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.39/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.39/2.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.39/2.00  tff('#skF_4', type, '#skF_4': $i).
% 5.39/2.00  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.39/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.39/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.39/2.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.39/2.00  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.39/2.00  
% 5.39/2.01  tff(f_36, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.39/2.01  tff(f_40, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.39/2.01  tff(f_76, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_1)).
% 5.39/2.01  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.39/2.01  tff(f_61, axiom, (![A, B]: (r2_hidden(A, B) => (k1_funct_1(k6_relat_1(B), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_1)).
% 5.39/2.01  tff(f_44, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.39/2.01  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k1_relat_1(k5_relat_1(k6_relat_1(A), B)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_funct_1)).
% 5.39/2.01  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 5.39/2.01  tff(c_20, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.39/2.01  tff(c_87, plain, (![A_28, B_29]: (k1_setfam_1(k2_tarski(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.39/2.01  tff(c_102, plain, (![B_30, A_31]: (k1_setfam_1(k2_tarski(B_30, A_31))=k3_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_20, c_87])).
% 5.39/2.01  tff(c_24, plain, (![A_11, B_12]: (k1_setfam_1(k2_tarski(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.39/2.01  tff(c_108, plain, (![B_30, A_31]: (k3_xboole_0(B_30, A_31)=k3_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_102, c_24])).
% 5.39/2.01  tff(c_38, plain, (r2_hidden('#skF_3', k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.39/2.01  tff(c_125, plain, (r2_hidden('#skF_3', k3_xboole_0('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_38])).
% 5.39/2.01  tff(c_160, plain, (![D_34, A_35, B_36]: (r2_hidden(D_34, A_35) | ~r2_hidden(D_34, k3_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.39/2.01  tff(c_170, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_125, c_160])).
% 5.39/2.01  tff(c_32, plain, (![B_19, A_18]: (k1_funct_1(k6_relat_1(B_19), A_18)=A_18 | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.39/2.01  tff(c_42, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.39/2.01  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.39/2.01  tff(c_26, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.39/2.01  tff(c_28, plain, (![A_13]: (v1_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.39/2.01  tff(c_34, plain, (![A_20, B_21]: (k1_relat_1(k5_relat_1(k6_relat_1(A_20), B_21))=k3_xboole_0(k1_relat_1(B_21), A_20) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.39/2.01  tff(c_600, plain, (![C_90, B_91, A_92]: (k1_funct_1(k5_relat_1(C_90, B_91), A_92)=k1_funct_1(B_91, k1_funct_1(C_90, A_92)) | ~r2_hidden(A_92, k1_relat_1(k5_relat_1(C_90, B_91))) | ~v1_funct_1(C_90) | ~v1_relat_1(C_90) | ~v1_funct_1(B_91) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.39/2.01  tff(c_655, plain, (![A_20, B_21, A_92]: (k1_funct_1(k5_relat_1(k6_relat_1(A_20), B_21), A_92)=k1_funct_1(B_21, k1_funct_1(k6_relat_1(A_20), A_92)) | ~r2_hidden(A_92, k3_xboole_0(k1_relat_1(B_21), A_20)) | ~v1_funct_1(k6_relat_1(A_20)) | ~v1_relat_1(k6_relat_1(A_20)) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(superposition, [status(thm), theory('equality')], [c_34, c_600])).
% 5.39/2.01  tff(c_1215, plain, (![A_132, B_133, A_134]: (k1_funct_1(k5_relat_1(k6_relat_1(A_132), B_133), A_134)=k1_funct_1(B_133, k1_funct_1(k6_relat_1(A_132), A_134)) | ~r2_hidden(A_134, k3_xboole_0(k1_relat_1(B_133), A_132)) | ~v1_funct_1(B_133) | ~v1_relat_1(B_133))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_655])).
% 5.39/2.01  tff(c_2622, plain, (![B_215, B_216, A_217]: (k1_funct_1(k5_relat_1(k6_relat_1(B_215), B_216), A_217)=k1_funct_1(B_216, k1_funct_1(k6_relat_1(B_215), A_217)) | ~r2_hidden(A_217, k3_xboole_0(B_215, k1_relat_1(B_216))) | ~v1_funct_1(B_216) | ~v1_relat_1(B_216))), inference(superposition, [status(thm), theory('equality')], [c_108, c_1215])).
% 5.39/2.01  tff(c_2860, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'), '#skF_5'), '#skF_3')=k1_funct_1('#skF_5', k1_funct_1(k6_relat_1('#skF_4'), '#skF_3')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_125, c_2622])).
% 5.39/2.01  tff(c_2928, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'), '#skF_5'), '#skF_3')=k1_funct_1('#skF_5', k1_funct_1(k6_relat_1('#skF_4'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_2860])).
% 5.39/2.01  tff(c_36, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'), '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.39/2.01  tff(c_2929, plain, (k1_funct_1('#skF_5', k1_funct_1(k6_relat_1('#skF_4'), '#skF_3'))!=k1_funct_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2928, c_36])).
% 5.39/2.01  tff(c_2936, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_32, c_2929])).
% 5.39/2.01  tff(c_2940, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_170, c_2936])).
% 5.39/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.39/2.01  
% 5.39/2.01  Inference rules
% 5.39/2.01  ----------------------
% 5.39/2.01  #Ref     : 0
% 5.39/2.01  #Sup     : 657
% 5.39/2.01  #Fact    : 0
% 5.39/2.01  #Define  : 0
% 5.39/2.01  #Split   : 0
% 5.39/2.01  #Chain   : 0
% 5.39/2.01  #Close   : 0
% 5.39/2.01  
% 5.39/2.01  Ordering : KBO
% 5.39/2.01  
% 5.39/2.01  Simplification rules
% 5.39/2.01  ----------------------
% 5.39/2.01  #Subsume      : 186
% 5.39/2.01  #Demod        : 231
% 5.39/2.01  #Tautology    : 46
% 5.39/2.01  #SimpNegUnit  : 0
% 5.39/2.01  #BackRed      : 2
% 5.39/2.01  
% 5.39/2.01  #Partial instantiations: 0
% 5.39/2.01  #Strategies tried      : 1
% 5.39/2.01  
% 5.39/2.01  Timing (in seconds)
% 5.39/2.01  ----------------------
% 5.39/2.02  Preprocessing        : 0.30
% 5.39/2.02  Parsing              : 0.15
% 5.39/2.02  CNF conversion       : 0.02
% 5.39/2.02  Main loop            : 0.96
% 5.39/2.02  Inferencing          : 0.30
% 5.39/2.02  Reduction            : 0.32
% 5.39/2.02  Demodulation         : 0.26
% 5.39/2.02  BG Simplification    : 0.05
% 5.39/2.02  Subsumption          : 0.22
% 5.39/2.02  Abstraction          : 0.08
% 5.39/2.02  MUC search           : 0.00
% 5.39/2.02  Cooper               : 0.00
% 5.39/2.02  Total                : 1.29
% 5.39/2.02  Index Insertion      : 0.00
% 5.39/2.02  Index Deletion       : 0.00
% 5.39/2.02  Index Matching       : 0.00
% 5.39/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
