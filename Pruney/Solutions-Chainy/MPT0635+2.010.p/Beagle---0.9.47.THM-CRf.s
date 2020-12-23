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

% Result     : Theorem 6.55s
% Output     : CNFRefutation 6.55s
% Verified   : 
% Statistics : Number of formulae       :   48 (  59 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   67 (  91 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k1_relat_1(k5_relat_1(k6_relat_1(A),B)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    r2_hidden('#skF_3',k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_45,plain,(
    r2_hidden('#skF_3',k3_xboole_0('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_99,plain,(
    ! [D_33,A_34,B_35] :
      ( r2_hidden(D_33,A_34)
      | ~ r2_hidden(D_33,k3_xboole_0(A_34,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_109,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_45,c_99])).

tff(c_34,plain,(
    ! [B_22,A_21] :
      ( k1_funct_1(k6_relat_1(B_22),A_21) = A_21
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_44,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,(
    ! [A_16] : v1_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_36,plain,(
    ! [A_23,B_24] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(A_23),B_24)) = k3_xboole_0(k1_relat_1(B_24),A_23)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_515,plain,(
    ! [C_89,B_90,A_91] :
      ( k1_funct_1(k5_relat_1(C_89,B_90),A_91) = k1_funct_1(B_90,k1_funct_1(C_89,A_91))
      | ~ r2_hidden(A_91,k1_relat_1(k5_relat_1(C_89,B_90)))
      | ~ v1_funct_1(C_89)
      | ~ v1_relat_1(C_89)
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_566,plain,(
    ! [A_23,B_24,A_91] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_23),B_24),A_91) = k1_funct_1(B_24,k1_funct_1(k6_relat_1(A_23),A_91))
      | ~ r2_hidden(A_91,k3_xboole_0(k1_relat_1(B_24),A_23))
      | ~ v1_funct_1(k6_relat_1(A_23))
      | ~ v1_relat_1(k6_relat_1(A_23))
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_515])).

tff(c_1713,plain,(
    ! [A_174,B_175,A_176] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_174),B_175),A_176) = k1_funct_1(B_175,k1_funct_1(k6_relat_1(A_174),A_176))
      | ~ r2_hidden(A_176,k3_xboole_0(k1_relat_1(B_175),A_174))
      | ~ v1_funct_1(B_175)
      | ~ v1_relat_1(B_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_566])).

tff(c_3704,plain,(
    ! [A_264,B_265,A_266] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_264),B_265),A_266) = k1_funct_1(B_265,k1_funct_1(k6_relat_1(A_264),A_266))
      | ~ r2_hidden(A_266,k3_xboole_0(A_264,k1_relat_1(B_265)))
      | ~ v1_funct_1(B_265)
      | ~ v1_relat_1(B_265) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1713])).

tff(c_4038,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'),'#skF_5'),'#skF_3') = k1_funct_1('#skF_5',k1_funct_1(k6_relat_1('#skF_4'),'#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_45,c_3704])).

tff(c_4130,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'),'#skF_5'),'#skF_3') = k1_funct_1('#skF_5',k1_funct_1(k6_relat_1('#skF_4'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_4038])).

tff(c_38,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'),'#skF_5'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4291,plain,(
    k1_funct_1('#skF_5',k1_funct_1(k6_relat_1('#skF_4'),'#skF_3')) != k1_funct_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4130,c_38])).

tff(c_4298,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4291])).

tff(c_4302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_4298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.55/2.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.55/2.32  
% 6.55/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.55/2.32  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 6.55/2.32  
% 6.55/2.32  %Foreground sorts:
% 6.55/2.32  
% 6.55/2.32  
% 6.55/2.32  %Background operators:
% 6.55/2.32  
% 6.55/2.32  
% 6.55/2.32  %Foreground operators:
% 6.55/2.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.55/2.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.55/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.55/2.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.55/2.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.55/2.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.55/2.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.55/2.32  tff('#skF_5', type, '#skF_5': $i).
% 6.55/2.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.55/2.32  tff('#skF_3', type, '#skF_3': $i).
% 6.55/2.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.55/2.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.55/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.55/2.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.55/2.32  tff('#skF_4', type, '#skF_4': $i).
% 6.55/2.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.55/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.55/2.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.55/2.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.55/2.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.55/2.32  
% 6.55/2.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.55/2.33  tff(f_78, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_1)).
% 6.55/2.33  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 6.55/2.33  tff(f_63, axiom, (![A, B]: (r2_hidden(A, B) => (k1_funct_1(k6_relat_1(B), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_1)).
% 6.55/2.33  tff(f_46, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 6.55/2.33  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k1_relat_1(k5_relat_1(k6_relat_1(A), B)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_funct_1)).
% 6.55/2.33  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 6.55/2.33  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.55/2.33  tff(c_40, plain, (r2_hidden('#skF_3', k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.55/2.33  tff(c_45, plain, (r2_hidden('#skF_3', k3_xboole_0('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40])).
% 6.55/2.33  tff(c_99, plain, (![D_33, A_34, B_35]: (r2_hidden(D_33, A_34) | ~r2_hidden(D_33, k3_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.55/2.33  tff(c_109, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_45, c_99])).
% 6.55/2.33  tff(c_34, plain, (![B_22, A_21]: (k1_funct_1(k6_relat_1(B_22), A_21)=A_21 | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.55/2.33  tff(c_44, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.55/2.33  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.55/2.33  tff(c_28, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.55/2.33  tff(c_30, plain, (![A_16]: (v1_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.55/2.33  tff(c_36, plain, (![A_23, B_24]: (k1_relat_1(k5_relat_1(k6_relat_1(A_23), B_24))=k3_xboole_0(k1_relat_1(B_24), A_23) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.55/2.33  tff(c_515, plain, (![C_89, B_90, A_91]: (k1_funct_1(k5_relat_1(C_89, B_90), A_91)=k1_funct_1(B_90, k1_funct_1(C_89, A_91)) | ~r2_hidden(A_91, k1_relat_1(k5_relat_1(C_89, B_90))) | ~v1_funct_1(C_89) | ~v1_relat_1(C_89) | ~v1_funct_1(B_90) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.55/2.33  tff(c_566, plain, (![A_23, B_24, A_91]: (k1_funct_1(k5_relat_1(k6_relat_1(A_23), B_24), A_91)=k1_funct_1(B_24, k1_funct_1(k6_relat_1(A_23), A_91)) | ~r2_hidden(A_91, k3_xboole_0(k1_relat_1(B_24), A_23)) | ~v1_funct_1(k6_relat_1(A_23)) | ~v1_relat_1(k6_relat_1(A_23)) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(superposition, [status(thm), theory('equality')], [c_36, c_515])).
% 6.55/2.33  tff(c_1713, plain, (![A_174, B_175, A_176]: (k1_funct_1(k5_relat_1(k6_relat_1(A_174), B_175), A_176)=k1_funct_1(B_175, k1_funct_1(k6_relat_1(A_174), A_176)) | ~r2_hidden(A_176, k3_xboole_0(k1_relat_1(B_175), A_174)) | ~v1_funct_1(B_175) | ~v1_relat_1(B_175))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_566])).
% 6.55/2.33  tff(c_3704, plain, (![A_264, B_265, A_266]: (k1_funct_1(k5_relat_1(k6_relat_1(A_264), B_265), A_266)=k1_funct_1(B_265, k1_funct_1(k6_relat_1(A_264), A_266)) | ~r2_hidden(A_266, k3_xboole_0(A_264, k1_relat_1(B_265))) | ~v1_funct_1(B_265) | ~v1_relat_1(B_265))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1713])).
% 6.55/2.33  tff(c_4038, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'), '#skF_5'), '#skF_3')=k1_funct_1('#skF_5', k1_funct_1(k6_relat_1('#skF_4'), '#skF_3')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_45, c_3704])).
% 6.55/2.33  tff(c_4130, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'), '#skF_5'), '#skF_3')=k1_funct_1('#skF_5', k1_funct_1(k6_relat_1('#skF_4'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_4038])).
% 6.55/2.33  tff(c_38, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'), '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.55/2.33  tff(c_4291, plain, (k1_funct_1('#skF_5', k1_funct_1(k6_relat_1('#skF_4'), '#skF_3'))!=k1_funct_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4130, c_38])).
% 6.55/2.33  tff(c_4298, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_34, c_4291])).
% 6.55/2.33  tff(c_4302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109, c_4298])).
% 6.55/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.55/2.33  
% 6.55/2.33  Inference rules
% 6.55/2.33  ----------------------
% 6.55/2.33  #Ref     : 0
% 6.55/2.33  #Sup     : 968
% 6.55/2.33  #Fact    : 0
% 6.55/2.33  #Define  : 0
% 6.55/2.33  #Split   : 0
% 6.55/2.33  #Chain   : 0
% 6.55/2.33  #Close   : 0
% 6.55/2.33  
% 6.55/2.33  Ordering : KBO
% 6.55/2.33  
% 6.55/2.33  Simplification rules
% 6.55/2.33  ----------------------
% 6.55/2.33  #Subsume      : 297
% 6.55/2.33  #Demod        : 354
% 6.55/2.33  #Tautology    : 36
% 6.55/2.33  #SimpNegUnit  : 0
% 6.55/2.33  #BackRed      : 1
% 6.55/2.33  
% 6.55/2.33  #Partial instantiations: 0
% 6.55/2.33  #Strategies tried      : 1
% 6.55/2.33  
% 6.55/2.33  Timing (in seconds)
% 6.55/2.33  ----------------------
% 6.55/2.34  Preprocessing        : 0.32
% 6.55/2.34  Parsing              : 0.17
% 6.55/2.34  CNF conversion       : 0.02
% 6.55/2.34  Main loop            : 1.24
% 6.55/2.34  Inferencing          : 0.38
% 6.55/2.34  Reduction            : 0.39
% 6.55/2.34  Demodulation         : 0.33
% 6.55/2.34  BG Simplification    : 0.06
% 6.55/2.34  Subsumption          : 0.33
% 6.55/2.34  Abstraction          : 0.09
% 6.55/2.34  MUC search           : 0.00
% 6.55/2.34  Cooper               : 0.00
% 6.55/2.34  Total                : 1.59
% 6.55/2.34  Index Insertion      : 0.00
% 6.55/2.34  Index Deletion       : 0.00
% 6.55/2.34  Index Matching       : 0.00
% 6.55/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
