%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:53 EST 2020

% Result     : Theorem 24.92s
% Output     : CNFRefutation 24.92s
% Verified   : 
% Statistics : Number of formulae       :   57 (  99 expanded)
%              Number of leaves         :   24 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 ( 145 expanded)
%              Number of equality atoms :   15 (  40 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [C_19,A_17,B_18] :
      ( r1_tarski(k9_relat_1(C_19,A_17),k9_relat_1(C_19,B_18))
      | ~ r1_tarski(A_17,B_18)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_65,plain,(
    ! [A_27,B_28] : k1_setfam_1(k2_tarski(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_89,plain,(
    ! [B_31,A_32] : k1_setfam_1(k2_tarski(B_31,A_32)) = k3_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_65])).

tff(c_18,plain,(
    ! [A_15,B_16] : k1_setfam_1(k2_tarski(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_112,plain,(
    ! [B_33,A_34] : k3_xboole_0(B_33,A_34) = k3_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_18])).

tff(c_127,plain,(
    ! [B_33,A_34] : r1_tarski(k3_xboole_0(B_33,A_34),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_8])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_95,plain,(
    ! [B_31,A_32] : k3_xboole_0(B_31,A_32) = k3_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_18])).

tff(c_22,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k9_relat_1(B_21,k10_relat_1(B_21,A_20)),A_20)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_tarski(A_8,k3_xboole_0(B_9,C_10))
      | ~ r1_tarski(A_8,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_163,plain,(
    ! [B_37,A_38] :
      ( B_37 = A_38
      | ~ r1_tarski(B_37,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_387,plain,(
    ! [A_62,B_63] :
      ( k3_xboole_0(A_62,B_63) = A_62
      | ~ r1_tarski(A_62,k3_xboole_0(A_62,B_63)) ) ),
    inference(resolution,[status(thm)],[c_8,c_163])).

tff(c_391,plain,(
    ! [B_9,C_10] :
      ( k3_xboole_0(B_9,C_10) = B_9
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(B_9,B_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_387])).

tff(c_401,plain,(
    ! [B_64,C_65] :
      ( k3_xboole_0(B_64,C_65) = B_64
      | ~ r1_tarski(B_64,C_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_391])).

tff(c_410,plain,(
    ! [B_21,A_20] :
      ( k3_xboole_0(k9_relat_1(B_21,k10_relat_1(B_21,A_20)),A_20) = k9_relat_1(B_21,k10_relat_1(B_21,A_20))
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_22,c_401])).

tff(c_30298,plain,(
    ! [A_433,B_434] :
      ( k3_xboole_0(A_433,k9_relat_1(B_434,k10_relat_1(B_434,A_433))) = k9_relat_1(B_434,k10_relat_1(B_434,A_433))
      | ~ v1_funct_1(B_434)
      | ~ v1_relat_1(B_434) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_410])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(A_5,B_6)
      | ~ r1_tarski(A_5,k3_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66419,plain,(
    ! [A_679,A_680,B_681] :
      ( r1_tarski(A_679,A_680)
      | ~ r1_tarski(A_679,k9_relat_1(B_681,k10_relat_1(B_681,A_680)))
      | ~ v1_funct_1(B_681)
      | ~ v1_relat_1(B_681) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30298,c_10])).

tff(c_71077,plain,(
    ! [C_711,A_712,A_713] :
      ( r1_tarski(k9_relat_1(C_711,A_712),A_713)
      | ~ v1_funct_1(C_711)
      | ~ r1_tarski(A_712,k10_relat_1(C_711,A_713))
      | ~ v1_relat_1(C_711) ) ),
    inference(resolution,[status(thm)],[c_20,c_66419])).

tff(c_312,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(A_56,k3_xboole_0(B_57,C_58))
      | ~ r1_tarski(A_56,C_58)
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_151,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_24])).

tff(c_329,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_312,c_151])).

tff(c_386,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_329])).

tff(c_71275,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),k10_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71077,c_386])).

tff(c_71360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_127,c_26,c_71275])).

tff(c_71361,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_329])).

tff(c_72063,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_71361])).

tff(c_72067,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_8,c_72063])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:52:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.92/15.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.92/15.14  
% 24.92/15.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.92/15.14  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 24.92/15.14  
% 24.92/15.14  %Foreground sorts:
% 24.92/15.14  
% 24.92/15.14  
% 24.92/15.14  %Background operators:
% 24.92/15.14  
% 24.92/15.14  
% 24.92/15.14  %Foreground operators:
% 24.92/15.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 24.92/15.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.92/15.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.92/15.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 24.92/15.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 24.92/15.14  tff('#skF_2', type, '#skF_2': $i).
% 24.92/15.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 24.92/15.14  tff('#skF_3', type, '#skF_3': $i).
% 24.92/15.14  tff('#skF_1', type, '#skF_1': $i).
% 24.92/15.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.92/15.14  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 24.92/15.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 24.92/15.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.92/15.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 24.92/15.14  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 24.92/15.14  
% 24.92/15.15  tff(f_68, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_funct_1)).
% 24.92/15.15  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 24.92/15.15  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 24.92/15.15  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 24.92/15.15  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 24.92/15.15  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 24.92/15.15  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 24.92/15.15  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 24.92/15.15  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 24.92/15.15  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 24.92/15.15  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 24.92/15.15  tff(c_20, plain, (![C_19, A_17, B_18]: (r1_tarski(k9_relat_1(C_19, A_17), k9_relat_1(C_19, B_18)) | ~r1_tarski(A_17, B_18) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 24.92/15.15  tff(c_14, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 24.92/15.15  tff(c_65, plain, (![A_27, B_28]: (k1_setfam_1(k2_tarski(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_49])).
% 24.92/15.15  tff(c_89, plain, (![B_31, A_32]: (k1_setfam_1(k2_tarski(B_31, A_32))=k3_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_14, c_65])).
% 24.92/15.15  tff(c_18, plain, (![A_15, B_16]: (k1_setfam_1(k2_tarski(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 24.92/15.15  tff(c_112, plain, (![B_33, A_34]: (k3_xboole_0(B_33, A_34)=k3_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_89, c_18])).
% 24.92/15.15  tff(c_127, plain, (![B_33, A_34]: (r1_tarski(k3_xboole_0(B_33, A_34), A_34))), inference(superposition, [status(thm), theory('equality')], [c_112, c_8])).
% 24.92/15.15  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 24.92/15.15  tff(c_95, plain, (![B_31, A_32]: (k3_xboole_0(B_31, A_32)=k3_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_89, c_18])).
% 24.92/15.15  tff(c_22, plain, (![B_21, A_20]: (r1_tarski(k9_relat_1(B_21, k10_relat_1(B_21, A_20)), A_20) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 24.92/15.15  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.92/15.15  tff(c_12, plain, (![A_8, B_9, C_10]: (r1_tarski(A_8, k3_xboole_0(B_9, C_10)) | ~r1_tarski(A_8, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 24.92/15.15  tff(c_163, plain, (![B_37, A_38]: (B_37=A_38 | ~r1_tarski(B_37, A_38) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.92/15.15  tff(c_387, plain, (![A_62, B_63]: (k3_xboole_0(A_62, B_63)=A_62 | ~r1_tarski(A_62, k3_xboole_0(A_62, B_63)))), inference(resolution, [status(thm)], [c_8, c_163])).
% 24.92/15.15  tff(c_391, plain, (![B_9, C_10]: (k3_xboole_0(B_9, C_10)=B_9 | ~r1_tarski(B_9, C_10) | ~r1_tarski(B_9, B_9))), inference(resolution, [status(thm)], [c_12, c_387])).
% 24.92/15.15  tff(c_401, plain, (![B_64, C_65]: (k3_xboole_0(B_64, C_65)=B_64 | ~r1_tarski(B_64, C_65))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_391])).
% 24.92/15.15  tff(c_410, plain, (![B_21, A_20]: (k3_xboole_0(k9_relat_1(B_21, k10_relat_1(B_21, A_20)), A_20)=k9_relat_1(B_21, k10_relat_1(B_21, A_20)) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_22, c_401])).
% 24.92/15.15  tff(c_30298, plain, (![A_433, B_434]: (k3_xboole_0(A_433, k9_relat_1(B_434, k10_relat_1(B_434, A_433)))=k9_relat_1(B_434, k10_relat_1(B_434, A_433)) | ~v1_funct_1(B_434) | ~v1_relat_1(B_434))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_410])).
% 24.92/15.15  tff(c_10, plain, (![A_5, B_6, C_7]: (r1_tarski(A_5, B_6) | ~r1_tarski(A_5, k3_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 24.92/15.15  tff(c_66419, plain, (![A_679, A_680, B_681]: (r1_tarski(A_679, A_680) | ~r1_tarski(A_679, k9_relat_1(B_681, k10_relat_1(B_681, A_680))) | ~v1_funct_1(B_681) | ~v1_relat_1(B_681))), inference(superposition, [status(thm), theory('equality')], [c_30298, c_10])).
% 24.92/15.15  tff(c_71077, plain, (![C_711, A_712, A_713]: (r1_tarski(k9_relat_1(C_711, A_712), A_713) | ~v1_funct_1(C_711) | ~r1_tarski(A_712, k10_relat_1(C_711, A_713)) | ~v1_relat_1(C_711))), inference(resolution, [status(thm)], [c_20, c_66419])).
% 24.92/15.15  tff(c_312, plain, (![A_56, B_57, C_58]: (r1_tarski(A_56, k3_xboole_0(B_57, C_58)) | ~r1_tarski(A_56, C_58) | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_43])).
% 24.92/15.15  tff(c_24, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 24.92/15.15  tff(c_151, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_24])).
% 24.92/15.15  tff(c_329, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_312, c_151])).
% 24.92/15.15  tff(c_386, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_329])).
% 24.92/15.15  tff(c_71275, plain, (~v1_funct_1('#skF_3') | ~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), k10_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_71077, c_386])).
% 24.92/15.15  tff(c_71360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_127, c_26, c_71275])).
% 24.92/15.15  tff(c_71361, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_329])).
% 24.92/15.15  tff(c_72063, plain, (~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_71361])).
% 24.92/15.15  tff(c_72067, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_8, c_72063])).
% 24.92/15.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.92/15.15  
% 24.92/15.15  Inference rules
% 24.92/15.15  ----------------------
% 24.92/15.15  #Ref     : 0
% 24.92/15.15  #Sup     : 18493
% 24.92/15.15  #Fact    : 0
% 24.92/15.15  #Define  : 0
% 24.92/15.15  #Split   : 2
% 24.92/15.15  #Chain   : 0
% 24.92/15.15  #Close   : 0
% 24.92/15.15  
% 24.92/15.15  Ordering : KBO
% 24.92/15.15  
% 24.92/15.15  Simplification rules
% 24.92/15.15  ----------------------
% 24.92/15.15  #Subsume      : 2492
% 24.92/15.15  #Demod        : 9630
% 24.92/15.15  #Tautology    : 6320
% 24.92/15.15  #SimpNegUnit  : 0
% 24.92/15.15  #BackRed      : 0
% 24.92/15.15  
% 24.92/15.15  #Partial instantiations: 0
% 24.92/15.15  #Strategies tried      : 1
% 24.92/15.15  
% 24.92/15.15  Timing (in seconds)
% 24.92/15.15  ----------------------
% 24.92/15.16  Preprocessing        : 0.30
% 24.92/15.16  Parsing              : 0.16
% 24.92/15.16  CNF conversion       : 0.02
% 24.92/15.16  Main loop            : 14.10
% 24.92/15.16  Inferencing          : 1.56
% 24.92/15.16  Reduction            : 8.14
% 24.92/15.16  Demodulation         : 7.67
% 24.92/15.16  BG Simplification    : 0.25
% 24.92/15.16  Subsumption          : 3.61
% 24.92/15.16  Abstraction          : 0.37
% 24.92/15.16  MUC search           : 0.00
% 24.92/15.16  Cooper               : 0.00
% 24.92/15.16  Total                : 14.43
% 24.92/15.16  Index Insertion      : 0.00
% 24.92/15.16  Index Deletion       : 0.00
% 24.92/15.16  Index Matching       : 0.00
% 24.92/15.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
