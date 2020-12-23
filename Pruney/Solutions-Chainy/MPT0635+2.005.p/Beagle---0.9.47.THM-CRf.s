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
% DateTime   : Thu Dec  3 10:03:21 EST 2020

% Result     : Theorem 7.12s
% Output     : CNFRefutation 7.12s
% Verified   : 
% Statistics : Number of formulae       :   58 (  78 expanded)
%              Number of leaves         :   29 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :  107 ( 148 expanded)
%              Number of equality atoms :   18 (  33 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_40,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( v1_relat_1(D)
     => ( r2_hidden(k4_tarski(A,B),k5_relat_1(k6_relat_1(C),D))
      <=> ( r2_hidden(A,C)
          & r2_hidden(k4_tarski(A,B),D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_20,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_90,plain,(
    ! [A_29,B_30] : k1_setfam_1(k2_tarski(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_114,plain,(
    ! [B_33,A_34] : k1_setfam_1(k2_tarski(B_33,A_34)) = k3_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_90])).

tff(c_24,plain,(
    ! [A_11,B_12] : k1_setfam_1(k2_tarski(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_120,plain,(
    ! [B_33,A_34] : k3_xboole_0(B_33,A_34) = k3_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_24])).

tff(c_50,plain,(
    r2_hidden('#skF_3',k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_137,plain,(
    r2_hidden('#skF_3',k3_xboole_0('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_50])).

tff(c_173,plain,(
    ! [D_39,B_40,A_41] :
      ( r2_hidden(D_39,B_40)
      | ~ r2_hidden(D_39,k3_xboole_0(A_41,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_183,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_137,c_173])).

tff(c_184,plain,(
    ! [D_42,A_43,B_44] :
      ( r2_hidden(D_42,A_43)
      | ~ r2_hidden(D_42,k3_xboole_0(A_43,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_194,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_137,c_184])).

tff(c_42,plain,(
    ! [A_22,C_24] :
      ( r2_hidden(k4_tarski(A_22,k1_funct_1(C_24,A_22)),C_24)
      | ~ r2_hidden(A_22,k1_relat_1(C_24))
      | ~ v1_funct_1(C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    ! [A_21] : v1_funct_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( v1_funct_1(k5_relat_1(A_19,B_20))
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k5_relat_1(A_13,B_14))
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_335,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( r2_hidden(k4_tarski(A_79,B_80),k5_relat_1(k6_relat_1(C_81),D_82))
      | ~ r2_hidden(k4_tarski(A_79,B_80),D_82)
      | ~ r2_hidden(A_79,C_81)
      | ~ v1_relat_1(D_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_44,plain,(
    ! [C_24,A_22,B_23] :
      ( k1_funct_1(C_24,A_22) = B_23
      | ~ r2_hidden(k4_tarski(A_22,B_23),C_24)
      | ~ v1_funct_1(C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4713,plain,(
    ! [C_340,D_341,A_342,B_343] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(C_340),D_341),A_342) = B_343
      | ~ v1_funct_1(k5_relat_1(k6_relat_1(C_340),D_341))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_340),D_341))
      | ~ r2_hidden(k4_tarski(A_342,B_343),D_341)
      | ~ r2_hidden(A_342,C_340)
      | ~ v1_relat_1(D_341) ) ),
    inference(resolution,[status(thm)],[c_335,c_44])).

tff(c_4716,plain,(
    ! [C_340,B_14,A_342,B_343] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(C_340),B_14),A_342) = B_343
      | ~ v1_funct_1(k5_relat_1(k6_relat_1(C_340),B_14))
      | ~ r2_hidden(k4_tarski(A_342,B_343),B_14)
      | ~ r2_hidden(A_342,C_340)
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(k6_relat_1(C_340)) ) ),
    inference(resolution,[status(thm)],[c_26,c_4713])).

tff(c_4720,plain,(
    ! [C_344,B_345,A_346,B_347] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(C_344),B_345),A_346) = B_347
      | ~ v1_funct_1(k5_relat_1(k6_relat_1(C_344),B_345))
      | ~ r2_hidden(k4_tarski(A_346,B_347),B_345)
      | ~ r2_hidden(A_346,C_344)
      | ~ v1_relat_1(B_345) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4716])).

tff(c_4723,plain,(
    ! [C_344,B_20,A_346,B_347] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(C_344),B_20),A_346) = B_347
      | ~ r2_hidden(k4_tarski(A_346,B_347),B_20)
      | ~ r2_hidden(A_346,C_344)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(k6_relat_1(C_344))
      | ~ v1_relat_1(k6_relat_1(C_344)) ) ),
    inference(resolution,[status(thm)],[c_34,c_4720])).

tff(c_4727,plain,(
    ! [C_348,B_349,A_350,B_351] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(C_348),B_349),A_350) = B_351
      | ~ r2_hidden(k4_tarski(A_350,B_351),B_349)
      | ~ r2_hidden(A_350,C_348)
      | ~ v1_funct_1(B_349)
      | ~ v1_relat_1(B_349) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_4723])).

tff(c_4744,plain,(
    ! [C_352,C_353,A_354] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(C_352),C_353),A_354) = k1_funct_1(C_353,A_354)
      | ~ r2_hidden(A_354,C_352)
      | ~ r2_hidden(A_354,k1_relat_1(C_353))
      | ~ v1_funct_1(C_353)
      | ~ v1_relat_1(C_353) ) ),
    inference(resolution,[status(thm)],[c_42,c_4727])).

tff(c_48,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'),'#skF_5'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4753,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4744,c_48])).

tff(c_4761,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_183,c_194,c_4753])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:53:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.12/2.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/2.46  
% 7.12/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/2.46  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 7.12/2.46  
% 7.12/2.46  %Foreground sorts:
% 7.12/2.46  
% 7.12/2.46  
% 7.12/2.46  %Background operators:
% 7.12/2.46  
% 7.12/2.46  
% 7.12/2.46  %Foreground operators:
% 7.12/2.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.12/2.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.12/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.12/2.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.12/2.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.12/2.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.12/2.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.12/2.46  tff('#skF_5', type, '#skF_5': $i).
% 7.12/2.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.12/2.46  tff('#skF_3', type, '#skF_3': $i).
% 7.12/2.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.12/2.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.12/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.12/2.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.12/2.46  tff('#skF_4', type, '#skF_4': $i).
% 7.12/2.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.12/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.12/2.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.12/2.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.12/2.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.12/2.46  
% 7.12/2.47  tff(f_89, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_1)).
% 7.12/2.47  tff(f_36, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.12/2.47  tff(f_40, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 7.12/2.47  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.12/2.47  tff(f_80, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 7.12/2.47  tff(f_70, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 7.12/2.47  tff(f_66, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 7.12/2.47  tff(f_46, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 7.12/2.47  tff(f_54, axiom, (![A, B, C, D]: (v1_relat_1(D) => (r2_hidden(k4_tarski(A, B), k5_relat_1(k6_relat_1(C), D)) <=> (r2_hidden(A, C) & r2_hidden(k4_tarski(A, B), D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_relat_1)).
% 7.12/2.47  tff(c_54, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.12/2.47  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.12/2.47  tff(c_20, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.12/2.47  tff(c_90, plain, (![A_29, B_30]: (k1_setfam_1(k2_tarski(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.12/2.47  tff(c_114, plain, (![B_33, A_34]: (k1_setfam_1(k2_tarski(B_33, A_34))=k3_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_20, c_90])).
% 7.12/2.47  tff(c_24, plain, (![A_11, B_12]: (k1_setfam_1(k2_tarski(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.12/2.47  tff(c_120, plain, (![B_33, A_34]: (k3_xboole_0(B_33, A_34)=k3_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_114, c_24])).
% 7.12/2.47  tff(c_50, plain, (r2_hidden('#skF_3', k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.12/2.47  tff(c_137, plain, (r2_hidden('#skF_3', k3_xboole_0('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_50])).
% 7.12/2.47  tff(c_173, plain, (![D_39, B_40, A_41]: (r2_hidden(D_39, B_40) | ~r2_hidden(D_39, k3_xboole_0(A_41, B_40)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.12/2.47  tff(c_183, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_137, c_173])).
% 7.12/2.47  tff(c_184, plain, (![D_42, A_43, B_44]: (r2_hidden(D_42, A_43) | ~r2_hidden(D_42, k3_xboole_0(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.12/2.47  tff(c_194, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_137, c_184])).
% 7.12/2.47  tff(c_42, plain, (![A_22, C_24]: (r2_hidden(k4_tarski(A_22, k1_funct_1(C_24, A_22)), C_24) | ~r2_hidden(A_22, k1_relat_1(C_24)) | ~v1_funct_1(C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.12/2.47  tff(c_38, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.12/2.47  tff(c_40, plain, (![A_21]: (v1_funct_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.12/2.47  tff(c_34, plain, (![A_19, B_20]: (v1_funct_1(k5_relat_1(A_19, B_20)) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.12/2.47  tff(c_26, plain, (![A_13, B_14]: (v1_relat_1(k5_relat_1(A_13, B_14)) | ~v1_relat_1(B_14) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.12/2.47  tff(c_335, plain, (![A_79, B_80, C_81, D_82]: (r2_hidden(k4_tarski(A_79, B_80), k5_relat_1(k6_relat_1(C_81), D_82)) | ~r2_hidden(k4_tarski(A_79, B_80), D_82) | ~r2_hidden(A_79, C_81) | ~v1_relat_1(D_82))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.12/2.47  tff(c_44, plain, (![C_24, A_22, B_23]: (k1_funct_1(C_24, A_22)=B_23 | ~r2_hidden(k4_tarski(A_22, B_23), C_24) | ~v1_funct_1(C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.12/2.47  tff(c_4713, plain, (![C_340, D_341, A_342, B_343]: (k1_funct_1(k5_relat_1(k6_relat_1(C_340), D_341), A_342)=B_343 | ~v1_funct_1(k5_relat_1(k6_relat_1(C_340), D_341)) | ~v1_relat_1(k5_relat_1(k6_relat_1(C_340), D_341)) | ~r2_hidden(k4_tarski(A_342, B_343), D_341) | ~r2_hidden(A_342, C_340) | ~v1_relat_1(D_341))), inference(resolution, [status(thm)], [c_335, c_44])).
% 7.12/2.47  tff(c_4716, plain, (![C_340, B_14, A_342, B_343]: (k1_funct_1(k5_relat_1(k6_relat_1(C_340), B_14), A_342)=B_343 | ~v1_funct_1(k5_relat_1(k6_relat_1(C_340), B_14)) | ~r2_hidden(k4_tarski(A_342, B_343), B_14) | ~r2_hidden(A_342, C_340) | ~v1_relat_1(B_14) | ~v1_relat_1(k6_relat_1(C_340)))), inference(resolution, [status(thm)], [c_26, c_4713])).
% 7.12/2.47  tff(c_4720, plain, (![C_344, B_345, A_346, B_347]: (k1_funct_1(k5_relat_1(k6_relat_1(C_344), B_345), A_346)=B_347 | ~v1_funct_1(k5_relat_1(k6_relat_1(C_344), B_345)) | ~r2_hidden(k4_tarski(A_346, B_347), B_345) | ~r2_hidden(A_346, C_344) | ~v1_relat_1(B_345))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4716])).
% 7.12/2.47  tff(c_4723, plain, (![C_344, B_20, A_346, B_347]: (k1_funct_1(k5_relat_1(k6_relat_1(C_344), B_20), A_346)=B_347 | ~r2_hidden(k4_tarski(A_346, B_347), B_20) | ~r2_hidden(A_346, C_344) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(k6_relat_1(C_344)) | ~v1_relat_1(k6_relat_1(C_344)))), inference(resolution, [status(thm)], [c_34, c_4720])).
% 7.12/2.47  tff(c_4727, plain, (![C_348, B_349, A_350, B_351]: (k1_funct_1(k5_relat_1(k6_relat_1(C_348), B_349), A_350)=B_351 | ~r2_hidden(k4_tarski(A_350, B_351), B_349) | ~r2_hidden(A_350, C_348) | ~v1_funct_1(B_349) | ~v1_relat_1(B_349))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_4723])).
% 7.12/2.47  tff(c_4744, plain, (![C_352, C_353, A_354]: (k1_funct_1(k5_relat_1(k6_relat_1(C_352), C_353), A_354)=k1_funct_1(C_353, A_354) | ~r2_hidden(A_354, C_352) | ~r2_hidden(A_354, k1_relat_1(C_353)) | ~v1_funct_1(C_353) | ~v1_relat_1(C_353))), inference(resolution, [status(thm)], [c_42, c_4727])).
% 7.12/2.47  tff(c_48, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'), '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.12/2.47  tff(c_4753, plain, (~r2_hidden('#skF_3', '#skF_4') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4744, c_48])).
% 7.12/2.47  tff(c_4761, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_183, c_194, c_4753])).
% 7.12/2.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/2.47  
% 7.12/2.47  Inference rules
% 7.12/2.47  ----------------------
% 7.12/2.47  #Ref     : 0
% 7.12/2.47  #Sup     : 1071
% 7.12/2.47  #Fact    : 0
% 7.12/2.47  #Define  : 0
% 7.12/2.47  #Split   : 0
% 7.12/2.47  #Chain   : 0
% 7.12/2.47  #Close   : 0
% 7.12/2.47  
% 7.12/2.47  Ordering : KBO
% 7.12/2.47  
% 7.12/2.47  Simplification rules
% 7.12/2.47  ----------------------
% 7.12/2.47  #Subsume      : 326
% 7.12/2.47  #Demod        : 325
% 7.12/2.47  #Tautology    : 46
% 7.12/2.47  #SimpNegUnit  : 0
% 7.12/2.47  #BackRed      : 1
% 7.12/2.47  
% 7.12/2.47  #Partial instantiations: 0
% 7.12/2.47  #Strategies tried      : 1
% 7.12/2.47  
% 7.12/2.47  Timing (in seconds)
% 7.12/2.47  ----------------------
% 7.12/2.48  Preprocessing        : 0.32
% 7.12/2.48  Parsing              : 0.17
% 7.12/2.48  CNF conversion       : 0.02
% 7.12/2.48  Main loop            : 1.38
% 7.12/2.48  Inferencing          : 0.43
% 7.12/2.48  Reduction            : 0.42
% 7.12/2.48  Demodulation         : 0.34
% 7.12/2.48  BG Simplification    : 0.05
% 7.12/2.48  Subsumption          : 0.39
% 7.12/2.48  Abstraction          : 0.09
% 7.12/2.48  MUC search           : 0.00
% 7.12/2.48  Cooper               : 0.00
% 7.12/2.48  Total                : 1.73
% 7.12/2.48  Index Insertion      : 0.00
% 7.12/2.48  Index Deletion       : 0.00
% 7.12/2.48  Index Matching       : 0.00
% 7.12/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
