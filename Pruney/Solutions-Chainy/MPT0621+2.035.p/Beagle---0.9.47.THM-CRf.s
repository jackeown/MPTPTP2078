%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:03 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 395 expanded)
%              Number of leaves         :   25 ( 144 expanded)
%              Depth                    :   18
%              Number of atoms          :  130 (1375 expanded)
%              Number of equality atoms :   96 ( 867 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_47,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_16,plain,(
    ! [A_11] : v1_funct_1('#skF_1'(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_11] : k1_relat_1('#skF_1'(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_11] : v1_relat_1('#skF_1'(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_17,B_21] :
      ( k1_relat_1('#skF_2'(A_17,B_21)) = A_17
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24,plain,(
    ! [A_17,B_21] :
      ( v1_funct_1('#skF_2'(A_17,B_21))
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26,plain,(
    ! [A_17,B_21] :
      ( v1_relat_1('#skF_2'(A_17,B_21))
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_71,plain,(
    ! [C_40,B_41] :
      ( C_40 = B_41
      | k1_relat_1(C_40) != '#skF_3'
      | k1_relat_1(B_41) != '#skF_3'
      | ~ v1_funct_1(C_40)
      | ~ v1_relat_1(C_40)
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_75,plain,(
    ! [B_41,A_11] :
      ( B_41 = '#skF_1'(A_11)
      | k1_relat_1('#skF_1'(A_11)) != '#skF_3'
      | k1_relat_1(B_41) != '#skF_3'
      | ~ v1_funct_1('#skF_1'(A_11))
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(resolution,[status(thm)],[c_18,c_71])).

tff(c_141,plain,(
    ! [B_54,A_55] :
      ( B_54 = '#skF_1'(A_55)
      | A_55 != '#skF_3'
      | k1_relat_1(B_54) != '#skF_3'
      | ~ v1_funct_1(B_54)
      | ~ v1_relat_1(B_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_75])).

tff(c_214,plain,(
    ! [A_66,B_67,A_68] :
      ( '#skF_2'(A_66,B_67) = '#skF_1'(A_68)
      | A_68 != '#skF_3'
      | k1_relat_1('#skF_2'(A_66,B_67)) != '#skF_3'
      | ~ v1_funct_1('#skF_2'(A_66,B_67))
      | k1_xboole_0 = A_66 ) ),
    inference(resolution,[status(thm)],[c_26,c_141])).

tff(c_219,plain,(
    ! [A_69,B_70,A_71] :
      ( '#skF_2'(A_69,B_70) = '#skF_1'(A_71)
      | A_71 != '#skF_3'
      | k1_relat_1('#skF_2'(A_69,B_70)) != '#skF_3'
      | k1_xboole_0 = A_69 ) ),
    inference(resolution,[status(thm)],[c_24,c_214])).

tff(c_228,plain,(
    ! [A_75,B_76,A_77] :
      ( '#skF_2'(A_75,B_76) = '#skF_1'(A_77)
      | A_77 != '#skF_3'
      | A_75 != '#skF_3'
      | k1_xboole_0 = A_75
      | k1_xboole_0 = A_75 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_219])).

tff(c_262,plain,(
    ! [A_75,B_76,A_77] :
      ( k1_relat_1('#skF_2'(A_75,B_76)) = A_77
      | A_77 != '#skF_3'
      | A_75 != '#skF_3'
      | k1_xboole_0 = A_75
      | k1_xboole_0 = A_75 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_14])).

tff(c_292,plain,(
    ! [A_81,B_82] :
      ( k1_relat_1('#skF_2'(A_81,B_82)) = '#skF_3'
      | A_81 != '#skF_3'
      | k1_xboole_0 = A_81
      | k1_xboole_0 = A_81 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_262])).

tff(c_207,plain,(
    ! [B_60,A_61,B_62] :
      ( B_60 = '#skF_2'(A_61,B_62)
      | k1_relat_1('#skF_2'(A_61,B_62)) != '#skF_3'
      | k1_relat_1(B_60) != '#skF_3'
      | ~ v1_funct_1('#skF_2'(A_61,B_62))
      | ~ v1_funct_1(B_60)
      | ~ v1_relat_1(B_60)
      | k1_xboole_0 = A_61 ) ),
    inference(resolution,[status(thm)],[c_26,c_71])).

tff(c_210,plain,(
    ! [B_60,A_17,B_21] :
      ( B_60 = '#skF_2'(A_17,B_21)
      | k1_relat_1('#skF_2'(A_17,B_21)) != '#skF_3'
      | k1_relat_1(B_60) != '#skF_3'
      | ~ v1_funct_1(B_60)
      | ~ v1_relat_1(B_60)
      | k1_xboole_0 = A_17 ) ),
    inference(resolution,[status(thm)],[c_24,c_207])).

tff(c_318,plain,(
    ! [B_83,A_84,B_85] :
      ( B_83 = '#skF_2'(A_84,B_85)
      | k1_relat_1(B_83) != '#skF_3'
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83)
      | A_84 != '#skF_3'
      | k1_xboole_0 = A_84 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_210])).

tff(c_322,plain,(
    ! [A_84,B_85,A_11] :
      ( '#skF_2'(A_84,B_85) = '#skF_1'(A_11)
      | k1_relat_1('#skF_1'(A_11)) != '#skF_3'
      | ~ v1_funct_1('#skF_1'(A_11))
      | A_84 != '#skF_3'
      | k1_xboole_0 = A_84 ) ),
    inference(resolution,[status(thm)],[c_18,c_318])).

tff(c_329,plain,(
    ! [A_86,B_87,A_88] :
      ( '#skF_2'(A_86,B_87) = '#skF_1'(A_88)
      | A_88 != '#skF_3'
      | A_86 != '#skF_3'
      | k1_xboole_0 = A_86 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_322])).

tff(c_20,plain,(
    ! [A_17,B_21] :
      ( k2_relat_1('#skF_2'(A_17,B_21)) = k1_tarski(B_21)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_351,plain,(
    ! [A_88,B_87,A_86] :
      ( k2_relat_1('#skF_1'(A_88)) = k1_tarski(B_87)
      | k1_xboole_0 = A_86
      | A_88 != '#skF_3'
      | A_86 != '#skF_3'
      | k1_xboole_0 = A_86 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_20])).

tff(c_422,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_28])).

tff(c_440,plain,(
    ! [A_94,B_95] :
      ( k2_relat_1('#skF_1'(A_94)) = k1_tarski(B_95)
      | A_94 != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_80,plain,(
    ! [A_42,B_43] : k1_setfam_1(k2_tarski(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = k1_setfam_1(k1_tarski(A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_80])).

tff(c_92,plain,(
    ! [A_3] : k1_setfam_1(k1_tarski(A_3)) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_89])).

tff(c_476,plain,(
    ! [A_96] :
      ( k1_setfam_1(k2_relat_1('#skF_1'(A_96))) = k1_xboole_0
      | A_96 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_92])).

tff(c_448,plain,(
    ! [A_94,B_95] :
      ( k1_setfam_1(k2_relat_1('#skF_1'(A_94))) = B_95
      | A_94 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_92])).

tff(c_479,plain,(
    ! [B_95,A_96] :
      ( k1_xboole_0 = B_95
      | A_96 != '#skF_3'
      | A_96 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_448])).

tff(c_712,plain,(
    ! [A_96] :
      ( A_96 != '#skF_3'
      | A_96 != '#skF_3' ) ),
    inference(splitLeft,[status(thm)],[c_479])).

tff(c_719,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_712])).

tff(c_722,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_479])).

tff(c_720,plain,(
    ! [B_95] : k1_xboole_0 = B_95 ),
    inference(splitRight,[status(thm)],[c_479])).

tff(c_769,plain,(
    ! [B_1092] : B_1092 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_722,c_720])).

tff(c_817,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:15:17 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.46  
% 2.66/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.47  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.66/1.47  
% 2.66/1.47  %Foreground sorts:
% 2.66/1.47  
% 2.66/1.47  
% 2.66/1.47  %Background operators:
% 2.66/1.47  
% 2.66/1.47  
% 2.66/1.47  %Foreground operators:
% 2.66/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.66/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.66/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.66/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.66/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.66/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.66/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.66/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.66/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.66/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.66/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.66/1.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.66/1.47  
% 3.02/1.48  tff(f_47, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 3.02/1.48  tff(f_60, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 3.02/1.48  tff(f_79, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 3.02/1.48  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.02/1.48  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.02/1.48  tff(f_35, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.02/1.48  tff(c_16, plain, (![A_11]: (v1_funct_1('#skF_1'(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.02/1.48  tff(c_14, plain, (![A_11]: (k1_relat_1('#skF_1'(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.02/1.48  tff(c_18, plain, (![A_11]: (v1_relat_1('#skF_1'(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.02/1.48  tff(c_22, plain, (![A_17, B_21]: (k1_relat_1('#skF_2'(A_17, B_21))=A_17 | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.02/1.48  tff(c_24, plain, (![A_17, B_21]: (v1_funct_1('#skF_2'(A_17, B_21)) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.02/1.48  tff(c_26, plain, (![A_17, B_21]: (v1_relat_1('#skF_2'(A_17, B_21)) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.02/1.48  tff(c_71, plain, (![C_40, B_41]: (C_40=B_41 | k1_relat_1(C_40)!='#skF_3' | k1_relat_1(B_41)!='#skF_3' | ~v1_funct_1(C_40) | ~v1_relat_1(C_40) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.02/1.48  tff(c_75, plain, (![B_41, A_11]: (B_41='#skF_1'(A_11) | k1_relat_1('#skF_1'(A_11))!='#skF_3' | k1_relat_1(B_41)!='#skF_3' | ~v1_funct_1('#skF_1'(A_11)) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41))), inference(resolution, [status(thm)], [c_18, c_71])).
% 3.02/1.48  tff(c_141, plain, (![B_54, A_55]: (B_54='#skF_1'(A_55) | A_55!='#skF_3' | k1_relat_1(B_54)!='#skF_3' | ~v1_funct_1(B_54) | ~v1_relat_1(B_54))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_75])).
% 3.02/1.48  tff(c_214, plain, (![A_66, B_67, A_68]: ('#skF_2'(A_66, B_67)='#skF_1'(A_68) | A_68!='#skF_3' | k1_relat_1('#skF_2'(A_66, B_67))!='#skF_3' | ~v1_funct_1('#skF_2'(A_66, B_67)) | k1_xboole_0=A_66)), inference(resolution, [status(thm)], [c_26, c_141])).
% 3.02/1.48  tff(c_219, plain, (![A_69, B_70, A_71]: ('#skF_2'(A_69, B_70)='#skF_1'(A_71) | A_71!='#skF_3' | k1_relat_1('#skF_2'(A_69, B_70))!='#skF_3' | k1_xboole_0=A_69)), inference(resolution, [status(thm)], [c_24, c_214])).
% 3.02/1.48  tff(c_228, plain, (![A_75, B_76, A_77]: ('#skF_2'(A_75, B_76)='#skF_1'(A_77) | A_77!='#skF_3' | A_75!='#skF_3' | k1_xboole_0=A_75 | k1_xboole_0=A_75)), inference(superposition, [status(thm), theory('equality')], [c_22, c_219])).
% 3.02/1.48  tff(c_262, plain, (![A_75, B_76, A_77]: (k1_relat_1('#skF_2'(A_75, B_76))=A_77 | A_77!='#skF_3' | A_75!='#skF_3' | k1_xboole_0=A_75 | k1_xboole_0=A_75)), inference(superposition, [status(thm), theory('equality')], [c_228, c_14])).
% 3.02/1.48  tff(c_292, plain, (![A_81, B_82]: (k1_relat_1('#skF_2'(A_81, B_82))='#skF_3' | A_81!='#skF_3' | k1_xboole_0=A_81 | k1_xboole_0=A_81)), inference(reflexivity, [status(thm), theory('equality')], [c_262])).
% 3.02/1.48  tff(c_207, plain, (![B_60, A_61, B_62]: (B_60='#skF_2'(A_61, B_62) | k1_relat_1('#skF_2'(A_61, B_62))!='#skF_3' | k1_relat_1(B_60)!='#skF_3' | ~v1_funct_1('#skF_2'(A_61, B_62)) | ~v1_funct_1(B_60) | ~v1_relat_1(B_60) | k1_xboole_0=A_61)), inference(resolution, [status(thm)], [c_26, c_71])).
% 3.02/1.48  tff(c_210, plain, (![B_60, A_17, B_21]: (B_60='#skF_2'(A_17, B_21) | k1_relat_1('#skF_2'(A_17, B_21))!='#skF_3' | k1_relat_1(B_60)!='#skF_3' | ~v1_funct_1(B_60) | ~v1_relat_1(B_60) | k1_xboole_0=A_17)), inference(resolution, [status(thm)], [c_24, c_207])).
% 3.02/1.48  tff(c_318, plain, (![B_83, A_84, B_85]: (B_83='#skF_2'(A_84, B_85) | k1_relat_1(B_83)!='#skF_3' | ~v1_funct_1(B_83) | ~v1_relat_1(B_83) | A_84!='#skF_3' | k1_xboole_0=A_84)), inference(superposition, [status(thm), theory('equality')], [c_292, c_210])).
% 3.02/1.48  tff(c_322, plain, (![A_84, B_85, A_11]: ('#skF_2'(A_84, B_85)='#skF_1'(A_11) | k1_relat_1('#skF_1'(A_11))!='#skF_3' | ~v1_funct_1('#skF_1'(A_11)) | A_84!='#skF_3' | k1_xboole_0=A_84)), inference(resolution, [status(thm)], [c_18, c_318])).
% 3.02/1.48  tff(c_329, plain, (![A_86, B_87, A_88]: ('#skF_2'(A_86, B_87)='#skF_1'(A_88) | A_88!='#skF_3' | A_86!='#skF_3' | k1_xboole_0=A_86)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_322])).
% 3.02/1.48  tff(c_20, plain, (![A_17, B_21]: (k2_relat_1('#skF_2'(A_17, B_21))=k1_tarski(B_21) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.02/1.48  tff(c_351, plain, (![A_88, B_87, A_86]: (k2_relat_1('#skF_1'(A_88))=k1_tarski(B_87) | k1_xboole_0=A_86 | A_88!='#skF_3' | A_86!='#skF_3' | k1_xboole_0=A_86)), inference(superposition, [status(thm), theory('equality')], [c_329, c_20])).
% 3.02/1.48  tff(c_422, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_351])).
% 3.02/1.48  tff(c_28, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.02/1.48  tff(c_437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_422, c_28])).
% 3.02/1.48  tff(c_440, plain, (![A_94, B_95]: (k2_relat_1('#skF_1'(A_94))=k1_tarski(B_95) | A_94!='#skF_3')), inference(splitRight, [status(thm)], [c_351])).
% 3.02/1.48  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.02/1.48  tff(c_4, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.02/1.48  tff(c_80, plain, (![A_42, B_43]: (k1_setfam_1(k2_tarski(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.02/1.48  tff(c_89, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=k1_setfam_1(k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_80])).
% 3.02/1.48  tff(c_92, plain, (![A_3]: (k1_setfam_1(k1_tarski(A_3))=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_89])).
% 3.02/1.48  tff(c_476, plain, (![A_96]: (k1_setfam_1(k2_relat_1('#skF_1'(A_96)))=k1_xboole_0 | A_96!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_440, c_92])).
% 3.02/1.48  tff(c_448, plain, (![A_94, B_95]: (k1_setfam_1(k2_relat_1('#skF_1'(A_94)))=B_95 | A_94!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_440, c_92])).
% 3.02/1.48  tff(c_479, plain, (![B_95, A_96]: (k1_xboole_0=B_95 | A_96!='#skF_3' | A_96!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_476, c_448])).
% 3.02/1.48  tff(c_712, plain, (![A_96]: (A_96!='#skF_3' | A_96!='#skF_3')), inference(splitLeft, [status(thm)], [c_479])).
% 3.02/1.48  tff(c_719, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_712])).
% 3.02/1.48  tff(c_722, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_479])).
% 3.02/1.48  tff(c_720, plain, (![B_95]: (k1_xboole_0=B_95)), inference(splitRight, [status(thm)], [c_479])).
% 3.02/1.48  tff(c_769, plain, (![B_1092]: (B_1092='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_722, c_720])).
% 3.02/1.48  tff(c_817, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_769, c_28])).
% 3.02/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.48  
% 3.02/1.48  Inference rules
% 3.02/1.48  ----------------------
% 3.02/1.48  #Ref     : 4
% 3.02/1.48  #Sup     : 221
% 3.02/1.48  #Fact    : 0
% 3.02/1.48  #Define  : 0
% 3.02/1.48  #Split   : 3
% 3.02/1.48  #Chain   : 0
% 3.02/1.48  #Close   : 0
% 3.02/1.48  
% 3.02/1.48  Ordering : KBO
% 3.02/1.48  
% 3.02/1.48  Simplification rules
% 3.02/1.48  ----------------------
% 3.02/1.48  #Subsume      : 100
% 3.02/1.48  #Demod        : 40
% 3.02/1.48  #Tautology    : 44
% 3.02/1.48  #SimpNegUnit  : 0
% 3.02/1.48  #BackRed      : 9
% 3.02/1.48  
% 3.02/1.48  #Partial instantiations: 422
% 3.02/1.48  #Strategies tried      : 1
% 3.02/1.48  
% 3.02/1.48  Timing (in seconds)
% 3.02/1.48  ----------------------
% 3.02/1.48  Preprocessing        : 0.31
% 3.02/1.48  Parsing              : 0.16
% 3.02/1.48  CNF conversion       : 0.02
% 3.02/1.48  Main loop            : 0.36
% 3.02/1.48  Inferencing          : 0.15
% 3.02/1.48  Reduction            : 0.09
% 3.02/1.48  Demodulation         : 0.06
% 3.02/1.48  BG Simplification    : 0.02
% 3.02/1.48  Subsumption          : 0.08
% 3.02/1.48  Abstraction          : 0.02
% 3.02/1.48  MUC search           : 0.00
% 3.02/1.48  Cooper               : 0.00
% 3.02/1.48  Total                : 0.70
% 3.02/1.48  Index Insertion      : 0.00
% 3.02/1.48  Index Deletion       : 0.00
% 3.02/1.49  Index Matching       : 0.00
% 3.02/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
