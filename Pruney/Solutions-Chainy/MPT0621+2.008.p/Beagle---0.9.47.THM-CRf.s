%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:59 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 267 expanded)
%              Number of leaves         :   27 ( 102 expanded)
%              Depth                    :   13
%              Number of atoms          :  104 ( 815 expanded)
%              Number of equality atoms :   71 ( 515 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(np__1,type,(
    np__1: $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_53,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_66,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_85,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_20,plain,(
    ! [A_10] : v1_funct_1('#skF_1'(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_10] : k1_relat_1('#skF_1'(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_10] : v1_relat_1('#skF_1'(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [A_16,B_20] :
      ( k1_relat_1('#skF_2'(A_16,B_20)) = A_16
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,(
    ! [A_16,B_20] :
      ( v1_funct_1('#skF_2'(A_16,B_20))
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ! [A_16,B_20] :
      ( v1_relat_1('#skF_2'(A_16,B_20))
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_71,plain,(
    ! [C_39,B_40] :
      ( C_39 = B_40
      | k1_relat_1(C_39) != '#skF_3'
      | k1_relat_1(B_40) != '#skF_3'
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39)
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_166,plain,(
    ! [B_56,A_57,B_58] :
      ( B_56 = '#skF_2'(A_57,B_58)
      | k1_relat_1('#skF_2'(A_57,B_58)) != '#skF_3'
      | k1_relat_1(B_56) != '#skF_3'
      | ~ v1_funct_1('#skF_2'(A_57,B_58))
      | ~ v1_funct_1(B_56)
      | ~ v1_relat_1(B_56)
      | k1_xboole_0 = A_57 ) ),
    inference(resolution,[status(thm)],[c_30,c_71])).

tff(c_239,plain,(
    ! [B_68,A_69,B_70] :
      ( B_68 = '#skF_2'(A_69,B_70)
      | k1_relat_1('#skF_2'(A_69,B_70)) != '#skF_3'
      | k1_relat_1(B_68) != '#skF_3'
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68)
      | k1_xboole_0 = A_69 ) ),
    inference(resolution,[status(thm)],[c_28,c_166])).

tff(c_243,plain,(
    ! [B_71,A_72,B_73] :
      ( B_71 = '#skF_2'(A_72,B_73)
      | A_72 != '#skF_3'
      | k1_relat_1(B_71) != '#skF_3'
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71)
      | k1_xboole_0 = A_72
      | k1_xboole_0 = A_72 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_239])).

tff(c_247,plain,(
    ! [A_72,B_73,A_10] :
      ( '#skF_2'(A_72,B_73) = '#skF_1'(A_10)
      | A_72 != '#skF_3'
      | k1_relat_1('#skF_1'(A_10)) != '#skF_3'
      | ~ v1_funct_1('#skF_1'(A_10))
      | k1_xboole_0 = A_72 ) ),
    inference(resolution,[status(thm)],[c_22,c_243])).

tff(c_254,plain,(
    ! [A_74,B_75,A_76] :
      ( '#skF_2'(A_74,B_75) = '#skF_1'(A_76)
      | A_74 != '#skF_3'
      | A_76 != '#skF_3'
      | k1_xboole_0 = A_74 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_247])).

tff(c_24,plain,(
    ! [A_16,B_20] :
      ( k2_relat_1('#skF_2'(A_16,B_20)) = k1_tarski(B_20)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_274,plain,(
    ! [A_76,B_75,A_74] :
      ( k2_relat_1('#skF_1'(A_76)) = k1_tarski(B_75)
      | k1_xboole_0 = A_74
      | A_74 != '#skF_3'
      | A_76 != '#skF_3'
      | k1_xboole_0 = A_74 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_24])).

tff(c_346,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_274])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_32])).

tff(c_362,plain,(
    ! [A_85,B_86] :
      ( k2_relat_1('#skF_1'(A_85)) = k1_tarski(B_86)
      | A_85 != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_111,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_10,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_59,plain,(
    ! [A_37,B_38] : k1_setfam_1(k2_tarski(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_68,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = k1_setfam_1(k1_tarski(A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_59])).

tff(c_112,plain,(
    ! [A_5] : k1_setfam_1(k1_tarski(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_68])).

tff(c_403,plain,(
    ! [A_90] :
      ( k1_setfam_1(k2_relat_1('#skF_1'(A_90))) = np__1
      | A_90 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_112])).

tff(c_370,plain,(
    ! [A_85,B_86] :
      ( k1_setfam_1(k2_relat_1('#skF_1'(A_85))) = B_86
      | A_85 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_112])).

tff(c_406,plain,(
    ! [B_86,A_90] :
      ( np__1 = B_86
      | A_90 != '#skF_3'
      | A_90 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_370])).

tff(c_642,plain,(
    ! [A_90] :
      ( A_90 != '#skF_3'
      | A_90 != '#skF_3' ) ),
    inference(splitLeft,[status(thm)],[c_406])).

tff(c_648,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_642])).

tff(c_652,plain,(
    np__1 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_406])).

tff(c_649,plain,(
    ! [B_86] : np__1 = B_86 ),
    inference(splitRight,[status(thm)],[c_406])).

tff(c_730,plain,(
    ! [B_1116] : B_1116 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_652,c_649])).

tff(c_804,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_730,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:30:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.88  
% 3.40/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.88  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 3.40/1.88  
% 3.40/1.88  %Foreground sorts:
% 3.40/1.88  
% 3.40/1.88  
% 3.40/1.88  %Background operators:
% 3.40/1.88  
% 3.40/1.88  
% 3.40/1.88  %Foreground operators:
% 3.40/1.88  tff(np__1, type, np__1: $i).
% 3.40/1.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.40/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.40/1.88  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.40/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.40/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.40/1.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.40/1.88  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.88  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.40/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.40/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.40/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.40/1.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.40/1.88  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.40/1.88  
% 3.40/1.90  tff(f_53, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 3.40/1.90  tff(f_66, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 3.40/1.90  tff(f_85, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 3.40/1.90  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.40/1.90  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.40/1.90  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.40/1.90  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.40/1.90  tff(c_20, plain, (![A_10]: (v1_funct_1('#skF_1'(A_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.40/1.90  tff(c_18, plain, (![A_10]: (k1_relat_1('#skF_1'(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.40/1.90  tff(c_22, plain, (![A_10]: (v1_relat_1('#skF_1'(A_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.40/1.90  tff(c_26, plain, (![A_16, B_20]: (k1_relat_1('#skF_2'(A_16, B_20))=A_16 | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.40/1.90  tff(c_28, plain, (![A_16, B_20]: (v1_funct_1('#skF_2'(A_16, B_20)) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.40/1.90  tff(c_30, plain, (![A_16, B_20]: (v1_relat_1('#skF_2'(A_16, B_20)) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.40/1.90  tff(c_71, plain, (![C_39, B_40]: (C_39=B_40 | k1_relat_1(C_39)!='#skF_3' | k1_relat_1(B_40)!='#skF_3' | ~v1_funct_1(C_39) | ~v1_relat_1(C_39) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.40/1.90  tff(c_166, plain, (![B_56, A_57, B_58]: (B_56='#skF_2'(A_57, B_58) | k1_relat_1('#skF_2'(A_57, B_58))!='#skF_3' | k1_relat_1(B_56)!='#skF_3' | ~v1_funct_1('#skF_2'(A_57, B_58)) | ~v1_funct_1(B_56) | ~v1_relat_1(B_56) | k1_xboole_0=A_57)), inference(resolution, [status(thm)], [c_30, c_71])).
% 3.40/1.90  tff(c_239, plain, (![B_68, A_69, B_70]: (B_68='#skF_2'(A_69, B_70) | k1_relat_1('#skF_2'(A_69, B_70))!='#skF_3' | k1_relat_1(B_68)!='#skF_3' | ~v1_funct_1(B_68) | ~v1_relat_1(B_68) | k1_xboole_0=A_69)), inference(resolution, [status(thm)], [c_28, c_166])).
% 3.40/1.90  tff(c_243, plain, (![B_71, A_72, B_73]: (B_71='#skF_2'(A_72, B_73) | A_72!='#skF_3' | k1_relat_1(B_71)!='#skF_3' | ~v1_funct_1(B_71) | ~v1_relat_1(B_71) | k1_xboole_0=A_72 | k1_xboole_0=A_72)), inference(superposition, [status(thm), theory('equality')], [c_26, c_239])).
% 3.40/1.90  tff(c_247, plain, (![A_72, B_73, A_10]: ('#skF_2'(A_72, B_73)='#skF_1'(A_10) | A_72!='#skF_3' | k1_relat_1('#skF_1'(A_10))!='#skF_3' | ~v1_funct_1('#skF_1'(A_10)) | k1_xboole_0=A_72)), inference(resolution, [status(thm)], [c_22, c_243])).
% 3.40/1.90  tff(c_254, plain, (![A_74, B_75, A_76]: ('#skF_2'(A_74, B_75)='#skF_1'(A_76) | A_74!='#skF_3' | A_76!='#skF_3' | k1_xboole_0=A_74)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_247])).
% 3.40/1.90  tff(c_24, plain, (![A_16, B_20]: (k2_relat_1('#skF_2'(A_16, B_20))=k1_tarski(B_20) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.40/1.90  tff(c_274, plain, (![A_76, B_75, A_74]: (k2_relat_1('#skF_1'(A_76))=k1_tarski(B_75) | k1_xboole_0=A_74 | A_74!='#skF_3' | A_76!='#skF_3' | k1_xboole_0=A_74)), inference(superposition, [status(thm), theory('equality')], [c_254, c_24])).
% 3.40/1.90  tff(c_346, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_274])).
% 3.40/1.90  tff(c_32, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.40/1.90  tff(c_359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_346, c_32])).
% 3.40/1.90  tff(c_362, plain, (![A_85, B_86]: (k2_relat_1('#skF_1'(A_85))=k1_tarski(B_86) | A_85!='#skF_3')), inference(splitRight, [status(thm)], [c_274])).
% 3.40/1.90  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.40/1.90  tff(c_107, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=A_44 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.40/1.90  tff(c_111, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_107])).
% 3.40/1.90  tff(c_10, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.40/1.90  tff(c_59, plain, (![A_37, B_38]: (k1_setfam_1(k2_tarski(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.40/1.90  tff(c_68, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=k1_setfam_1(k1_tarski(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_59])).
% 3.40/1.90  tff(c_112, plain, (![A_5]: (k1_setfam_1(k1_tarski(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_68])).
% 3.40/1.90  tff(c_403, plain, (![A_90]: (k1_setfam_1(k2_relat_1('#skF_1'(A_90)))=np__1 | A_90!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_362, c_112])).
% 3.40/1.90  tff(c_370, plain, (![A_85, B_86]: (k1_setfam_1(k2_relat_1('#skF_1'(A_85)))=B_86 | A_85!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_362, c_112])).
% 3.40/1.90  tff(c_406, plain, (![B_86, A_90]: (np__1=B_86 | A_90!='#skF_3' | A_90!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_403, c_370])).
% 3.40/1.90  tff(c_642, plain, (![A_90]: (A_90!='#skF_3' | A_90!='#skF_3')), inference(splitLeft, [status(thm)], [c_406])).
% 3.40/1.90  tff(c_648, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_642])).
% 3.40/1.90  tff(c_652, plain, (np__1='#skF_3'), inference(splitRight, [status(thm)], [c_406])).
% 3.40/1.90  tff(c_649, plain, (![B_86]: (np__1=B_86)), inference(splitRight, [status(thm)], [c_406])).
% 3.40/1.90  tff(c_730, plain, (![B_1116]: (B_1116='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_652, c_649])).
% 3.40/1.90  tff(c_804, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_730, c_32])).
% 3.40/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.90  
% 3.40/1.90  Inference rules
% 3.40/1.90  ----------------------
% 3.40/1.90  #Ref     : 3
% 3.40/1.90  #Sup     : 225
% 3.40/1.90  #Fact    : 0
% 3.40/1.90  #Define  : 0
% 3.40/1.90  #Split   : 3
% 3.40/1.90  #Chain   : 0
% 3.40/1.90  #Close   : 0
% 3.40/1.90  
% 3.40/1.90  Ordering : KBO
% 3.40/1.90  
% 3.40/1.90  Simplification rules
% 3.40/1.90  ----------------------
% 3.40/1.90  #Subsume      : 84
% 3.40/1.90  #Demod        : 35
% 3.40/1.90  #Tautology    : 40
% 3.40/1.90  #SimpNegUnit  : 0
% 3.40/1.90  #BackRed      : 8
% 3.40/1.90  
% 3.40/1.90  #Partial instantiations: 491
% 3.40/1.90  #Strategies tried      : 1
% 3.40/1.90  
% 3.40/1.90  Timing (in seconds)
% 3.40/1.90  ----------------------
% 3.40/1.91  Preprocessing        : 0.49
% 3.40/1.91  Parsing              : 0.25
% 3.40/1.91  CNF conversion       : 0.03
% 3.40/1.91  Main loop            : 0.57
% 3.40/1.91  Inferencing          : 0.24
% 3.79/1.91  Reduction            : 0.15
% 3.79/1.91  Demodulation         : 0.11
% 3.79/1.91  BG Simplification    : 0.03
% 3.79/1.91  Subsumption          : 0.12
% 3.79/1.91  Abstraction          : 0.03
% 3.79/1.91  MUC search           : 0.00
% 3.79/1.91  Cooper               : 0.00
% 3.79/1.91  Total                : 1.10
% 3.79/1.91  Index Insertion      : 0.00
% 3.79/1.91  Index Deletion       : 0.00
% 3.79/1.91  Index Matching       : 0.00
% 3.79/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
