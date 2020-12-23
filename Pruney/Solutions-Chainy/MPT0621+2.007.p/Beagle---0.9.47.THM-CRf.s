%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:59 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 193 expanded)
%              Number of leaves         :   26 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 582 expanded)
%              Number of equality atoms :   69 ( 366 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

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

tff(c_361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_32])).

tff(c_364,plain,(
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

tff(c_420,plain,(
    ! [A_90] :
      ( k1_setfam_1(k2_relat_1('#skF_1'(A_90))) = '#skF_3'
      | A_90 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_112])).

tff(c_372,plain,(
    ! [A_85,B_86] :
      ( k1_setfam_1(k2_relat_1('#skF_1'(A_85))) = B_86
      | A_85 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_112])).

tff(c_423,plain,(
    ! [B_86,A_90] :
      ( B_86 = '#skF_3'
      | A_90 != '#skF_3'
      | A_90 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_372])).

tff(c_632,plain,(
    ! [A_90] :
      ( A_90 != '#skF_3'
      | A_90 != '#skF_3' ) ),
    inference(splitLeft,[status(thm)],[c_423])).

tff(c_638,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_632])).

tff(c_641,plain,(
    ! [B_619] : B_619 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_423])).

tff(c_718,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.47  
% 2.92/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.47  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.92/1.47  
% 2.92/1.47  %Foreground sorts:
% 2.92/1.47  
% 2.92/1.47  
% 2.92/1.47  %Background operators:
% 2.92/1.47  
% 2.92/1.47  
% 2.92/1.47  %Foreground operators:
% 2.92/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.92/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.92/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.92/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.92/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.92/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.92/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.92/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.92/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.92/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.92/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.92/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.92/1.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.92/1.47  
% 2.92/1.49  tff(f_53, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 2.92/1.49  tff(f_66, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 2.92/1.49  tff(f_85, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 2.92/1.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.92/1.49  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.92/1.49  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.92/1.49  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.92/1.49  tff(c_20, plain, (![A_10]: (v1_funct_1('#skF_1'(A_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.92/1.49  tff(c_18, plain, (![A_10]: (k1_relat_1('#skF_1'(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.92/1.49  tff(c_22, plain, (![A_10]: (v1_relat_1('#skF_1'(A_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.92/1.49  tff(c_26, plain, (![A_16, B_20]: (k1_relat_1('#skF_2'(A_16, B_20))=A_16 | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.92/1.49  tff(c_28, plain, (![A_16, B_20]: (v1_funct_1('#skF_2'(A_16, B_20)) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.92/1.49  tff(c_30, plain, (![A_16, B_20]: (v1_relat_1('#skF_2'(A_16, B_20)) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.92/1.49  tff(c_71, plain, (![C_39, B_40]: (C_39=B_40 | k1_relat_1(C_39)!='#skF_3' | k1_relat_1(B_40)!='#skF_3' | ~v1_funct_1(C_39) | ~v1_relat_1(C_39) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.92/1.49  tff(c_166, plain, (![B_56, A_57, B_58]: (B_56='#skF_2'(A_57, B_58) | k1_relat_1('#skF_2'(A_57, B_58))!='#skF_3' | k1_relat_1(B_56)!='#skF_3' | ~v1_funct_1('#skF_2'(A_57, B_58)) | ~v1_funct_1(B_56) | ~v1_relat_1(B_56) | k1_xboole_0=A_57)), inference(resolution, [status(thm)], [c_30, c_71])).
% 2.92/1.49  tff(c_239, plain, (![B_68, A_69, B_70]: (B_68='#skF_2'(A_69, B_70) | k1_relat_1('#skF_2'(A_69, B_70))!='#skF_3' | k1_relat_1(B_68)!='#skF_3' | ~v1_funct_1(B_68) | ~v1_relat_1(B_68) | k1_xboole_0=A_69)), inference(resolution, [status(thm)], [c_28, c_166])).
% 2.92/1.49  tff(c_243, plain, (![B_71, A_72, B_73]: (B_71='#skF_2'(A_72, B_73) | A_72!='#skF_3' | k1_relat_1(B_71)!='#skF_3' | ~v1_funct_1(B_71) | ~v1_relat_1(B_71) | k1_xboole_0=A_72 | k1_xboole_0=A_72)), inference(superposition, [status(thm), theory('equality')], [c_26, c_239])).
% 2.92/1.49  tff(c_247, plain, (![A_72, B_73, A_10]: ('#skF_2'(A_72, B_73)='#skF_1'(A_10) | A_72!='#skF_3' | k1_relat_1('#skF_1'(A_10))!='#skF_3' | ~v1_funct_1('#skF_1'(A_10)) | k1_xboole_0=A_72)), inference(resolution, [status(thm)], [c_22, c_243])).
% 2.92/1.49  tff(c_254, plain, (![A_74, B_75, A_76]: ('#skF_2'(A_74, B_75)='#skF_1'(A_76) | A_74!='#skF_3' | A_76!='#skF_3' | k1_xboole_0=A_74)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_247])).
% 2.92/1.49  tff(c_24, plain, (![A_16, B_20]: (k2_relat_1('#skF_2'(A_16, B_20))=k1_tarski(B_20) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.92/1.49  tff(c_274, plain, (![A_76, B_75, A_74]: (k2_relat_1('#skF_1'(A_76))=k1_tarski(B_75) | k1_xboole_0=A_74 | A_74!='#skF_3' | A_76!='#skF_3' | k1_xboole_0=A_74)), inference(superposition, [status(thm), theory('equality')], [c_254, c_24])).
% 2.92/1.49  tff(c_346, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_274])).
% 2.92/1.49  tff(c_32, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.92/1.49  tff(c_361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_346, c_32])).
% 2.92/1.49  tff(c_364, plain, (![A_85, B_86]: (k2_relat_1('#skF_1'(A_85))=k1_tarski(B_86) | A_85!='#skF_3')), inference(splitRight, [status(thm)], [c_274])).
% 2.92/1.49  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.49  tff(c_107, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=A_44 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.92/1.49  tff(c_111, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_107])).
% 2.92/1.49  tff(c_10, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.92/1.49  tff(c_59, plain, (![A_37, B_38]: (k1_setfam_1(k2_tarski(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.92/1.49  tff(c_68, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=k1_setfam_1(k1_tarski(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_59])).
% 2.92/1.49  tff(c_112, plain, (![A_5]: (k1_setfam_1(k1_tarski(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_68])).
% 2.92/1.49  tff(c_420, plain, (![A_90]: (k1_setfam_1(k2_relat_1('#skF_1'(A_90)))='#skF_3' | A_90!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_364, c_112])).
% 2.92/1.49  tff(c_372, plain, (![A_85, B_86]: (k1_setfam_1(k2_relat_1('#skF_1'(A_85)))=B_86 | A_85!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_364, c_112])).
% 2.92/1.49  tff(c_423, plain, (![B_86, A_90]: (B_86='#skF_3' | A_90!='#skF_3' | A_90!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_420, c_372])).
% 2.92/1.49  tff(c_632, plain, (![A_90]: (A_90!='#skF_3' | A_90!='#skF_3')), inference(splitLeft, [status(thm)], [c_423])).
% 2.92/1.49  tff(c_638, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_632])).
% 2.92/1.49  tff(c_641, plain, (![B_619]: (B_619='#skF_3')), inference(splitRight, [status(thm)], [c_423])).
% 2.92/1.49  tff(c_718, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_641, c_32])).
% 2.92/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.49  
% 2.92/1.49  Inference rules
% 2.92/1.49  ----------------------
% 2.92/1.49  #Ref     : 3
% 2.92/1.49  #Sup     : 187
% 2.92/1.49  #Fact    : 0
% 2.92/1.49  #Define  : 0
% 2.92/1.49  #Split   : 3
% 2.92/1.49  #Chain   : 0
% 2.92/1.49  #Close   : 0
% 2.92/1.49  
% 2.92/1.49  Ordering : KBO
% 2.92/1.49  
% 2.92/1.49  Simplification rules
% 2.92/1.49  ----------------------
% 2.92/1.49  #Subsume      : 65
% 2.92/1.49  #Demod        : 37
% 2.92/1.49  #Tautology    : 40
% 2.92/1.49  #SimpNegUnit  : 1
% 2.92/1.49  #BackRed      : 10
% 2.92/1.49  
% 2.92/1.49  #Partial instantiations: 384
% 2.92/1.49  #Strategies tried      : 1
% 2.92/1.49  
% 2.92/1.49  Timing (in seconds)
% 2.92/1.49  ----------------------
% 2.92/1.49  Preprocessing        : 0.31
% 2.92/1.49  Parsing              : 0.17
% 2.92/1.49  CNF conversion       : 0.02
% 2.92/1.49  Main loop            : 0.34
% 2.92/1.49  Inferencing          : 0.14
% 2.92/1.49  Reduction            : 0.09
% 2.92/1.49  Demodulation         : 0.06
% 2.92/1.49  BG Simplification    : 0.02
% 2.92/1.49  Subsumption          : 0.07
% 2.92/1.49  Abstraction          : 0.02
% 2.92/1.49  MUC search           : 0.00
% 2.92/1.49  Cooper               : 0.00
% 2.92/1.49  Total                : 0.68
% 2.92/1.49  Index Insertion      : 0.00
% 2.92/1.49  Index Deletion       : 0.00
% 2.92/1.49  Index Matching       : 0.00
% 2.92/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
