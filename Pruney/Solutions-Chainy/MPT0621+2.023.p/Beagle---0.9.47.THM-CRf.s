%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:01 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 157 expanded)
%              Number of leaves         :   23 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  103 ( 537 expanded)
%              Number of equality atoms :   69 ( 334 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_50,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_82,negated_conjecture,(
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

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_28,plain,(
    ! [A_10] : v1_funct_1('#skF_3'(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26,plain,(
    ! [A_10] : k1_relat_1('#skF_3'(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,(
    ! [A_10] : v1_relat_1('#skF_3'(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_34,plain,(
    ! [A_16,B_20] :
      ( k1_relat_1('#skF_4'(A_16,B_20)) = A_16
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,(
    ! [A_16,B_20] :
      ( v1_funct_1('#skF_4'(A_16,B_20))
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_79,plain,(
    ! [A_39,B_40] :
      ( v1_relat_1('#skF_4'(A_39,B_40))
      | k1_xboole_0 = A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    ! [C_27,B_25] :
      ( C_27 = B_25
      | k1_relat_1(C_27) != '#skF_5'
      | k1_relat_1(B_25) != '#skF_5'
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27)
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_152,plain,(
    ! [B_58,A_59,B_60] :
      ( B_58 = '#skF_4'(A_59,B_60)
      | k1_relat_1('#skF_4'(A_59,B_60)) != '#skF_5'
      | k1_relat_1(B_58) != '#skF_5'
      | ~ v1_funct_1('#skF_4'(A_59,B_60))
      | ~ v1_funct_1(B_58)
      | ~ v1_relat_1(B_58)
      | k1_xboole_0 = A_59 ) ),
    inference(resolution,[status(thm)],[c_79,c_42])).

tff(c_257,plain,(
    ! [B_79,A_80,B_81] :
      ( B_79 = '#skF_4'(A_80,B_81)
      | k1_relat_1('#skF_4'(A_80,B_81)) != '#skF_5'
      | k1_relat_1(B_79) != '#skF_5'
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79)
      | k1_xboole_0 = A_80 ) ),
    inference(resolution,[status(thm)],[c_36,c_152])).

tff(c_263,plain,(
    ! [B_88,A_89,B_90] :
      ( B_88 = '#skF_4'(A_89,B_90)
      | A_89 != '#skF_5'
      | k1_relat_1(B_88) != '#skF_5'
      | ~ v1_funct_1(B_88)
      | ~ v1_relat_1(B_88)
      | k1_xboole_0 = A_89
      | k1_xboole_0 = A_89 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_257])).

tff(c_267,plain,(
    ! [A_89,B_90,A_10] :
      ( '#skF_4'(A_89,B_90) = '#skF_3'(A_10)
      | A_89 != '#skF_5'
      | k1_relat_1('#skF_3'(A_10)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_10))
      | k1_xboole_0 = A_89 ) ),
    inference(resolution,[status(thm)],[c_30,c_263])).

tff(c_274,plain,(
    ! [A_91,B_92,A_93] :
      ( '#skF_4'(A_91,B_92) = '#skF_3'(A_93)
      | A_91 != '#skF_5'
      | A_93 != '#skF_5'
      | k1_xboole_0 = A_91 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_267])).

tff(c_32,plain,(
    ! [A_16,B_20] :
      ( k2_relat_1('#skF_4'(A_16,B_20)) = k1_tarski(B_20)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_294,plain,(
    ! [A_93,B_92,A_91] :
      ( k2_relat_1('#skF_3'(A_93)) = k1_tarski(B_92)
      | k1_xboole_0 = A_91
      | A_91 != '#skF_5'
      | A_93 != '#skF_5'
      | k1_xboole_0 = A_91 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_32])).

tff(c_985,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_294])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1004,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_40])).

tff(c_1005,plain,(
    ! [A_93,B_92] :
      ( k2_relat_1('#skF_3'(A_93)) = k1_tarski(B_92)
      | A_93 != '#skF_5' ) ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_1007,plain,(
    ! [A_1585,B_1586] :
      ( k2_relat_1('#skF_3'(A_1585)) = k1_tarski(B_1586)
      | A_1585 != '#skF_5' ) ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_1026,plain,(
    ! [B_92,B_1586,A_93] :
      ( k1_tarski(B_92) = k1_tarski(B_1586)
      | A_93 != '#skF_5'
      | A_93 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1005,c_1007])).

tff(c_1562,plain,(
    ! [A_93] :
      ( A_93 != '#skF_5'
      | A_93 != '#skF_5' ) ),
    inference(splitLeft,[status(thm)],[c_1026])).

tff(c_1568,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1562])).

tff(c_1586,plain,(
    ! [B_2546,B_2545] : k1_tarski(B_2546) = k1_tarski(B_2545) ),
    inference(splitRight,[status(thm)],[c_1026])).

tff(c_56,plain,(
    ! [A_35] : k2_tarski(A_35,A_35) = k1_tarski(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_62,plain,(
    ! [A_35] : r2_hidden(A_35,k1_tarski(A_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_4])).

tff(c_1613,plain,(
    ! [B_2545,B_2546] : r2_hidden(B_2545,k1_tarski(B_2546)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1586,c_62])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_122,plain,(
    ! [D_51,B_52,A_53] :
      ( D_51 = B_52
      | D_51 = A_53
      | ~ r2_hidden(D_51,k2_tarski(A_53,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_125,plain,(
    ! [D_51,A_7] :
      ( D_51 = A_7
      | D_51 = A_7
      | ~ r2_hidden(D_51,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_122])).

tff(c_1753,plain,(
    ! [D_2663,A_2664] : D_2663 = A_2664 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1613,c_125])).

tff(c_2429,plain,(
    ! [A_2664] : A_2664 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1753,c_40])).

tff(c_2500,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2429])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.65  
% 3.82/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.65  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.82/1.65  
% 3.82/1.65  %Foreground sorts:
% 3.82/1.65  
% 3.82/1.65  
% 3.82/1.65  %Background operators:
% 3.82/1.65  
% 3.82/1.65  
% 3.82/1.65  %Foreground operators:
% 3.82/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.82/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.82/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.82/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.82/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.82/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.82/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.82/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.82/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.82/1.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.82/1.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.82/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.82/1.65  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.82/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.82/1.65  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.82/1.65  
% 3.82/1.66  tff(f_50, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 3.82/1.66  tff(f_63, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 3.82/1.66  tff(f_82, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 3.82/1.66  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.82/1.66  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.82/1.66  tff(c_28, plain, (![A_10]: (v1_funct_1('#skF_3'(A_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.82/1.66  tff(c_26, plain, (![A_10]: (k1_relat_1('#skF_3'(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.82/1.66  tff(c_30, plain, (![A_10]: (v1_relat_1('#skF_3'(A_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.82/1.66  tff(c_34, plain, (![A_16, B_20]: (k1_relat_1('#skF_4'(A_16, B_20))=A_16 | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.82/1.66  tff(c_36, plain, (![A_16, B_20]: (v1_funct_1('#skF_4'(A_16, B_20)) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.82/1.66  tff(c_79, plain, (![A_39, B_40]: (v1_relat_1('#skF_4'(A_39, B_40)) | k1_xboole_0=A_39)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.82/1.66  tff(c_42, plain, (![C_27, B_25]: (C_27=B_25 | k1_relat_1(C_27)!='#skF_5' | k1_relat_1(B_25)!='#skF_5' | ~v1_funct_1(C_27) | ~v1_relat_1(C_27) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.82/1.66  tff(c_152, plain, (![B_58, A_59, B_60]: (B_58='#skF_4'(A_59, B_60) | k1_relat_1('#skF_4'(A_59, B_60))!='#skF_5' | k1_relat_1(B_58)!='#skF_5' | ~v1_funct_1('#skF_4'(A_59, B_60)) | ~v1_funct_1(B_58) | ~v1_relat_1(B_58) | k1_xboole_0=A_59)), inference(resolution, [status(thm)], [c_79, c_42])).
% 3.82/1.66  tff(c_257, plain, (![B_79, A_80, B_81]: (B_79='#skF_4'(A_80, B_81) | k1_relat_1('#skF_4'(A_80, B_81))!='#skF_5' | k1_relat_1(B_79)!='#skF_5' | ~v1_funct_1(B_79) | ~v1_relat_1(B_79) | k1_xboole_0=A_80)), inference(resolution, [status(thm)], [c_36, c_152])).
% 3.82/1.66  tff(c_263, plain, (![B_88, A_89, B_90]: (B_88='#skF_4'(A_89, B_90) | A_89!='#skF_5' | k1_relat_1(B_88)!='#skF_5' | ~v1_funct_1(B_88) | ~v1_relat_1(B_88) | k1_xboole_0=A_89 | k1_xboole_0=A_89)), inference(superposition, [status(thm), theory('equality')], [c_34, c_257])).
% 3.82/1.66  tff(c_267, plain, (![A_89, B_90, A_10]: ('#skF_4'(A_89, B_90)='#skF_3'(A_10) | A_89!='#skF_5' | k1_relat_1('#skF_3'(A_10))!='#skF_5' | ~v1_funct_1('#skF_3'(A_10)) | k1_xboole_0=A_89)), inference(resolution, [status(thm)], [c_30, c_263])).
% 3.82/1.66  tff(c_274, plain, (![A_91, B_92, A_93]: ('#skF_4'(A_91, B_92)='#skF_3'(A_93) | A_91!='#skF_5' | A_93!='#skF_5' | k1_xboole_0=A_91)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_267])).
% 3.82/1.66  tff(c_32, plain, (![A_16, B_20]: (k2_relat_1('#skF_4'(A_16, B_20))=k1_tarski(B_20) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.82/1.66  tff(c_294, plain, (![A_93, B_92, A_91]: (k2_relat_1('#skF_3'(A_93))=k1_tarski(B_92) | k1_xboole_0=A_91 | A_91!='#skF_5' | A_93!='#skF_5' | k1_xboole_0=A_91)), inference(superposition, [status(thm), theory('equality')], [c_274, c_32])).
% 3.82/1.66  tff(c_985, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_294])).
% 3.82/1.66  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.82/1.66  tff(c_1004, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_985, c_40])).
% 3.82/1.66  tff(c_1005, plain, (![A_93, B_92]: (k2_relat_1('#skF_3'(A_93))=k1_tarski(B_92) | A_93!='#skF_5')), inference(splitRight, [status(thm)], [c_294])).
% 3.82/1.66  tff(c_1007, plain, (![A_1585, B_1586]: (k2_relat_1('#skF_3'(A_1585))=k1_tarski(B_1586) | A_1585!='#skF_5')), inference(splitRight, [status(thm)], [c_294])).
% 3.82/1.66  tff(c_1026, plain, (![B_92, B_1586, A_93]: (k1_tarski(B_92)=k1_tarski(B_1586) | A_93!='#skF_5' | A_93!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1005, c_1007])).
% 3.82/1.66  tff(c_1562, plain, (![A_93]: (A_93!='#skF_5' | A_93!='#skF_5')), inference(splitLeft, [status(thm)], [c_1026])).
% 3.82/1.66  tff(c_1568, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_1562])).
% 3.82/1.66  tff(c_1586, plain, (![B_2546, B_2545]: (k1_tarski(B_2546)=k1_tarski(B_2545))), inference(splitRight, [status(thm)], [c_1026])).
% 3.82/1.66  tff(c_56, plain, (![A_35]: (k2_tarski(A_35, A_35)=k1_tarski(A_35))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.82/1.66  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.82/1.66  tff(c_62, plain, (![A_35]: (r2_hidden(A_35, k1_tarski(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_4])).
% 3.82/1.66  tff(c_1613, plain, (![B_2545, B_2546]: (r2_hidden(B_2545, k1_tarski(B_2546)))), inference(superposition, [status(thm), theory('equality')], [c_1586, c_62])).
% 3.82/1.66  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.82/1.66  tff(c_122, plain, (![D_51, B_52, A_53]: (D_51=B_52 | D_51=A_53 | ~r2_hidden(D_51, k2_tarski(A_53, B_52)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.82/1.66  tff(c_125, plain, (![D_51, A_7]: (D_51=A_7 | D_51=A_7 | ~r2_hidden(D_51, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_122])).
% 3.82/1.66  tff(c_1753, plain, (![D_2663, A_2664]: (D_2663=A_2664)), inference(demodulation, [status(thm), theory('equality')], [c_1613, c_125])).
% 3.82/1.66  tff(c_2429, plain, (![A_2664]: (A_2664!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1753, c_40])).
% 3.82/1.66  tff(c_2500, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_2429])).
% 3.82/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.66  
% 3.82/1.66  Inference rules
% 3.82/1.66  ----------------------
% 3.82/1.66  #Ref     : 4
% 3.82/1.66  #Sup     : 405
% 3.82/1.66  #Fact    : 4
% 3.82/1.66  #Define  : 0
% 3.82/1.66  #Split   : 2
% 3.82/1.66  #Chain   : 0
% 3.82/1.66  #Close   : 0
% 3.82/1.66  
% 3.82/1.66  Ordering : KBO
% 3.82/1.66  
% 3.82/1.66  Simplification rules
% 3.82/1.66  ----------------------
% 3.82/1.66  #Subsume      : 109
% 3.82/1.66  #Demod        : 75
% 3.82/1.66  #Tautology    : 81
% 3.82/1.66  #SimpNegUnit  : 0
% 3.82/1.66  #BackRed      : 14
% 3.82/1.66  
% 3.82/1.66  #Partial instantiations: 1848
% 3.82/1.66  #Strategies tried      : 1
% 3.82/1.66  
% 3.82/1.66  Timing (in seconds)
% 3.82/1.66  ----------------------
% 3.82/1.67  Preprocessing        : 0.38
% 3.82/1.67  Parsing              : 0.21
% 3.82/1.67  CNF conversion       : 0.03
% 3.82/1.67  Main loop            : 0.53
% 3.82/1.67  Inferencing          : 0.26
% 3.82/1.67  Reduction            : 0.12
% 3.82/1.67  Demodulation         : 0.09
% 3.82/1.67  BG Simplification    : 0.03
% 3.82/1.67  Subsumption          : 0.09
% 3.82/1.67  Abstraction          : 0.03
% 3.82/1.67  MUC search           : 0.00
% 3.82/1.67  Cooper               : 0.00
% 3.82/1.67  Total                : 0.93
% 3.82/1.67  Index Insertion      : 0.00
% 3.82/1.67  Index Deletion       : 0.00
% 3.82/1.67  Index Matching       : 0.00
% 3.82/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
