%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:01 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   58 (  77 expanded)
%              Number of leaves         :   30 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :   95 ( 160 expanded)
%              Number of equality atoms :   55 (  86 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_9 > #skF_7 > #skF_5 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_56,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_99,negated_conjecture,(
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

tff(f_68,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_80,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(c_42,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_534,plain,(
    ! [A_197,B_198] :
      ( r2_hidden(k4_tarski('#skF_4'(A_197,B_198),'#skF_3'(A_197,B_198)),A_197)
      | r2_hidden('#skF_5'(A_197,B_198),B_198)
      | k2_relat_1(A_197) = B_198 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_128,plain,(
    ! [A_64,B_65] : ~ r2_hidden(A_64,k2_zfmisc_1(A_64,B_65)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_134,plain,(
    ! [A_9] : ~ r2_hidden(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_128])).

tff(c_549,plain,(
    ! [B_198] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_198),B_198)
      | k2_relat_1(k1_xboole_0) = B_198 ) ),
    inference(resolution,[status(thm)],[c_534,c_134])).

tff(c_555,plain,(
    ! [B_198] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_198),B_198)
      | k1_xboole_0 = B_198 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_549])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_556,plain,(
    ! [B_199] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_199),B_199)
      | k1_xboole_0 = B_199 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_549])).

tff(c_50,plain,(
    ! [A_32,B_33] : v1_funct_1('#skF_7'(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_48,plain,(
    ! [A_32,B_33] : k1_relat_1('#skF_7'(A_32,B_33)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_52,plain,(
    ! [A_32,B_33] : v1_relat_1('#skF_7'(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_58,plain,(
    ! [A_39] : v1_funct_1('#skF_8'(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_56,plain,(
    ! [A_39] : k1_relat_1('#skF_8'(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_60,plain,(
    ! [A_39] : v1_relat_1('#skF_8'(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_93,plain,(
    ! [C_59,B_60] :
      ( C_59 = B_60
      | k1_relat_1(C_59) != '#skF_9'
      | k1_relat_1(B_60) != '#skF_9'
      | ~ v1_funct_1(C_59)
      | ~ v1_relat_1(C_59)
      | ~ v1_funct_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_97,plain,(
    ! [B_60,A_39] :
      ( B_60 = '#skF_8'(A_39)
      | k1_relat_1('#skF_8'(A_39)) != '#skF_9'
      | k1_relat_1(B_60) != '#skF_9'
      | ~ v1_funct_1('#skF_8'(A_39))
      | ~ v1_funct_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_60,c_93])).

tff(c_159,plain,(
    ! [B_75,A_76] :
      ( B_75 = '#skF_8'(A_76)
      | A_76 != '#skF_9'
      | k1_relat_1(B_75) != '#skF_9'
      | ~ v1_funct_1(B_75)
      | ~ v1_relat_1(B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_97])).

tff(c_161,plain,(
    ! [A_76,A_32,B_33] :
      ( '#skF_8'(A_76) = '#skF_7'(A_32,B_33)
      | A_76 != '#skF_9'
      | k1_relat_1('#skF_7'(A_32,B_33)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_32,B_33)) ) ),
    inference(resolution,[status(thm)],[c_52,c_159])).

tff(c_293,plain,(
    ! [A_101,A_102,B_103] :
      ( '#skF_8'(A_101) = '#skF_7'(A_102,B_103)
      | A_101 != '#skF_9'
      | A_102 != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_161])).

tff(c_46,plain,(
    ! [A_32,B_33,D_38] :
      ( k1_funct_1('#skF_7'(A_32,B_33),D_38) = B_33
      | ~ r2_hidden(D_38,A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_302,plain,(
    ! [A_101,D_38,B_103,A_102] :
      ( k1_funct_1('#skF_8'(A_101),D_38) = B_103
      | ~ r2_hidden(D_38,A_102)
      | A_101 != '#skF_9'
      | A_102 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_46])).

tff(c_1023,plain,(
    ! [A_200,B_201] :
      ( k1_funct_1('#skF_8'(A_200),'#skF_5'(k1_xboole_0,B_201)) = '#skF_9'
      | A_200 != '#skF_9'
      | B_201 != '#skF_9'
      | k1_xboole_0 = B_201 ) ),
    inference(resolution,[status(thm)],[c_556,c_302])).

tff(c_54,plain,(
    ! [A_39,C_44] :
      ( k1_funct_1('#skF_8'(A_39),C_44) = k1_xboole_0
      | ~ r2_hidden(C_44,A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1026,plain,(
    ! [B_201,A_200] :
      ( k1_xboole_0 = '#skF_9'
      | ~ r2_hidden('#skF_5'(k1_xboole_0,B_201),A_200)
      | A_200 != '#skF_9'
      | B_201 != '#skF_9'
      | k1_xboole_0 = B_201 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1023,c_54])).

tff(c_1245,plain,(
    ! [B_1952,A_1953] :
      ( ~ r2_hidden('#skF_5'(k1_xboole_0,B_1952),A_1953)
      | A_1953 != '#skF_9'
      | B_1952 != '#skF_9'
      | k1_xboole_0 = B_1952 ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1026])).

tff(c_1292,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_555,c_1245])).

tff(c_1305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1292,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.55  
% 3.42/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.56  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_9 > #skF_7 > #skF_5 > #skF_4
% 3.42/1.56  
% 3.42/1.56  %Foreground sorts:
% 3.42/1.56  
% 3.42/1.56  
% 3.42/1.56  %Background operators:
% 3.42/1.56  
% 3.42/1.56  
% 3.42/1.56  %Foreground operators:
% 3.42/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.42/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.42/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.42/1.56  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.42/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.42/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.42/1.56  tff('#skF_8', type, '#skF_8': $i > $i).
% 3.42/1.56  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.42/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.42/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.42/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.42/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.42/1.56  tff('#skF_9', type, '#skF_9': $i).
% 3.42/1.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.42/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.42/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.42/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.56  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.42/1.56  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.42/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.42/1.56  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.42/1.56  
% 3.42/1.57  tff(f_56, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.42/1.57  tff(f_53, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 3.42/1.57  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.42/1.57  tff(f_45, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.42/1.57  tff(f_99, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 3.42/1.57  tff(f_68, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 3.42/1.57  tff(f_80, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 3.42/1.57  tff(c_42, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.42/1.57  tff(c_534, plain, (![A_197, B_198]: (r2_hidden(k4_tarski('#skF_4'(A_197, B_198), '#skF_3'(A_197, B_198)), A_197) | r2_hidden('#skF_5'(A_197, B_198), B_198) | k2_relat_1(A_197)=B_198)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.42/1.57  tff(c_24, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.42/1.57  tff(c_128, plain, (![A_64, B_65]: (~r2_hidden(A_64, k2_zfmisc_1(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.42/1.57  tff(c_134, plain, (![A_9]: (~r2_hidden(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_128])).
% 3.42/1.57  tff(c_549, plain, (![B_198]: (r2_hidden('#skF_5'(k1_xboole_0, B_198), B_198) | k2_relat_1(k1_xboole_0)=B_198)), inference(resolution, [status(thm)], [c_534, c_134])).
% 3.42/1.57  tff(c_555, plain, (![B_198]: (r2_hidden('#skF_5'(k1_xboole_0, B_198), B_198) | k1_xboole_0=B_198)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_549])).
% 3.42/1.57  tff(c_62, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.42/1.57  tff(c_556, plain, (![B_199]: (r2_hidden('#skF_5'(k1_xboole_0, B_199), B_199) | k1_xboole_0=B_199)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_549])).
% 3.42/1.57  tff(c_50, plain, (![A_32, B_33]: (v1_funct_1('#skF_7'(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.42/1.57  tff(c_48, plain, (![A_32, B_33]: (k1_relat_1('#skF_7'(A_32, B_33))=A_32)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.42/1.57  tff(c_52, plain, (![A_32, B_33]: (v1_relat_1('#skF_7'(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.42/1.57  tff(c_58, plain, (![A_39]: (v1_funct_1('#skF_8'(A_39)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.42/1.57  tff(c_56, plain, (![A_39]: (k1_relat_1('#skF_8'(A_39))=A_39)), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.42/1.57  tff(c_60, plain, (![A_39]: (v1_relat_1('#skF_8'(A_39)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.42/1.57  tff(c_93, plain, (![C_59, B_60]: (C_59=B_60 | k1_relat_1(C_59)!='#skF_9' | k1_relat_1(B_60)!='#skF_9' | ~v1_funct_1(C_59) | ~v1_relat_1(C_59) | ~v1_funct_1(B_60) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.42/1.57  tff(c_97, plain, (![B_60, A_39]: (B_60='#skF_8'(A_39) | k1_relat_1('#skF_8'(A_39))!='#skF_9' | k1_relat_1(B_60)!='#skF_9' | ~v1_funct_1('#skF_8'(A_39)) | ~v1_funct_1(B_60) | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_60, c_93])).
% 3.42/1.57  tff(c_159, plain, (![B_75, A_76]: (B_75='#skF_8'(A_76) | A_76!='#skF_9' | k1_relat_1(B_75)!='#skF_9' | ~v1_funct_1(B_75) | ~v1_relat_1(B_75))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_97])).
% 3.42/1.57  tff(c_161, plain, (![A_76, A_32, B_33]: ('#skF_8'(A_76)='#skF_7'(A_32, B_33) | A_76!='#skF_9' | k1_relat_1('#skF_7'(A_32, B_33))!='#skF_9' | ~v1_funct_1('#skF_7'(A_32, B_33)))), inference(resolution, [status(thm)], [c_52, c_159])).
% 3.42/1.57  tff(c_293, plain, (![A_101, A_102, B_103]: ('#skF_8'(A_101)='#skF_7'(A_102, B_103) | A_101!='#skF_9' | A_102!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_161])).
% 3.42/1.57  tff(c_46, plain, (![A_32, B_33, D_38]: (k1_funct_1('#skF_7'(A_32, B_33), D_38)=B_33 | ~r2_hidden(D_38, A_32))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.42/1.57  tff(c_302, plain, (![A_101, D_38, B_103, A_102]: (k1_funct_1('#skF_8'(A_101), D_38)=B_103 | ~r2_hidden(D_38, A_102) | A_101!='#skF_9' | A_102!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_293, c_46])).
% 3.42/1.57  tff(c_1023, plain, (![A_200, B_201]: (k1_funct_1('#skF_8'(A_200), '#skF_5'(k1_xboole_0, B_201))='#skF_9' | A_200!='#skF_9' | B_201!='#skF_9' | k1_xboole_0=B_201)), inference(resolution, [status(thm)], [c_556, c_302])).
% 3.42/1.57  tff(c_54, plain, (![A_39, C_44]: (k1_funct_1('#skF_8'(A_39), C_44)=k1_xboole_0 | ~r2_hidden(C_44, A_39))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.42/1.57  tff(c_1026, plain, (![B_201, A_200]: (k1_xboole_0='#skF_9' | ~r2_hidden('#skF_5'(k1_xboole_0, B_201), A_200) | A_200!='#skF_9' | B_201!='#skF_9' | k1_xboole_0=B_201)), inference(superposition, [status(thm), theory('equality')], [c_1023, c_54])).
% 3.42/1.57  tff(c_1245, plain, (![B_1952, A_1953]: (~r2_hidden('#skF_5'(k1_xboole_0, B_1952), A_1953) | A_1953!='#skF_9' | B_1952!='#skF_9' | k1_xboole_0=B_1952)), inference(negUnitSimplification, [status(thm)], [c_62, c_1026])).
% 3.42/1.57  tff(c_1292, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_555, c_1245])).
% 3.42/1.57  tff(c_1305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1292, c_62])).
% 3.42/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.57  
% 3.42/1.57  Inference rules
% 3.42/1.57  ----------------------
% 3.42/1.57  #Ref     : 1
% 3.42/1.57  #Sup     : 284
% 3.42/1.57  #Fact    : 0
% 3.42/1.57  #Define  : 0
% 3.42/1.57  #Split   : 0
% 3.42/1.57  #Chain   : 0
% 3.42/1.57  #Close   : 0
% 3.42/1.57  
% 3.42/1.57  Ordering : KBO
% 3.42/1.57  
% 3.42/1.57  Simplification rules
% 3.42/1.57  ----------------------
% 3.42/1.57  #Subsume      : 58
% 3.42/1.57  #Demod        : 53
% 3.42/1.57  #Tautology    : 42
% 3.42/1.57  #SimpNegUnit  : 2
% 3.42/1.57  #BackRed      : 9
% 3.42/1.57  
% 3.42/1.57  #Partial instantiations: 952
% 3.42/1.57  #Strategies tried      : 1
% 3.42/1.57  
% 3.42/1.57  Timing (in seconds)
% 3.42/1.57  ----------------------
% 3.42/1.57  Preprocessing        : 0.33
% 3.42/1.57  Parsing              : 0.17
% 3.42/1.57  CNF conversion       : 0.03
% 3.42/1.57  Main loop            : 0.48
% 3.42/1.57  Inferencing          : 0.19
% 3.42/1.57  Reduction            : 0.13
% 3.42/1.57  Demodulation         : 0.09
% 3.42/1.57  BG Simplification    : 0.03
% 3.42/1.57  Subsumption          : 0.10
% 3.42/1.57  Abstraction          : 0.02
% 3.42/1.57  MUC search           : 0.00
% 3.42/1.57  Cooper               : 0.00
% 3.42/1.57  Total                : 0.84
% 3.42/1.57  Index Insertion      : 0.00
% 3.42/1.57  Index Deletion       : 0.00
% 3.42/1.57  Index Matching       : 0.00
% 3.42/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
