%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:21 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   60 (  76 expanded)
%              Number of leaves         :   33 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 ( 100 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_12,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_253,plain,(
    ! [B_94,A_95] :
      ( ~ r2_hidden(B_94,A_95)
      | k4_xboole_0(A_95,k1_tarski(B_94)) != A_95 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_258,plain,(
    ! [B_94] : ~ r2_hidden(B_94,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_253])).

tff(c_48,plain,
    ( k11_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_80,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,
    ( r2_hidden('#skF_7',k1_relat_1('#skF_8'))
    | k11_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_113,plain,(
    k11_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_54])).

tff(c_46,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_157,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_1'(A_83,B_84),B_84)
      | r2_hidden('#skF_2'(A_83,B_84),A_83)
      | B_84 = A_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_81,plain,(
    ! [B_57,A_58] :
      ( ~ r2_hidden(B_57,A_58)
      | k4_xboole_0(A_58,k1_tarski(B_57)) != A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_86,plain,(
    ! [B_57] : ~ r2_hidden(B_57,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_81])).

tff(c_171,plain,(
    ! [B_84] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_84),B_84)
      | k1_xboole_0 = B_84 ) ),
    inference(resolution,[status(thm)],[c_157,c_86])).

tff(c_172,plain,(
    ! [A_85,B_86,C_87] :
      ( r2_hidden(k4_tarski(A_85,B_86),C_87)
      | ~ r2_hidden(B_86,k11_relat_1(C_87,A_85))
      | ~ v1_relat_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    ! [C_46,A_31,D_49] :
      ( r2_hidden(C_46,k1_relat_1(A_31))
      | ~ r2_hidden(k4_tarski(C_46,D_49),A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_198,plain,(
    ! [A_89,C_90,B_91] :
      ( r2_hidden(A_89,k1_relat_1(C_90))
      | ~ r2_hidden(B_91,k11_relat_1(C_90,A_89))
      | ~ v1_relat_1(C_90) ) ),
    inference(resolution,[status(thm)],[c_172,c_32])).

tff(c_219,plain,(
    ! [A_92,C_93] :
      ( r2_hidden(A_92,k1_relat_1(C_93))
      | ~ v1_relat_1(C_93)
      | k11_relat_1(C_93,A_92) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_171,c_198])).

tff(c_237,plain,
    ( ~ v1_relat_1('#skF_8')
    | k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_219,c_80])).

tff(c_244,plain,(
    k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_237])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_244])).

tff(c_248,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_247,plain,(
    k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_422,plain,(
    ! [C_133,A_134] :
      ( r2_hidden(k4_tarski(C_133,'#skF_6'(A_134,k1_relat_1(A_134),C_133)),A_134)
      | ~ r2_hidden(C_133,k1_relat_1(A_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_44,plain,(
    ! [B_51,C_52,A_50] :
      ( r2_hidden(B_51,k11_relat_1(C_52,A_50))
      | ~ r2_hidden(k4_tarski(A_50,B_51),C_52)
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1146,plain,(
    ! [A_181,C_182] :
      ( r2_hidden('#skF_6'(A_181,k1_relat_1(A_181),C_182),k11_relat_1(A_181,C_182))
      | ~ v1_relat_1(A_181)
      | ~ r2_hidden(C_182,k1_relat_1(A_181)) ) ),
    inference(resolution,[status(thm)],[c_422,c_44])).

tff(c_1166,plain,
    ( r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0)
    | ~ v1_relat_1('#skF_8')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_1146])).

tff(c_1171,plain,(
    r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_46,c_1166])).

tff(c_1173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_1171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.72  
% 3.10/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.73  %$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 3.10/1.73  
% 3.10/1.73  %Foreground sorts:
% 3.10/1.73  
% 3.10/1.73  
% 3.10/1.73  %Background operators:
% 3.10/1.73  
% 3.10/1.73  
% 3.10/1.73  %Foreground operators:
% 3.10/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.73  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.10/1.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.10/1.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.10/1.73  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.10/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.73  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.10/1.73  tff('#skF_7', type, '#skF_7': $i).
% 3.10/1.73  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.10/1.73  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.10/1.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.10/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.10/1.73  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.10/1.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.10/1.73  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.10/1.73  tff('#skF_8', type, '#skF_8': $i).
% 3.10/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.10/1.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.10/1.73  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.10/1.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.10/1.73  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.10/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.10/1.73  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.10/1.73  
% 3.40/1.74  tff(f_36, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.40/1.74  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.40/1.74  tff(f_75, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.40/1.74  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 3.40/1.74  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 3.40/1.74  tff(f_61, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.40/1.74  tff(c_12, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.40/1.74  tff(c_253, plain, (![B_94, A_95]: (~r2_hidden(B_94, A_95) | k4_xboole_0(A_95, k1_tarski(B_94))!=A_95)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.40/1.74  tff(c_258, plain, (![B_94]: (~r2_hidden(B_94, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_253])).
% 3.40/1.74  tff(c_48, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0 | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.40/1.74  tff(c_80, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_48])).
% 3.40/1.74  tff(c_54, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8')) | k11_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.40/1.74  tff(c_113, plain, (k11_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_80, c_54])).
% 3.40/1.74  tff(c_46, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.40/1.74  tff(c_157, plain, (![A_83, B_84]: (r2_hidden('#skF_1'(A_83, B_84), B_84) | r2_hidden('#skF_2'(A_83, B_84), A_83) | B_84=A_83)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.40/1.74  tff(c_81, plain, (![B_57, A_58]: (~r2_hidden(B_57, A_58) | k4_xboole_0(A_58, k1_tarski(B_57))!=A_58)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.40/1.74  tff(c_86, plain, (![B_57]: (~r2_hidden(B_57, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_81])).
% 3.40/1.74  tff(c_171, plain, (![B_84]: (r2_hidden('#skF_1'(k1_xboole_0, B_84), B_84) | k1_xboole_0=B_84)), inference(resolution, [status(thm)], [c_157, c_86])).
% 3.40/1.74  tff(c_172, plain, (![A_85, B_86, C_87]: (r2_hidden(k4_tarski(A_85, B_86), C_87) | ~r2_hidden(B_86, k11_relat_1(C_87, A_85)) | ~v1_relat_1(C_87))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.40/1.74  tff(c_32, plain, (![C_46, A_31, D_49]: (r2_hidden(C_46, k1_relat_1(A_31)) | ~r2_hidden(k4_tarski(C_46, D_49), A_31))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.40/1.74  tff(c_198, plain, (![A_89, C_90, B_91]: (r2_hidden(A_89, k1_relat_1(C_90)) | ~r2_hidden(B_91, k11_relat_1(C_90, A_89)) | ~v1_relat_1(C_90))), inference(resolution, [status(thm)], [c_172, c_32])).
% 3.40/1.74  tff(c_219, plain, (![A_92, C_93]: (r2_hidden(A_92, k1_relat_1(C_93)) | ~v1_relat_1(C_93) | k11_relat_1(C_93, A_92)=k1_xboole_0)), inference(resolution, [status(thm)], [c_171, c_198])).
% 3.40/1.74  tff(c_237, plain, (~v1_relat_1('#skF_8') | k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_219, c_80])).
% 3.40/1.74  tff(c_244, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_237])).
% 3.40/1.74  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_244])).
% 3.40/1.74  tff(c_248, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_48])).
% 3.40/1.74  tff(c_247, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 3.40/1.74  tff(c_422, plain, (![C_133, A_134]: (r2_hidden(k4_tarski(C_133, '#skF_6'(A_134, k1_relat_1(A_134), C_133)), A_134) | ~r2_hidden(C_133, k1_relat_1(A_134)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.40/1.74  tff(c_44, plain, (![B_51, C_52, A_50]: (r2_hidden(B_51, k11_relat_1(C_52, A_50)) | ~r2_hidden(k4_tarski(A_50, B_51), C_52) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.40/1.74  tff(c_1146, plain, (![A_181, C_182]: (r2_hidden('#skF_6'(A_181, k1_relat_1(A_181), C_182), k11_relat_1(A_181, C_182)) | ~v1_relat_1(A_181) | ~r2_hidden(C_182, k1_relat_1(A_181)))), inference(resolution, [status(thm)], [c_422, c_44])).
% 3.40/1.74  tff(c_1166, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0) | ~v1_relat_1('#skF_8') | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_247, c_1146])).
% 3.40/1.74  tff(c_1171, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_248, c_46, c_1166])).
% 3.40/1.74  tff(c_1173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_258, c_1171])).
% 3.40/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.74  
% 3.40/1.74  Inference rules
% 3.40/1.74  ----------------------
% 3.40/1.74  #Ref     : 0
% 3.40/1.74  #Sup     : 233
% 3.40/1.74  #Fact    : 0
% 3.40/1.74  #Define  : 0
% 3.40/1.74  #Split   : 3
% 3.40/1.74  #Chain   : 0
% 3.40/1.74  #Close   : 0
% 3.40/1.74  
% 3.40/1.74  Ordering : KBO
% 3.40/1.74  
% 3.40/1.74  Simplification rules
% 3.40/1.74  ----------------------
% 3.40/1.74  #Subsume      : 50
% 3.40/1.74  #Demod        : 70
% 3.40/1.74  #Tautology    : 69
% 3.40/1.74  #SimpNegUnit  : 35
% 3.40/1.74  #BackRed      : 1
% 3.40/1.74  
% 3.40/1.74  #Partial instantiations: 0
% 3.40/1.74  #Strategies tried      : 1
% 3.40/1.74  
% 3.40/1.74  Timing (in seconds)
% 3.40/1.74  ----------------------
% 3.40/1.74  Preprocessing        : 0.51
% 3.40/1.74  Parsing              : 0.27
% 3.40/1.74  CNF conversion       : 0.04
% 3.40/1.74  Main loop            : 0.43
% 3.40/1.74  Inferencing          : 0.17
% 3.40/1.74  Reduction            : 0.11
% 3.40/1.74  Demodulation         : 0.07
% 3.40/1.74  BG Simplification    : 0.03
% 3.40/1.74  Subsumption          : 0.09
% 3.40/1.74  Abstraction          : 0.03
% 3.40/1.74  MUC search           : 0.00
% 3.40/1.74  Cooper               : 0.00
% 3.40/1.74  Total                : 0.97
% 3.40/1.74  Index Insertion      : 0.00
% 3.40/1.74  Index Deletion       : 0.00
% 3.40/1.74  Index Matching       : 0.00
% 3.40/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
