%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:25 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   41 (  65 expanded)
%              Number of leaves         :   18 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :   82 ( 147 expanded)
%              Number of equality atoms :   53 (  90 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_36,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [C_14,A_10] :
      ( r2_hidden(C_14,k1_zfmisc_1(A_10))
      | ~ r1_tarski(C_14,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_76,plain,(
    ! [A_29,B_30] :
      ( '#skF_1'(A_29,B_30) = A_29
      | r2_hidden('#skF_2'(A_29,B_30),B_30)
      | k1_tarski(A_29) = B_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    ! [C_14,A_10] :
      ( r1_tarski(C_14,A_10)
      | ~ r2_hidden(C_14,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_164,plain,(
    ! [A_46,A_47] :
      ( r1_tarski('#skF_2'(A_46,k1_zfmisc_1(A_47)),A_47)
      | '#skF_1'(A_46,k1_zfmisc_1(A_47)) = A_46
      | k1_zfmisc_1(A_47) = k1_tarski(A_46) ) ),
    inference(resolution,[status(thm)],[c_76,c_24])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_174,plain,(
    ! [A_48] :
      ( '#skF_2'(A_48,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
      | '#skF_1'(A_48,k1_zfmisc_1(k1_xboole_0)) = A_48
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_48) ) ),
    inference(resolution,[status(thm)],[c_164,c_8])).

tff(c_16,plain,(
    ! [A_4,B_5] :
      ( '#skF_1'(A_4,B_5) = A_4
      | '#skF_2'(A_4,B_5) != A_4
      | k1_tarski(A_4) = B_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_188,plain,(
    ! [A_48] :
      ( '#skF_1'(A_48,k1_zfmisc_1(k1_xboole_0)) = A_48
      | k1_xboole_0 != A_48
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_48)
      | '#skF_1'(A_48,k1_zfmisc_1(k1_xboole_0)) = A_48
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_16])).

tff(c_368,plain,(
    ! [A_79] :
      ( k1_xboole_0 != A_79
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_79)
      | '#skF_1'(A_79,k1_zfmisc_1(k1_xboole_0)) = A_79 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_188])).

tff(c_130,plain,(
    ! [A_42,B_43] :
      ( ~ r2_hidden('#skF_1'(A_42,B_43),B_43)
      | r2_hidden('#skF_2'(A_42,B_43),B_43)
      | k1_tarski(A_42) = B_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_139,plain,(
    ! [A_42,A_10] :
      ( r1_tarski('#skF_2'(A_42,k1_zfmisc_1(A_10)),A_10)
      | ~ r2_hidden('#skF_1'(A_42,k1_zfmisc_1(A_10)),k1_zfmisc_1(A_10))
      | k1_zfmisc_1(A_10) = k1_tarski(A_42) ) ),
    inference(resolution,[status(thm)],[c_130,c_24])).

tff(c_464,plain,(
    ! [A_86] :
      ( r1_tarski('#skF_2'(A_86,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(A_86,k1_zfmisc_1(k1_xboole_0))
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_86)
      | k1_xboole_0 != A_86
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_139])).

tff(c_481,plain,(
    ! [A_87] :
      ( '#skF_2'(A_87,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
      | ~ r2_hidden(A_87,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != A_87
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_87) ) ),
    inference(resolution,[status(thm)],[c_464,c_8])).

tff(c_508,plain,(
    ! [C_88] :
      ( '#skF_2'(C_88,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
      | k1_xboole_0 != C_88
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(C_88)
      | ~ r1_tarski(C_88,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_481])).

tff(c_14,plain,(
    ! [A_4,B_5] :
      ( ~ r2_hidden('#skF_1'(A_4,B_5),B_5)
      | '#skF_2'(A_4,B_5) != A_4
      | k1_tarski(A_4) = B_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_390,plain,(
    ! [A_80] :
      ( ~ r2_hidden(A_80,k1_zfmisc_1(k1_xboole_0))
      | '#skF_2'(A_80,k1_zfmisc_1(k1_xboole_0)) != A_80
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_80)
      | k1_xboole_0 != A_80
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_14])).

tff(c_415,plain,(
    ! [C_14] :
      ( '#skF_2'(C_14,k1_zfmisc_1(k1_xboole_0)) != C_14
      | k1_xboole_0 != C_14
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(C_14)
      | ~ r1_tarski(C_14,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_390])).

tff(c_553,plain,(
    ! [C_91] :
      ( k1_xboole_0 != C_91
      | k1_xboole_0 != C_91
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(C_91)
      | ~ r1_tarski(C_91,k1_xboole_0)
      | k1_xboole_0 != C_91
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(C_91)
      | ~ r1_tarski(C_91,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_415])).

tff(c_578,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_553])).

tff(c_588,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_578])).

tff(c_590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_588])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.37  
% 2.71/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.37  %$ r2_hidden > r1_tarski > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1 > #skF_4
% 2.71/1.37  
% 2.71/1.37  %Foreground sorts:
% 2.71/1.37  
% 2.71/1.37  
% 2.71/1.37  %Background operators:
% 2.71/1.37  
% 2.71/1.37  
% 2.71/1.37  %Foreground operators:
% 2.71/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.71/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.71/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.71/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.71/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.71/1.37  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.71/1.37  
% 2.71/1.38  tff(f_53, negated_conjecture, ~(k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.71/1.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.71/1.38  tff(f_51, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.71/1.38  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.71/1.38  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.71/1.38  tff(c_36, plain, (k1_zfmisc_1(k1_xboole_0)!=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.71/1.38  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.71/1.38  tff(c_26, plain, (![C_14, A_10]: (r2_hidden(C_14, k1_zfmisc_1(A_10)) | ~r1_tarski(C_14, A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.71/1.38  tff(c_76, plain, (![A_29, B_30]: ('#skF_1'(A_29, B_30)=A_29 | r2_hidden('#skF_2'(A_29, B_30), B_30) | k1_tarski(A_29)=B_30)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.71/1.38  tff(c_24, plain, (![C_14, A_10]: (r1_tarski(C_14, A_10) | ~r2_hidden(C_14, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.71/1.38  tff(c_164, plain, (![A_46, A_47]: (r1_tarski('#skF_2'(A_46, k1_zfmisc_1(A_47)), A_47) | '#skF_1'(A_46, k1_zfmisc_1(A_47))=A_46 | k1_zfmisc_1(A_47)=k1_tarski(A_46))), inference(resolution, [status(thm)], [c_76, c_24])).
% 2.71/1.38  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.71/1.38  tff(c_174, plain, (![A_48]: ('#skF_2'(A_48, k1_zfmisc_1(k1_xboole_0))=k1_xboole_0 | '#skF_1'(A_48, k1_zfmisc_1(k1_xboole_0))=A_48 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_48))), inference(resolution, [status(thm)], [c_164, c_8])).
% 2.71/1.38  tff(c_16, plain, (![A_4, B_5]: ('#skF_1'(A_4, B_5)=A_4 | '#skF_2'(A_4, B_5)!=A_4 | k1_tarski(A_4)=B_5)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.71/1.38  tff(c_188, plain, (![A_48]: ('#skF_1'(A_48, k1_zfmisc_1(k1_xboole_0))=A_48 | k1_xboole_0!=A_48 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_48) | '#skF_1'(A_48, k1_zfmisc_1(k1_xboole_0))=A_48 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_48))), inference(superposition, [status(thm), theory('equality')], [c_174, c_16])).
% 2.71/1.38  tff(c_368, plain, (![A_79]: (k1_xboole_0!=A_79 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_79) | '#skF_1'(A_79, k1_zfmisc_1(k1_xboole_0))=A_79)), inference(factorization, [status(thm), theory('equality')], [c_188])).
% 2.71/1.38  tff(c_130, plain, (![A_42, B_43]: (~r2_hidden('#skF_1'(A_42, B_43), B_43) | r2_hidden('#skF_2'(A_42, B_43), B_43) | k1_tarski(A_42)=B_43)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.71/1.38  tff(c_139, plain, (![A_42, A_10]: (r1_tarski('#skF_2'(A_42, k1_zfmisc_1(A_10)), A_10) | ~r2_hidden('#skF_1'(A_42, k1_zfmisc_1(A_10)), k1_zfmisc_1(A_10)) | k1_zfmisc_1(A_10)=k1_tarski(A_42))), inference(resolution, [status(thm)], [c_130, c_24])).
% 2.71/1.38  tff(c_464, plain, (![A_86]: (r1_tarski('#skF_2'(A_86, k1_zfmisc_1(k1_xboole_0)), k1_xboole_0) | ~r2_hidden(A_86, k1_zfmisc_1(k1_xboole_0)) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_86) | k1_xboole_0!=A_86 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_86))), inference(superposition, [status(thm), theory('equality')], [c_368, c_139])).
% 2.71/1.38  tff(c_481, plain, (![A_87]: ('#skF_2'(A_87, k1_zfmisc_1(k1_xboole_0))=k1_xboole_0 | ~r2_hidden(A_87, k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0!=A_87 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_87))), inference(resolution, [status(thm)], [c_464, c_8])).
% 2.71/1.38  tff(c_508, plain, (![C_88]: ('#skF_2'(C_88, k1_zfmisc_1(k1_xboole_0))=k1_xboole_0 | k1_xboole_0!=C_88 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(C_88) | ~r1_tarski(C_88, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_481])).
% 2.71/1.38  tff(c_14, plain, (![A_4, B_5]: (~r2_hidden('#skF_1'(A_4, B_5), B_5) | '#skF_2'(A_4, B_5)!=A_4 | k1_tarski(A_4)=B_5)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.71/1.38  tff(c_390, plain, (![A_80]: (~r2_hidden(A_80, k1_zfmisc_1(k1_xboole_0)) | '#skF_2'(A_80, k1_zfmisc_1(k1_xboole_0))!=A_80 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_80) | k1_xboole_0!=A_80 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_80))), inference(superposition, [status(thm), theory('equality')], [c_368, c_14])).
% 2.71/1.38  tff(c_415, plain, (![C_14]: ('#skF_2'(C_14, k1_zfmisc_1(k1_xboole_0))!=C_14 | k1_xboole_0!=C_14 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(C_14) | ~r1_tarski(C_14, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_390])).
% 2.71/1.38  tff(c_553, plain, (![C_91]: (k1_xboole_0!=C_91 | k1_xboole_0!=C_91 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(C_91) | ~r1_tarski(C_91, k1_xboole_0) | k1_xboole_0!=C_91 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(C_91) | ~r1_tarski(C_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_508, c_415])).
% 2.71/1.38  tff(c_578, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_553])).
% 2.71/1.38  tff(c_588, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_578])).
% 2.71/1.38  tff(c_590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_588])).
% 2.71/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.38  
% 2.71/1.38  Inference rules
% 2.71/1.38  ----------------------
% 2.71/1.38  #Ref     : 0
% 2.71/1.38  #Sup     : 109
% 2.71/1.38  #Fact    : 2
% 2.71/1.38  #Define  : 0
% 2.71/1.38  #Split   : 0
% 2.71/1.38  #Chain   : 0
% 2.71/1.38  #Close   : 0
% 2.71/1.38  
% 2.71/1.38  Ordering : KBO
% 2.71/1.38  
% 2.71/1.38  Simplification rules
% 2.71/1.38  ----------------------
% 2.71/1.38  #Subsume      : 23
% 2.71/1.38  #Demod        : 21
% 2.71/1.38  #Tautology    : 35
% 2.71/1.38  #SimpNegUnit  : 1
% 2.71/1.38  #BackRed      : 0
% 2.71/1.38  
% 2.71/1.38  #Partial instantiations: 0
% 2.71/1.38  #Strategies tried      : 1
% 2.71/1.38  
% 2.71/1.38  Timing (in seconds)
% 2.71/1.38  ----------------------
% 2.71/1.38  Preprocessing        : 0.29
% 2.71/1.38  Parsing              : 0.15
% 2.71/1.38  CNF conversion       : 0.02
% 2.71/1.38  Main loop            : 0.34
% 2.71/1.38  Inferencing          : 0.14
% 2.71/1.38  Reduction            : 0.08
% 2.71/1.38  Demodulation         : 0.05
% 2.71/1.38  BG Simplification    : 0.02
% 2.71/1.38  Subsumption          : 0.08
% 2.71/1.38  Abstraction          : 0.02
% 2.71/1.38  MUC search           : 0.00
% 2.71/1.38  Cooper               : 0.00
% 2.71/1.38  Total                : 0.65
% 2.71/1.38  Index Insertion      : 0.00
% 2.71/1.38  Index Deletion       : 0.00
% 2.71/1.38  Index Matching       : 0.00
% 2.71/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
