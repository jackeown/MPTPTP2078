%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:26 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   47 (  95 expanded)
%              Number of leaves         :   18 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 205 expanded)
%              Number of equality atoms :   51 ( 125 expanded)
%              Maximal formula depth    :    7 (   4 average)
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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_49,negated_conjecture,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [C_13,A_9] :
      ( r2_hidden(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_70,plain,(
    ! [A_28,B_29] :
      ( '#skF_1'(A_28,B_29) = A_28
      | r2_hidden('#skF_2'(A_28,B_29),B_29)
      | k1_tarski(A_28) = B_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_147,plain,(
    ! [A_45,A_46] :
      ( r1_tarski('#skF_2'(A_45,k1_zfmisc_1(A_46)),A_46)
      | '#skF_1'(A_45,k1_zfmisc_1(A_46)) = A_45
      | k1_zfmisc_1(A_46) = k1_tarski(A_45) ) ),
    inference(resolution,[status(thm)],[c_70,c_20])).

tff(c_4,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_154,plain,(
    ! [A_47] :
      ( '#skF_2'(A_47,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
      | '#skF_1'(A_47,k1_zfmisc_1(k1_xboole_0)) = A_47
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_47) ) ),
    inference(resolution,[status(thm)],[c_147,c_4])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( '#skF_1'(A_3,B_4) = A_3
      | '#skF_2'(A_3,B_4) != A_3
      | k1_tarski(A_3) = B_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_168,plain,(
    ! [A_47] :
      ( '#skF_1'(A_47,k1_zfmisc_1(k1_xboole_0)) = A_47
      | k1_xboole_0 != A_47
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_47)
      | '#skF_1'(A_47,k1_zfmisc_1(k1_xboole_0)) = A_47
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_12])).

tff(c_306,plain,(
    ! [A_68] :
      ( k1_xboole_0 != A_68
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_68)
      | '#skF_1'(A_68,k1_zfmisc_1(k1_xboole_0)) = A_68 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_168])).

tff(c_112,plain,(
    ! [A_39,B_40] :
      ( ~ r2_hidden('#skF_1'(A_39,B_40),B_40)
      | r2_hidden('#skF_2'(A_39,B_40),B_40)
      | k1_tarski(A_39) = B_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_255,plain,(
    ! [A_62,A_63] :
      ( r1_tarski('#skF_2'(A_62,k1_zfmisc_1(A_63)),A_63)
      | ~ r2_hidden('#skF_1'(A_62,k1_zfmisc_1(A_63)),k1_zfmisc_1(A_63))
      | k1_zfmisc_1(A_63) = k1_tarski(A_62) ) ),
    inference(resolution,[status(thm)],[c_112,c_20])).

tff(c_261,plain,(
    ! [A_64,A_65] :
      ( r1_tarski('#skF_2'(A_64,k1_zfmisc_1(A_65)),A_65)
      | k1_zfmisc_1(A_65) = k1_tarski(A_64)
      | ~ r1_tarski('#skF_1'(A_64,k1_zfmisc_1(A_65)),A_65) ) ),
    inference(resolution,[status(thm)],[c_22,c_255])).

tff(c_269,plain,(
    ! [A_64] :
      ( '#skF_2'(A_64,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_64)
      | ~ r1_tarski('#skF_1'(A_64,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_261,c_4])).

tff(c_312,plain,(
    ! [A_68] :
      ( '#skF_2'(A_68,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_68)
      | ~ r1_tarski(A_68,k1_xboole_0)
      | k1_xboole_0 != A_68
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_269])).

tff(c_16,plain,(
    ! [A_3,B_4] :
      ( '#skF_1'(A_3,B_4) = A_3
      | r2_hidden('#skF_2'(A_3,B_4),B_4)
      | k1_tarski(A_3) = B_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_166,plain,(
    ! [A_47] :
      ( '#skF_1'(A_47,k1_zfmisc_1(k1_xboole_0)) = A_47
      | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_47)
      | '#skF_1'(A_47,k1_zfmisc_1(k1_xboole_0)) = A_47
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_16])).

tff(c_327,plain,(
    r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | '#skF_2'(A_3,B_4) != A_3
      | k1_tarski(A_3) = B_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_376,plain,(
    ! [A_71] :
      ( ~ r2_hidden(A_71,k1_zfmisc_1(k1_xboole_0))
      | '#skF_2'(A_71,k1_zfmisc_1(k1_xboole_0)) != A_71
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_71)
      | k1_xboole_0 != A_71
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_10])).

tff(c_379,plain,
    ( '#skF_2'(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_327,c_376])).

tff(c_402,plain,(
    '#skF_2'(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_379])).

tff(c_410,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_402])).

tff(c_416,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_410])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_416])).

tff(c_420,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_423,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_420])).

tff(c_427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_423])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:00:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.33  
% 2.09/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.33  %$ r2_hidden > r1_tarski > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1 > #skF_4
% 2.09/1.33  
% 2.09/1.33  %Foreground sorts:
% 2.09/1.33  
% 2.09/1.33  
% 2.09/1.33  %Background operators:
% 2.09/1.33  
% 2.09/1.33  
% 2.09/1.33  %Foreground operators:
% 2.09/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.09/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.09/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.09/1.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.09/1.33  
% 2.44/1.34  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.44/1.34  tff(f_47, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.44/1.34  tff(f_49, negated_conjecture, ~(k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.44/1.34  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.44/1.34  tff(f_31, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.44/1.34  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.44/1.34  tff(c_22, plain, (![C_13, A_9]: (r2_hidden(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.44/1.34  tff(c_32, plain, (k1_zfmisc_1(k1_xboole_0)!=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.44/1.34  tff(c_70, plain, (![A_28, B_29]: ('#skF_1'(A_28, B_29)=A_28 | r2_hidden('#skF_2'(A_28, B_29), B_29) | k1_tarski(A_28)=B_29)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.44/1.34  tff(c_20, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.44/1.34  tff(c_147, plain, (![A_45, A_46]: (r1_tarski('#skF_2'(A_45, k1_zfmisc_1(A_46)), A_46) | '#skF_1'(A_45, k1_zfmisc_1(A_46))=A_45 | k1_zfmisc_1(A_46)=k1_tarski(A_45))), inference(resolution, [status(thm)], [c_70, c_20])).
% 2.44/1.34  tff(c_4, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.34  tff(c_154, plain, (![A_47]: ('#skF_2'(A_47, k1_zfmisc_1(k1_xboole_0))=k1_xboole_0 | '#skF_1'(A_47, k1_zfmisc_1(k1_xboole_0))=A_47 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_47))), inference(resolution, [status(thm)], [c_147, c_4])).
% 2.44/1.34  tff(c_12, plain, (![A_3, B_4]: ('#skF_1'(A_3, B_4)=A_3 | '#skF_2'(A_3, B_4)!=A_3 | k1_tarski(A_3)=B_4)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.44/1.34  tff(c_168, plain, (![A_47]: ('#skF_1'(A_47, k1_zfmisc_1(k1_xboole_0))=A_47 | k1_xboole_0!=A_47 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_47) | '#skF_1'(A_47, k1_zfmisc_1(k1_xboole_0))=A_47 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_47))), inference(superposition, [status(thm), theory('equality')], [c_154, c_12])).
% 2.44/1.34  tff(c_306, plain, (![A_68]: (k1_xboole_0!=A_68 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_68) | '#skF_1'(A_68, k1_zfmisc_1(k1_xboole_0))=A_68)), inference(factorization, [status(thm), theory('equality')], [c_168])).
% 2.44/1.34  tff(c_112, plain, (![A_39, B_40]: (~r2_hidden('#skF_1'(A_39, B_40), B_40) | r2_hidden('#skF_2'(A_39, B_40), B_40) | k1_tarski(A_39)=B_40)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.44/1.34  tff(c_255, plain, (![A_62, A_63]: (r1_tarski('#skF_2'(A_62, k1_zfmisc_1(A_63)), A_63) | ~r2_hidden('#skF_1'(A_62, k1_zfmisc_1(A_63)), k1_zfmisc_1(A_63)) | k1_zfmisc_1(A_63)=k1_tarski(A_62))), inference(resolution, [status(thm)], [c_112, c_20])).
% 2.44/1.34  tff(c_261, plain, (![A_64, A_65]: (r1_tarski('#skF_2'(A_64, k1_zfmisc_1(A_65)), A_65) | k1_zfmisc_1(A_65)=k1_tarski(A_64) | ~r1_tarski('#skF_1'(A_64, k1_zfmisc_1(A_65)), A_65))), inference(resolution, [status(thm)], [c_22, c_255])).
% 2.44/1.34  tff(c_269, plain, (![A_64]: ('#skF_2'(A_64, k1_zfmisc_1(k1_xboole_0))=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_64) | ~r1_tarski('#skF_1'(A_64, k1_zfmisc_1(k1_xboole_0)), k1_xboole_0))), inference(resolution, [status(thm)], [c_261, c_4])).
% 2.44/1.34  tff(c_312, plain, (![A_68]: ('#skF_2'(A_68, k1_zfmisc_1(k1_xboole_0))=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_68) | ~r1_tarski(A_68, k1_xboole_0) | k1_xboole_0!=A_68 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_68))), inference(superposition, [status(thm), theory('equality')], [c_306, c_269])).
% 2.44/1.34  tff(c_16, plain, (![A_3, B_4]: ('#skF_1'(A_3, B_4)=A_3 | r2_hidden('#skF_2'(A_3, B_4), B_4) | k1_tarski(A_3)=B_4)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.44/1.34  tff(c_166, plain, (![A_47]: ('#skF_1'(A_47, k1_zfmisc_1(k1_xboole_0))=A_47 | r2_hidden(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_47) | '#skF_1'(A_47, k1_zfmisc_1(k1_xboole_0))=A_47 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_47))), inference(superposition, [status(thm), theory('equality')], [c_154, c_16])).
% 2.44/1.34  tff(c_327, plain, (r2_hidden(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_166])).
% 2.44/1.34  tff(c_10, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | '#skF_2'(A_3, B_4)!=A_3 | k1_tarski(A_3)=B_4)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.44/1.34  tff(c_376, plain, (![A_71]: (~r2_hidden(A_71, k1_zfmisc_1(k1_xboole_0)) | '#skF_2'(A_71, k1_zfmisc_1(k1_xboole_0))!=A_71 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_71) | k1_xboole_0!=A_71 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_71))), inference(superposition, [status(thm), theory('equality')], [c_306, c_10])).
% 2.44/1.34  tff(c_379, plain, ('#skF_2'(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))!=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(resolution, [status(thm)], [c_327, c_376])).
% 2.44/1.34  tff(c_402, plain, ('#skF_2'(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_379])).
% 2.44/1.34  tff(c_410, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_312, c_402])).
% 2.44/1.34  tff(c_416, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_410])).
% 2.44/1.34  tff(c_418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_416])).
% 2.44/1.34  tff(c_420, plain, (~r2_hidden(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_166])).
% 2.44/1.34  tff(c_423, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_420])).
% 2.44/1.34  tff(c_427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_423])).
% 2.44/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.34  
% 2.44/1.34  Inference rules
% 2.44/1.34  ----------------------
% 2.44/1.34  #Ref     : 0
% 2.44/1.34  #Sup     : 71
% 2.44/1.34  #Fact    : 2
% 2.44/1.34  #Define  : 0
% 2.44/1.34  #Split   : 1
% 2.44/1.34  #Chain   : 0
% 2.44/1.34  #Close   : 0
% 2.44/1.34  
% 2.44/1.34  Ordering : KBO
% 2.44/1.34  
% 2.44/1.34  Simplification rules
% 2.44/1.34  ----------------------
% 2.44/1.34  #Subsume      : 10
% 2.44/1.34  #Demod        : 13
% 2.44/1.34  #Tautology    : 29
% 2.44/1.34  #SimpNegUnit  : 2
% 2.44/1.34  #BackRed      : 0
% 2.44/1.34  
% 2.44/1.34  #Partial instantiations: 0
% 2.44/1.34  #Strategies tried      : 1
% 2.44/1.34  
% 2.44/1.34  Timing (in seconds)
% 2.44/1.34  ----------------------
% 2.44/1.34  Preprocessing        : 0.27
% 2.44/1.34  Parsing              : 0.14
% 2.44/1.34  CNF conversion       : 0.02
% 2.44/1.34  Main loop            : 0.27
% 2.44/1.34  Inferencing          : 0.12
% 2.44/1.34  Reduction            : 0.06
% 2.44/1.34  Demodulation         : 0.04
% 2.44/1.34  BG Simplification    : 0.02
% 2.44/1.34  Subsumption          : 0.06
% 2.44/1.34  Abstraction          : 0.02
% 2.44/1.34  MUC search           : 0.00
% 2.44/1.34  Cooper               : 0.00
% 2.44/1.34  Total                : 0.57
% 2.44/1.34  Index Insertion      : 0.00
% 2.44/1.34  Index Deletion       : 0.00
% 2.44/1.34  Index Matching       : 0.00
% 2.44/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
