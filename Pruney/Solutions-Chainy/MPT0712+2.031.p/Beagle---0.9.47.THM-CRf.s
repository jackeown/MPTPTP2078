%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:35 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   52 (  67 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 107 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_67,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ! [C_23,B_24] : r1_tarski(k1_tarski(C_23),k2_tarski(B_24,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_59,plain,(
    ! [A_2] : r1_tarski(k1_tarski(A_2),k1_tarski(A_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_56])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(k1_tarski(A_8),B_9)
      | r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_108,plain,(
    ! [A_39,B_40] :
      ( k7_relat_1(A_39,B_40) = k1_xboole_0
      | ~ r1_xboole_0(B_40,k1_relat_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_116,plain,(
    ! [A_39,A_8] :
      ( k7_relat_1(A_39,k1_tarski(A_8)) = k1_xboole_0
      | ~ v1_relat_1(A_39)
      | r2_hidden(A_8,k1_relat_1(A_39)) ) ),
    inference(resolution,[status(thm)],[c_10,c_108])).

tff(c_160,plain,(
    ! [C_48,A_49,B_50] :
      ( k2_tarski(k1_funct_1(C_48,A_49),k1_funct_1(C_48,B_50)) = k9_relat_1(C_48,k2_tarski(A_49,B_50))
      | ~ r2_hidden(B_50,k1_relat_1(C_48))
      | ~ r2_hidden(A_49,k1_relat_1(C_48))
      | ~ v1_funct_1(C_48)
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_182,plain,(
    ! [C_48,B_50] :
      ( k9_relat_1(C_48,k2_tarski(B_50,B_50)) = k1_tarski(k1_funct_1(C_48,B_50))
      | ~ r2_hidden(B_50,k1_relat_1(C_48))
      | ~ r2_hidden(B_50,k1_relat_1(C_48))
      | ~ v1_funct_1(C_48)
      | ~ v1_relat_1(C_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_4])).

tff(c_194,plain,(
    ! [C_51,B_52] :
      ( k9_relat_1(C_51,k1_tarski(B_52)) = k1_tarski(k1_funct_1(C_51,B_52))
      | ~ r2_hidden(B_52,k1_relat_1(C_51))
      | ~ r2_hidden(B_52,k1_relat_1(C_51))
      | ~ v1_funct_1(C_51)
      | ~ v1_relat_1(C_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_182])).

tff(c_208,plain,(
    ! [A_56,A_57] :
      ( k9_relat_1(A_56,k1_tarski(A_57)) = k1_tarski(k1_funct_1(A_56,A_57))
      | ~ r2_hidden(A_57,k1_relat_1(A_56))
      | ~ v1_funct_1(A_56)
      | k7_relat_1(A_56,k1_tarski(A_57)) = k1_xboole_0
      | ~ v1_relat_1(A_56) ) ),
    inference(resolution,[status(thm)],[c_116,c_194])).

tff(c_216,plain,(
    ! [A_58,A_59] :
      ( k9_relat_1(A_58,k1_tarski(A_59)) = k1_tarski(k1_funct_1(A_58,A_59))
      | ~ v1_funct_1(A_58)
      | k7_relat_1(A_58,k1_tarski(A_59)) = k1_xboole_0
      | ~ v1_relat_1(A_58) ) ),
    inference(resolution,[status(thm)],[c_116,c_208])).

tff(c_94,plain,(
    ! [B_37,A_38] :
      ( k2_relat_1(k7_relat_1(B_37,A_38)) = k9_relat_1(B_37,A_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_100,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_32])).

tff(c_106,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_100])).

tff(c_222,plain,
    ( ~ r1_tarski(k1_tarski(k1_funct_1('#skF_2','#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_106])).

tff(c_228,plain,(
    k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_59,c_222])).

tff(c_230,plain,(
    ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_32])).

tff(c_233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_26,c_230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:28:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.30  
% 2.27/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.30  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.27/1.30  
% 2.27/1.30  %Foreground sorts:
% 2.27/1.30  
% 2.27/1.30  
% 2.27/1.30  %Background operators:
% 2.27/1.30  
% 2.27/1.30  
% 2.27/1.30  %Foreground operators:
% 2.27/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.27/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.27/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.27/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.27/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.27/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.27/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.27/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.30  
% 2.27/1.31  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.27/1.31  tff(f_67, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.27/1.31  tff(f_84, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_1)).
% 2.27/1.31  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.27/1.31  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.27/1.31  tff(f_38, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.27/1.31  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 2.27/1.31  tff(f_77, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_funct_1)).
% 2.27/1.31  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.27/1.31  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.27/1.31  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.27/1.31  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.27/1.31  tff(c_34, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.27/1.31  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.27/1.31  tff(c_56, plain, (![C_23, B_24]: (r1_tarski(k1_tarski(C_23), k2_tarski(B_24, C_23)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.27/1.31  tff(c_59, plain, (![A_2]: (r1_tarski(k1_tarski(A_2), k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_56])).
% 2.27/1.31  tff(c_10, plain, (![A_8, B_9]: (r1_xboole_0(k1_tarski(A_8), B_9) | r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.27/1.31  tff(c_108, plain, (![A_39, B_40]: (k7_relat_1(A_39, B_40)=k1_xboole_0 | ~r1_xboole_0(B_40, k1_relat_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.27/1.31  tff(c_116, plain, (![A_39, A_8]: (k7_relat_1(A_39, k1_tarski(A_8))=k1_xboole_0 | ~v1_relat_1(A_39) | r2_hidden(A_8, k1_relat_1(A_39)))), inference(resolution, [status(thm)], [c_10, c_108])).
% 2.27/1.31  tff(c_160, plain, (![C_48, A_49, B_50]: (k2_tarski(k1_funct_1(C_48, A_49), k1_funct_1(C_48, B_50))=k9_relat_1(C_48, k2_tarski(A_49, B_50)) | ~r2_hidden(B_50, k1_relat_1(C_48)) | ~r2_hidden(A_49, k1_relat_1(C_48)) | ~v1_funct_1(C_48) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.27/1.31  tff(c_182, plain, (![C_48, B_50]: (k9_relat_1(C_48, k2_tarski(B_50, B_50))=k1_tarski(k1_funct_1(C_48, B_50)) | ~r2_hidden(B_50, k1_relat_1(C_48)) | ~r2_hidden(B_50, k1_relat_1(C_48)) | ~v1_funct_1(C_48) | ~v1_relat_1(C_48))), inference(superposition, [status(thm), theory('equality')], [c_160, c_4])).
% 2.27/1.31  tff(c_194, plain, (![C_51, B_52]: (k9_relat_1(C_51, k1_tarski(B_52))=k1_tarski(k1_funct_1(C_51, B_52)) | ~r2_hidden(B_52, k1_relat_1(C_51)) | ~r2_hidden(B_52, k1_relat_1(C_51)) | ~v1_funct_1(C_51) | ~v1_relat_1(C_51))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_182])).
% 2.27/1.31  tff(c_208, plain, (![A_56, A_57]: (k9_relat_1(A_56, k1_tarski(A_57))=k1_tarski(k1_funct_1(A_56, A_57)) | ~r2_hidden(A_57, k1_relat_1(A_56)) | ~v1_funct_1(A_56) | k7_relat_1(A_56, k1_tarski(A_57))=k1_xboole_0 | ~v1_relat_1(A_56))), inference(resolution, [status(thm)], [c_116, c_194])).
% 2.27/1.31  tff(c_216, plain, (![A_58, A_59]: (k9_relat_1(A_58, k1_tarski(A_59))=k1_tarski(k1_funct_1(A_58, A_59)) | ~v1_funct_1(A_58) | k7_relat_1(A_58, k1_tarski(A_59))=k1_xboole_0 | ~v1_relat_1(A_58))), inference(resolution, [status(thm)], [c_116, c_208])).
% 2.27/1.31  tff(c_94, plain, (![B_37, A_38]: (k2_relat_1(k7_relat_1(B_37, A_38))=k9_relat_1(B_37, A_38) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.27/1.31  tff(c_32, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.27/1.31  tff(c_100, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_94, c_32])).
% 2.27/1.31  tff(c_106, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_100])).
% 2.27/1.31  tff(c_222, plain, (~r1_tarski(k1_tarski(k1_funct_1('#skF_2', '#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_2') | k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_216, c_106])).
% 2.27/1.31  tff(c_228, plain, (k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_59, c_222])).
% 2.27/1.31  tff(c_230, plain, (~r1_tarski(k2_relat_1(k1_xboole_0), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_32])).
% 2.27/1.31  tff(c_233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_26, c_230])).
% 2.27/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.31  
% 2.27/1.31  Inference rules
% 2.27/1.31  ----------------------
% 2.27/1.31  #Ref     : 0
% 2.27/1.31  #Sup     : 45
% 2.27/1.31  #Fact    : 0
% 2.27/1.31  #Define  : 0
% 2.27/1.31  #Split   : 1
% 2.27/1.31  #Chain   : 0
% 2.27/1.31  #Close   : 0
% 2.27/1.31  
% 2.27/1.31  Ordering : KBO
% 2.27/1.31  
% 2.27/1.31  Simplification rules
% 2.27/1.31  ----------------------
% 2.27/1.31  #Subsume      : 5
% 2.27/1.31  #Demod        : 17
% 2.27/1.31  #Tautology    : 26
% 2.27/1.31  #SimpNegUnit  : 0
% 2.27/1.31  #BackRed      : 1
% 2.27/1.31  
% 2.27/1.31  #Partial instantiations: 0
% 2.27/1.31  #Strategies tried      : 1
% 2.27/1.31  
% 2.27/1.31  Timing (in seconds)
% 2.27/1.31  ----------------------
% 2.27/1.32  Preprocessing        : 0.34
% 2.27/1.32  Parsing              : 0.18
% 2.27/1.32  CNF conversion       : 0.02
% 2.27/1.32  Main loop            : 0.19
% 2.27/1.32  Inferencing          : 0.07
% 2.27/1.32  Reduction            : 0.06
% 2.27/1.32  Demodulation         : 0.05
% 2.27/1.32  BG Simplification    : 0.01
% 2.27/1.32  Subsumption          : 0.03
% 2.27/1.32  Abstraction          : 0.01
% 2.27/1.32  MUC search           : 0.00
% 2.27/1.32  Cooper               : 0.00
% 2.27/1.32  Total                : 0.56
% 2.27/1.32  Index Insertion      : 0.00
% 2.27/1.32  Index Deletion       : 0.00
% 2.27/1.32  Index Matching       : 0.00
% 2.27/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
