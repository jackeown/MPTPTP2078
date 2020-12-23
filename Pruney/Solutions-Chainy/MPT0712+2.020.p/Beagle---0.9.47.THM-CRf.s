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
% DateTime   : Thu Dec  3 10:05:33 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   56 (  74 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 119 expanded)
%              Number of equality atoms :   24 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_65,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    ! [A_24] : k2_relat_1(k6_relat_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_51,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_42])).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_146,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_xboole_0(k2_tarski(A_39,C_40),B_41)
      | r2_hidden(C_40,B_41)
      | r2_hidden(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_155,plain,(
    ! [A_42,B_43] :
      ( r1_xboole_0(k1_tarski(A_42),B_43)
      | r2_hidden(A_42,B_43)
      | r2_hidden(A_42,B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_146])).

tff(c_20,plain,(
    ! [A_15,B_17] :
      ( k7_relat_1(A_15,B_17) = k1_xboole_0
      | ~ r1_xboole_0(B_17,k1_relat_1(A_15))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_160,plain,(
    ! [A_15,A_42] :
      ( k7_relat_1(A_15,k1_tarski(A_42)) = k1_xboole_0
      | ~ v1_relat_1(A_15)
      | r2_hidden(A_42,k1_relat_1(A_15)) ) ),
    inference(resolution,[status(thm)],[c_155,c_20])).

tff(c_189,plain,(
    ! [C_50,A_51,B_52] :
      ( k2_tarski(k1_funct_1(C_50,A_51),k1_funct_1(C_50,B_52)) = k9_relat_1(C_50,k2_tarski(A_51,B_52))
      | ~ r2_hidden(B_52,k1_relat_1(C_50))
      | ~ r2_hidden(A_51,k1_relat_1(C_50))
      | ~ v1_funct_1(C_50)
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_206,plain,(
    ! [C_50,A_51] :
      ( k9_relat_1(C_50,k2_tarski(A_51,A_51)) = k1_tarski(k1_funct_1(C_50,A_51))
      | ~ r2_hidden(A_51,k1_relat_1(C_50))
      | ~ r2_hidden(A_51,k1_relat_1(C_50))
      | ~ v1_funct_1(C_50)
      | ~ v1_relat_1(C_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_189])).

tff(c_391,plain,(
    ! [C_72,A_73] :
      ( k9_relat_1(C_72,k1_tarski(A_73)) = k1_tarski(k1_funct_1(C_72,A_73))
      | ~ r2_hidden(A_73,k1_relat_1(C_72))
      | ~ r2_hidden(A_73,k1_relat_1(C_72))
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_206])).

tff(c_460,plain,(
    ! [A_80,A_81] :
      ( k9_relat_1(A_80,k1_tarski(A_81)) = k1_tarski(k1_funct_1(A_80,A_81))
      | ~ r2_hidden(A_81,k1_relat_1(A_80))
      | ~ v1_funct_1(A_80)
      | k7_relat_1(A_80,k1_tarski(A_81)) = k1_xboole_0
      | ~ v1_relat_1(A_80) ) ),
    inference(resolution,[status(thm)],[c_160,c_391])).

tff(c_491,plain,(
    ! [A_82,A_83] :
      ( k9_relat_1(A_82,k1_tarski(A_83)) = k1_tarski(k1_funct_1(A_82,A_83))
      | ~ v1_funct_1(A_82)
      | k7_relat_1(A_82,k1_tarski(A_83)) = k1_xboole_0
      | ~ v1_relat_1(A_82) ) ),
    inference(resolution,[status(thm)],[c_160,c_460])).

tff(c_115,plain,(
    ! [B_32,A_33] :
      ( k2_relat_1(k7_relat_1(B_32,A_33)) = k9_relat_1(B_32,A_33)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_121,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_30])).

tff(c_127,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_121])).

tff(c_504,plain,
    ( ~ r1_tarski(k1_tarski(k1_funct_1('#skF_2','#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_127])).

tff(c_513,plain,(
    k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_6,c_504])).

tff(c_515,plain,(
    ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_30])).

tff(c_518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_51,c_515])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.38  
% 2.63/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.63/1.38  
% 2.63/1.38  %Foreground sorts:
% 2.63/1.38  
% 2.63/1.38  
% 2.63/1.38  %Background operators:
% 2.63/1.38  
% 2.63/1.38  
% 2.63/1.38  %Foreground operators:
% 2.63/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.63/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.63/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.63/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.63/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.63/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.63/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.63/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.63/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.63/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.63/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.63/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.63/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.63/1.38  
% 2.97/1.39  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.97/1.39  tff(f_65, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.97/1.39  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.97/1.39  tff(f_82, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_funct_1)).
% 2.97/1.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.97/1.39  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.97/1.39  tff(f_49, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 2.97/1.39  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 2.97/1.39  tff(f_75, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_funct_1)).
% 2.97/1.39  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.97/1.39  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.97/1.39  tff(c_26, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.97/1.39  tff(c_42, plain, (![A_24]: (k2_relat_1(k6_relat_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.97/1.39  tff(c_51, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_26, c_42])).
% 2.97/1.39  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.97/1.39  tff(c_32, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.97/1.39  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.39  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.97/1.39  tff(c_146, plain, (![A_39, C_40, B_41]: (r1_xboole_0(k2_tarski(A_39, C_40), B_41) | r2_hidden(C_40, B_41) | r2_hidden(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.97/1.39  tff(c_155, plain, (![A_42, B_43]: (r1_xboole_0(k1_tarski(A_42), B_43) | r2_hidden(A_42, B_43) | r2_hidden(A_42, B_43))), inference(superposition, [status(thm), theory('equality')], [c_10, c_146])).
% 2.97/1.39  tff(c_20, plain, (![A_15, B_17]: (k7_relat_1(A_15, B_17)=k1_xboole_0 | ~r1_xboole_0(B_17, k1_relat_1(A_15)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.97/1.39  tff(c_160, plain, (![A_15, A_42]: (k7_relat_1(A_15, k1_tarski(A_42))=k1_xboole_0 | ~v1_relat_1(A_15) | r2_hidden(A_42, k1_relat_1(A_15)))), inference(resolution, [status(thm)], [c_155, c_20])).
% 2.97/1.39  tff(c_189, plain, (![C_50, A_51, B_52]: (k2_tarski(k1_funct_1(C_50, A_51), k1_funct_1(C_50, B_52))=k9_relat_1(C_50, k2_tarski(A_51, B_52)) | ~r2_hidden(B_52, k1_relat_1(C_50)) | ~r2_hidden(A_51, k1_relat_1(C_50)) | ~v1_funct_1(C_50) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.97/1.39  tff(c_206, plain, (![C_50, A_51]: (k9_relat_1(C_50, k2_tarski(A_51, A_51))=k1_tarski(k1_funct_1(C_50, A_51)) | ~r2_hidden(A_51, k1_relat_1(C_50)) | ~r2_hidden(A_51, k1_relat_1(C_50)) | ~v1_funct_1(C_50) | ~v1_relat_1(C_50))), inference(superposition, [status(thm), theory('equality')], [c_10, c_189])).
% 2.97/1.39  tff(c_391, plain, (![C_72, A_73]: (k9_relat_1(C_72, k1_tarski(A_73))=k1_tarski(k1_funct_1(C_72, A_73)) | ~r2_hidden(A_73, k1_relat_1(C_72)) | ~r2_hidden(A_73, k1_relat_1(C_72)) | ~v1_funct_1(C_72) | ~v1_relat_1(C_72))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_206])).
% 2.97/1.39  tff(c_460, plain, (![A_80, A_81]: (k9_relat_1(A_80, k1_tarski(A_81))=k1_tarski(k1_funct_1(A_80, A_81)) | ~r2_hidden(A_81, k1_relat_1(A_80)) | ~v1_funct_1(A_80) | k7_relat_1(A_80, k1_tarski(A_81))=k1_xboole_0 | ~v1_relat_1(A_80))), inference(resolution, [status(thm)], [c_160, c_391])).
% 2.97/1.39  tff(c_491, plain, (![A_82, A_83]: (k9_relat_1(A_82, k1_tarski(A_83))=k1_tarski(k1_funct_1(A_82, A_83)) | ~v1_funct_1(A_82) | k7_relat_1(A_82, k1_tarski(A_83))=k1_xboole_0 | ~v1_relat_1(A_82))), inference(resolution, [status(thm)], [c_160, c_460])).
% 2.97/1.39  tff(c_115, plain, (![B_32, A_33]: (k2_relat_1(k7_relat_1(B_32, A_33))=k9_relat_1(B_32, A_33) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.97/1.39  tff(c_30, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.97/1.39  tff(c_121, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_115, c_30])).
% 2.97/1.39  tff(c_127, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_121])).
% 2.97/1.39  tff(c_504, plain, (~r1_tarski(k1_tarski(k1_funct_1('#skF_2', '#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_2') | k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_491, c_127])).
% 2.97/1.39  tff(c_513, plain, (k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_6, c_504])).
% 2.97/1.39  tff(c_515, plain, (~r1_tarski(k2_relat_1(k1_xboole_0), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_513, c_30])).
% 2.97/1.39  tff(c_518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_51, c_515])).
% 2.97/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.39  
% 2.97/1.39  Inference rules
% 2.97/1.39  ----------------------
% 2.97/1.39  #Ref     : 0
% 2.97/1.39  #Sup     : 111
% 2.97/1.39  #Fact    : 4
% 2.97/1.39  #Define  : 0
% 2.97/1.39  #Split   : 1
% 2.97/1.39  #Chain   : 0
% 2.97/1.39  #Close   : 0
% 2.97/1.39  
% 2.97/1.39  Ordering : KBO
% 2.97/1.39  
% 2.97/1.39  Simplification rules
% 2.97/1.39  ----------------------
% 2.97/1.39  #Subsume      : 30
% 2.97/1.39  #Demod        : 48
% 2.97/1.39  #Tautology    : 47
% 2.97/1.39  #SimpNegUnit  : 0
% 2.97/1.39  #BackRed      : 1
% 2.97/1.39  
% 2.97/1.39  #Partial instantiations: 0
% 2.97/1.39  #Strategies tried      : 1
% 2.97/1.39  
% 2.97/1.39  Timing (in seconds)
% 2.97/1.39  ----------------------
% 2.97/1.40  Preprocessing        : 0.32
% 2.97/1.40  Parsing              : 0.17
% 2.97/1.40  CNF conversion       : 0.02
% 2.97/1.40  Main loop            : 0.31
% 2.97/1.40  Inferencing          : 0.12
% 2.97/1.40  Reduction            : 0.10
% 2.97/1.40  Demodulation         : 0.07
% 2.97/1.40  BG Simplification    : 0.02
% 2.97/1.40  Subsumption          : 0.06
% 2.97/1.40  Abstraction          : 0.02
% 2.97/1.40  MUC search           : 0.00
% 2.97/1.40  Cooper               : 0.00
% 2.97/1.40  Total                : 0.66
% 2.97/1.40  Index Insertion      : 0.00
% 2.97/1.40  Index Deletion       : 0.00
% 2.97/1.40  Index Matching       : 0.00
% 2.97/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
