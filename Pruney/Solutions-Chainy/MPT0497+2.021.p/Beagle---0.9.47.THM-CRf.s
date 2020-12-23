%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:42 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 120 expanded)
%              Number of leaves         :   24 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 ( 189 expanded)
%              Number of equality atoms :   29 (  64 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_36,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_58,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_109,plain,(
    ! [B_30,A_31] :
      ( k3_xboole_0(k1_relat_1(B_30),A_31) = k1_relat_1(k7_relat_1(B_30,A_31))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_96,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_32])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_100,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_115,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_100])).

tff(c_135,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_115])).

tff(c_18,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(k1_relat_1(A_10))
      | ~ v1_relat_1(A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_145,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | v1_xboole_0(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_18])).

tff(c_149,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | v1_xboole_0(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_145])).

tff(c_209,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_212,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_209])).

tff(c_216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_212])).

tff(c_217,plain,(
    v1_xboole_0(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_223,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_217,c_8])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_223])).

tff(c_229,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_287,plain,(
    ! [B_42,A_43] :
      ( k3_xboole_0(k1_relat_1(B_42),A_43) = k1_relat_1(k7_relat_1(B_42,A_43))
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_278,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_228,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_286,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_278,c_228])).

tff(c_293,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_286])).

tff(c_310,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_229,c_293])).

tff(c_10,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_48,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k3_xboole_0(A_20,B_21))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_51,plain,(
    ! [A_4] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_48])).

tff(c_52,plain,(
    ! [A_4] : ~ v1_relat_1(A_4) ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_56,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_24])).

tff(c_57,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_239,plain,(
    ! [B_34,A_35] :
      ( r1_tarski(k7_relat_1(B_34,A_35),B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_243,plain,(
    ! [A_35] :
      ( k7_relat_1(k1_xboole_0,A_35) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_239,c_12])).

tff(c_249,plain,(
    ! [A_35] : k7_relat_1(k1_xboole_0,A_35) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_243])).

tff(c_312,plain,(
    ! [B_44] :
      ( k1_relat_1(k7_relat_1(B_44,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_287])).

tff(c_328,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_312])).

tff(c_334,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_328])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_310,c_334])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:44:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.23  
% 2.01/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.23  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.01/1.23  
% 2.01/1.23  %Foreground sorts:
% 2.01/1.23  
% 2.01/1.23  
% 2.01/1.23  %Background operators:
% 2.01/1.23  
% 2.01/1.23  
% 2.01/1.23  %Foreground operators:
% 2.01/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.01/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.01/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.01/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.01/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.01/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.01/1.23  
% 2.11/1.25  tff(f_71, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.11/1.25  tff(f_44, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.11/1.25  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.11/1.25  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.11/1.25  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.11/1.25  tff(f_56, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.11/1.25  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.11/1.25  tff(f_36, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.11/1.25  tff(f_48, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.11/1.25  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 2.11/1.25  tff(f_40, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.11/1.25  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.11/1.25  tff(c_26, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.11/1.25  tff(c_58, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_26])).
% 2.11/1.25  tff(c_14, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.11/1.25  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.11/1.25  tff(c_109, plain, (![B_30, A_31]: (k3_xboole_0(k1_relat_1(B_30), A_31)=k1_relat_1(k7_relat_1(B_30, A_31)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.11/1.25  tff(c_32, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.11/1.25  tff(c_96, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_58, c_32])).
% 2.11/1.25  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.25  tff(c_100, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_96, c_2])).
% 2.11/1.25  tff(c_115, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_109, c_100])).
% 2.11/1.25  tff(c_135, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_115])).
% 2.11/1.25  tff(c_18, plain, (![A_10]: (~v1_xboole_0(k1_relat_1(A_10)) | ~v1_relat_1(A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.25  tff(c_145, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | v1_xboole_0(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_18])).
% 2.11/1.25  tff(c_149, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | v1_xboole_0(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_145])).
% 2.11/1.25  tff(c_209, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_149])).
% 2.11/1.25  tff(c_212, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_209])).
% 2.11/1.25  tff(c_216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_212])).
% 2.11/1.25  tff(c_217, plain, (v1_xboole_0(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_149])).
% 2.11/1.25  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.11/1.25  tff(c_223, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_217, c_8])).
% 2.11/1.25  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_223])).
% 2.11/1.25  tff(c_229, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_26])).
% 2.11/1.25  tff(c_287, plain, (![B_42, A_43]: (k3_xboole_0(k1_relat_1(B_42), A_43)=k1_relat_1(k7_relat_1(B_42, A_43)) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.11/1.25  tff(c_278, plain, (![A_40, B_41]: (r1_xboole_0(A_40, B_41) | k3_xboole_0(A_40, B_41)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.25  tff(c_228, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_26])).
% 2.11/1.25  tff(c_286, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_278, c_228])).
% 2.11/1.25  tff(c_293, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_287, c_286])).
% 2.11/1.25  tff(c_310, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_229, c_293])).
% 2.11/1.25  tff(c_10, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.11/1.25  tff(c_48, plain, (![A_20, B_21]: (v1_relat_1(k3_xboole_0(A_20, B_21)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.11/1.25  tff(c_51, plain, (![A_4]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_4))), inference(superposition, [status(thm), theory('equality')], [c_10, c_48])).
% 2.11/1.25  tff(c_52, plain, (![A_4]: (~v1_relat_1(A_4))), inference(splitLeft, [status(thm)], [c_51])).
% 2.11/1.25  tff(c_56, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_24])).
% 2.11/1.25  tff(c_57, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_51])).
% 2.11/1.25  tff(c_239, plain, (![B_34, A_35]: (r1_tarski(k7_relat_1(B_34, A_35), B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.11/1.25  tff(c_12, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.11/1.25  tff(c_243, plain, (![A_35]: (k7_relat_1(k1_xboole_0, A_35)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_239, c_12])).
% 2.11/1.25  tff(c_249, plain, (![A_35]: (k7_relat_1(k1_xboole_0, A_35)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_57, c_243])).
% 2.11/1.25  tff(c_312, plain, (![B_44]: (k1_relat_1(k7_relat_1(B_44, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_44))), inference(superposition, [status(thm), theory('equality')], [c_10, c_287])).
% 2.11/1.25  tff(c_328, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_249, c_312])).
% 2.11/1.25  tff(c_334, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_57, c_328])).
% 2.11/1.25  tff(c_335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_310, c_334])).
% 2.11/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.25  
% 2.11/1.25  Inference rules
% 2.11/1.25  ----------------------
% 2.11/1.25  #Ref     : 0
% 2.11/1.25  #Sup     : 65
% 2.11/1.25  #Fact    : 0
% 2.11/1.25  #Define  : 0
% 2.11/1.25  #Split   : 4
% 2.11/1.25  #Chain   : 0
% 2.11/1.25  #Close   : 0
% 2.11/1.25  
% 2.11/1.25  Ordering : KBO
% 2.11/1.25  
% 2.11/1.25  Simplification rules
% 2.11/1.25  ----------------------
% 2.11/1.25  #Subsume      : 3
% 2.11/1.25  #Demod        : 33
% 2.11/1.25  #Tautology    : 41
% 2.11/1.25  #SimpNegUnit  : 7
% 2.11/1.25  #BackRed      : 1
% 2.11/1.25  
% 2.11/1.25  #Partial instantiations: 0
% 2.11/1.25  #Strategies tried      : 1
% 2.11/1.25  
% 2.11/1.25  Timing (in seconds)
% 2.11/1.25  ----------------------
% 2.11/1.25  Preprocessing        : 0.30
% 2.11/1.25  Parsing              : 0.17
% 2.11/1.25  CNF conversion       : 0.02
% 2.11/1.25  Main loop            : 0.18
% 2.11/1.25  Inferencing          : 0.07
% 2.11/1.25  Reduction            : 0.06
% 2.11/1.25  Demodulation         : 0.03
% 2.11/1.25  BG Simplification    : 0.01
% 2.11/1.25  Subsumption          : 0.03
% 2.11/1.25  Abstraction          : 0.01
% 2.11/1.25  MUC search           : 0.00
% 2.11/1.25  Cooper               : 0.00
% 2.11/1.25  Total                : 0.51
% 2.11/1.25  Index Insertion      : 0.00
% 2.11/1.25  Index Deletion       : 0.00
% 2.11/1.25  Index Matching       : 0.00
% 2.11/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
