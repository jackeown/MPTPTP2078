%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:18 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   46 (  66 expanded)
%              Number of leaves         :   19 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 ( 107 expanded)
%              Number of equality atoms :   29 (  45 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,
    ( k11_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_45,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_24,plain,
    ( r2_hidden('#skF_1',k1_relat_1('#skF_2'))
    | k11_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_46,plain,(
    k11_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_24])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,k1_tarski(B_4)) = A_3
      | r2_hidden(B_4,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_61,plain,(
    ! [B_22,A_23] :
      ( k9_relat_1(B_22,A_23) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_22),A_23)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_96,plain,(
    ! [B_28,B_29] :
      ( k9_relat_1(B_28,B_29) = k1_xboole_0
      | ~ v1_relat_1(B_28)
      | k4_xboole_0(k1_relat_1(B_28),B_29) != k1_relat_1(B_28) ) ),
    inference(resolution,[status(thm)],[c_4,c_61])).

tff(c_106,plain,(
    ! [B_30,B_31] :
      ( k9_relat_1(B_30,k1_tarski(B_31)) = k1_xboole_0
      | ~ v1_relat_1(B_30)
      | r2_hidden(B_31,k1_relat_1(B_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_96])).

tff(c_112,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_106,c_45])).

tff(c_116,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_112])).

tff(c_10,plain,(
    ! [A_5,B_7] :
      ( k9_relat_1(A_5,k1_tarski(B_7)) = k11_relat_1(A_5,B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_120,plain,
    ( k11_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_10])).

tff(c_127,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_120])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_127])).

tff(c_130,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_131,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_153,plain,(
    ! [B_36,A_37] :
      ( r1_xboole_0(k1_relat_1(B_36),A_37)
      | k9_relat_1(B_36,A_37) != k1_xboole_0
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = A_1
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_169,plain,(
    ! [B_42,A_43] :
      ( k4_xboole_0(k1_relat_1(B_42),A_43) = k1_relat_1(B_42)
      | k9_relat_1(B_42,A_43) != k1_xboole_0
      | ~ v1_relat_1(B_42) ) ),
    inference(resolution,[status(thm)],[c_153,c_2])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( ~ r2_hidden(B_4,A_3)
      | k4_xboole_0(A_3,k1_tarski(B_4)) != A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_197,plain,(
    ! [B_44,B_45] :
      ( ~ r2_hidden(B_44,k1_relat_1(B_45))
      | k9_relat_1(B_45,k1_tarski(B_44)) != k1_xboole_0
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_6])).

tff(c_203,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_131,c_197])).

tff(c_207,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_203])).

tff(c_210,plain,
    ( k11_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_207])).

tff(c_213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_130,c_210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.25  
% 1.91/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.25  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.91/1.25  
% 1.91/1.25  %Foreground sorts:
% 1.91/1.25  
% 1.91/1.25  
% 1.91/1.25  %Background operators:
% 1.91/1.25  
% 1.91/1.25  
% 1.91/1.25  %Foreground operators:
% 1.91/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.91/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.25  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 1.91/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.91/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.25  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.91/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.91/1.25  
% 1.91/1.26  tff(f_53, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 1.91/1.26  tff(f_34, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.91/1.26  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.91/1.26  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 1.91/1.26  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 1.91/1.26  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.26  tff(c_18, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.26  tff(c_45, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_18])).
% 1.91/1.26  tff(c_24, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2')) | k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.26  tff(c_46, plain, (k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_45, c_24])).
% 1.91/1.26  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k1_tarski(B_4))=A_3 | r2_hidden(B_4, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.91/1.26  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k4_xboole_0(A_1, B_2)!=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.91/1.26  tff(c_61, plain, (![B_22, A_23]: (k9_relat_1(B_22, A_23)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_22), A_23) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.91/1.26  tff(c_96, plain, (![B_28, B_29]: (k9_relat_1(B_28, B_29)=k1_xboole_0 | ~v1_relat_1(B_28) | k4_xboole_0(k1_relat_1(B_28), B_29)!=k1_relat_1(B_28))), inference(resolution, [status(thm)], [c_4, c_61])).
% 1.91/1.26  tff(c_106, plain, (![B_30, B_31]: (k9_relat_1(B_30, k1_tarski(B_31))=k1_xboole_0 | ~v1_relat_1(B_30) | r2_hidden(B_31, k1_relat_1(B_30)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_96])).
% 1.91/1.26  tff(c_112, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_106, c_45])).
% 1.91/1.26  tff(c_116, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_112])).
% 1.91/1.26  tff(c_10, plain, (![A_5, B_7]: (k9_relat_1(A_5, k1_tarski(B_7))=k11_relat_1(A_5, B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.91/1.26  tff(c_120, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_116, c_10])).
% 1.91/1.26  tff(c_127, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_120])).
% 1.91/1.26  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_127])).
% 1.91/1.26  tff(c_130, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_18])).
% 1.91/1.26  tff(c_131, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_18])).
% 1.91/1.26  tff(c_153, plain, (![B_36, A_37]: (r1_xboole_0(k1_relat_1(B_36), A_37) | k9_relat_1(B_36, A_37)!=k1_xboole_0 | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.91/1.26  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=A_1 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.91/1.26  tff(c_169, plain, (![B_42, A_43]: (k4_xboole_0(k1_relat_1(B_42), A_43)=k1_relat_1(B_42) | k9_relat_1(B_42, A_43)!=k1_xboole_0 | ~v1_relat_1(B_42))), inference(resolution, [status(thm)], [c_153, c_2])).
% 1.91/1.26  tff(c_6, plain, (![B_4, A_3]: (~r2_hidden(B_4, A_3) | k4_xboole_0(A_3, k1_tarski(B_4))!=A_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.91/1.26  tff(c_197, plain, (![B_44, B_45]: (~r2_hidden(B_44, k1_relat_1(B_45)) | k9_relat_1(B_45, k1_tarski(B_44))!=k1_xboole_0 | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_169, c_6])).
% 1.91/1.26  tff(c_203, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_131, c_197])).
% 1.91/1.26  tff(c_207, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_203])).
% 1.91/1.26  tff(c_210, plain, (k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10, c_207])).
% 1.91/1.26  tff(c_213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_130, c_210])).
% 1.91/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.26  
% 1.91/1.26  Inference rules
% 1.91/1.26  ----------------------
% 1.91/1.26  #Ref     : 0
% 1.91/1.26  #Sup     : 39
% 1.91/1.26  #Fact    : 0
% 1.91/1.26  #Define  : 0
% 1.91/1.26  #Split   : 1
% 1.91/1.26  #Chain   : 0
% 1.91/1.26  #Close   : 0
% 1.91/1.26  
% 1.91/1.26  Ordering : KBO
% 1.91/1.26  
% 1.91/1.26  Simplification rules
% 1.91/1.26  ----------------------
% 1.91/1.26  #Subsume      : 0
% 1.91/1.26  #Demod        : 7
% 1.91/1.26  #Tautology    : 28
% 1.91/1.26  #SimpNegUnit  : 2
% 1.91/1.26  #BackRed      : 0
% 1.91/1.26  
% 1.91/1.26  #Partial instantiations: 0
% 1.91/1.26  #Strategies tried      : 1
% 1.91/1.26  
% 1.91/1.26  Timing (in seconds)
% 1.91/1.26  ----------------------
% 1.91/1.26  Preprocessing        : 0.28
% 1.91/1.26  Parsing              : 0.16
% 1.91/1.26  CNF conversion       : 0.02
% 1.91/1.26  Main loop            : 0.16
% 1.91/1.26  Inferencing          : 0.07
% 1.91/1.26  Reduction            : 0.04
% 1.91/1.26  Demodulation         : 0.02
% 1.91/1.26  BG Simplification    : 0.01
% 1.91/1.26  Subsumption          : 0.02
% 1.91/1.26  Abstraction          : 0.01
% 1.91/1.26  MUC search           : 0.00
% 1.91/1.26  Cooper               : 0.00
% 1.91/1.26  Total                : 0.46
% 1.91/1.26  Index Insertion      : 0.00
% 1.91/1.26  Index Deletion       : 0.00
% 1.91/1.26  Index Matching       : 0.00
% 1.91/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
