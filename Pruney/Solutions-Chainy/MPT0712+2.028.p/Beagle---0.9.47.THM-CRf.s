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
% DateTime   : Thu Dec  3 10:05:34 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   53 (  77 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 120 expanded)
%              Number of equality atoms :   26 (  41 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_49,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ! [A_4,B_5,C_6] : r1_tarski(k1_xboole_0,k1_enumset1(A_4,B_5,C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_64,plain,(
    ! [A_26,B_27] : r1_tarski(k1_xboole_0,k2_tarski(A_26,B_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_22])).

tff(c_66,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_64])).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,k1_relat_1(B_14))
      | k11_relat_1(B_14,A_13) = k1_xboole_0
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_165,plain,(
    ! [B_62,A_63] :
      ( k1_tarski(k1_funct_1(B_62,A_63)) = k11_relat_1(B_62,A_63)
      | ~ r2_hidden(A_63,k1_relat_1(B_62))
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_170,plain,(
    ! [B_64,A_65] :
      ( k1_tarski(k1_funct_1(B_64,A_65)) = k11_relat_1(B_64,A_65)
      | ~ v1_funct_1(B_64)
      | k11_relat_1(B_64,A_65) = k1_xboole_0
      | ~ v1_relat_1(B_64) ) ),
    inference(resolution,[status(thm)],[c_28,c_165])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_60,plain,(
    ! [B_23,A_24,C_25] : r1_tarski(k1_tarski(B_23),k1_enumset1(A_24,B_23,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_68,plain,(
    ! [A_29,B_30] : r1_tarski(k1_tarski(A_29),k2_tarski(A_29,B_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_60])).

tff(c_71,plain,(
    ! [A_1] : r1_tarski(k1_tarski(A_1),k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_68])).

tff(c_282,plain,(
    ! [B_74,A_75] :
      ( r1_tarski(k11_relat_1(B_74,A_75),k1_tarski(k1_funct_1(B_74,A_75)))
      | ~ v1_funct_1(B_74)
      | k11_relat_1(B_74,A_75) = k1_xboole_0
      | ~ v1_relat_1(B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_71])).

tff(c_24,plain,(
    ! [A_8,B_10] :
      ( k9_relat_1(A_8,k1_tarski(B_10)) = k11_relat_1(A_8,B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_140,plain,(
    ! [B_56,A_57] :
      ( k2_relat_1(k7_relat_1(B_56,A_57)) = k9_relat_1(B_56,A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_34,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_146,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_34])).

tff(c_152,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_146])).

tff(c_156,plain,
    ( ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_152])).

tff(c_158,plain,(
    ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_156])).

tff(c_285,plain,
    ( ~ v1_funct_1('#skF_2')
    | k11_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_282,c_158])).

tff(c_291,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_285])).

tff(c_295,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_158])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:03:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.31  
% 2.46/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.31  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.46/1.31  
% 2.46/1.31  %Foreground sorts:
% 2.46/1.31  
% 2.46/1.31  
% 2.46/1.31  %Background operators:
% 2.46/1.31  
% 2.46/1.31  
% 2.46/1.31  %Foreground operators:
% 2.46/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.46/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.46/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.46/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.46/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.46/1.31  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.46/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.46/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.46/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.46/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.46/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.46/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.46/1.31  
% 2.46/1.32  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.46/1.32  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.46/1.32  tff(f_56, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 2.46/1.32  tff(f_87, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_funct_1)).
% 2.46/1.32  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 2.46/1.32  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 2.46/1.32  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.46/1.32  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.46/1.32  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.46/1.32  tff(c_49, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.32  tff(c_22, plain, (![A_4, B_5, C_6]: (r1_tarski(k1_xboole_0, k1_enumset1(A_4, B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.46/1.32  tff(c_64, plain, (![A_26, B_27]: (r1_tarski(k1_xboole_0, k2_tarski(A_26, B_27)))), inference(superposition, [status(thm), theory('equality')], [c_49, c_22])).
% 2.46/1.32  tff(c_66, plain, (![A_1]: (r1_tarski(k1_xboole_0, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_64])).
% 2.46/1.32  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.46/1.32  tff(c_36, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.46/1.32  tff(c_28, plain, (![A_13, B_14]: (r2_hidden(A_13, k1_relat_1(B_14)) | k11_relat_1(B_14, A_13)=k1_xboole_0 | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.46/1.32  tff(c_165, plain, (![B_62, A_63]: (k1_tarski(k1_funct_1(B_62, A_63))=k11_relat_1(B_62, A_63) | ~r2_hidden(A_63, k1_relat_1(B_62)) | ~v1_funct_1(B_62) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.46/1.32  tff(c_170, plain, (![B_64, A_65]: (k1_tarski(k1_funct_1(B_64, A_65))=k11_relat_1(B_64, A_65) | ~v1_funct_1(B_64) | k11_relat_1(B_64, A_65)=k1_xboole_0 | ~v1_relat_1(B_64))), inference(resolution, [status(thm)], [c_28, c_165])).
% 2.46/1.32  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.32  tff(c_60, plain, (![B_23, A_24, C_25]: (r1_tarski(k1_tarski(B_23), k1_enumset1(A_24, B_23, C_25)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.46/1.32  tff(c_68, plain, (![A_29, B_30]: (r1_tarski(k1_tarski(A_29), k2_tarski(A_29, B_30)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_60])).
% 2.46/1.32  tff(c_71, plain, (![A_1]: (r1_tarski(k1_tarski(A_1), k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_68])).
% 2.46/1.32  tff(c_282, plain, (![B_74, A_75]: (r1_tarski(k11_relat_1(B_74, A_75), k1_tarski(k1_funct_1(B_74, A_75))) | ~v1_funct_1(B_74) | k11_relat_1(B_74, A_75)=k1_xboole_0 | ~v1_relat_1(B_74))), inference(superposition, [status(thm), theory('equality')], [c_170, c_71])).
% 2.46/1.32  tff(c_24, plain, (![A_8, B_10]: (k9_relat_1(A_8, k1_tarski(B_10))=k11_relat_1(A_8, B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.46/1.32  tff(c_140, plain, (![B_56, A_57]: (k2_relat_1(k7_relat_1(B_56, A_57))=k9_relat_1(B_56, A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.46/1.32  tff(c_34, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.46/1.32  tff(c_146, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_140, c_34])).
% 2.46/1.32  tff(c_152, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_146])).
% 2.46/1.32  tff(c_156, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_24, c_152])).
% 2.46/1.32  tff(c_158, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_156])).
% 2.46/1.32  tff(c_285, plain, (~v1_funct_1('#skF_2') | k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_282, c_158])).
% 2.46/1.32  tff(c_291, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_285])).
% 2.46/1.32  tff(c_295, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_158])).
% 2.46/1.32  tff(c_298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_295])).
% 2.46/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.32  
% 2.46/1.32  Inference rules
% 2.46/1.32  ----------------------
% 2.46/1.32  #Ref     : 0
% 2.46/1.32  #Sup     : 57
% 2.46/1.32  #Fact    : 0
% 2.46/1.32  #Define  : 0
% 2.46/1.32  #Split   : 2
% 2.46/1.32  #Chain   : 0
% 2.46/1.32  #Close   : 0
% 2.46/1.32  
% 2.46/1.32  Ordering : KBO
% 2.46/1.32  
% 2.46/1.32  Simplification rules
% 2.46/1.32  ----------------------
% 2.46/1.32  #Subsume      : 2
% 2.46/1.32  #Demod        : 37
% 2.46/1.32  #Tautology    : 30
% 2.46/1.32  #SimpNegUnit  : 0
% 2.46/1.32  #BackRed      : 4
% 2.46/1.32  
% 2.46/1.32  #Partial instantiations: 0
% 2.46/1.32  #Strategies tried      : 1
% 2.46/1.32  
% 2.46/1.32  Timing (in seconds)
% 2.46/1.32  ----------------------
% 2.46/1.32  Preprocessing        : 0.31
% 2.46/1.32  Parsing              : 0.16
% 2.46/1.32  CNF conversion       : 0.02
% 2.46/1.32  Main loop            : 0.25
% 2.46/1.33  Inferencing          : 0.09
% 2.46/1.33  Reduction            : 0.08
% 2.46/1.33  Demodulation         : 0.06
% 2.46/1.33  BG Simplification    : 0.02
% 2.46/1.33  Subsumption          : 0.04
% 2.46/1.33  Abstraction          : 0.02
% 2.46/1.33  MUC search           : 0.00
% 2.46/1.33  Cooper               : 0.00
% 2.46/1.33  Total                : 0.58
% 2.46/1.33  Index Insertion      : 0.00
% 2.46/1.33  Index Deletion       : 0.00
% 2.46/1.33  Index Matching       : 0.00
% 2.46/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
