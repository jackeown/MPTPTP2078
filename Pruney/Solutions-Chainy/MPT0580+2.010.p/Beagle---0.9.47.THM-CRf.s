%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:58 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   56 (  89 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   76 ( 165 expanded)
%              Number of equality atoms :   19 (  43 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v3_relat_1 > v1_relat_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(v3_relat_1,type,(
    v3_relat_1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( v3_relat_1(A)
        <=> ! [B] :
              ( r2_hidden(B,k2_relat_1(A))
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_relat_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v3_relat_1(A)
      <=> r1_tarski(k2_relat_1(A),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_relat_1)).

tff(c_34,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ v3_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_45,plain,(
    ~ v3_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_55,plain,(
    ! [D_18,A_19] : r2_hidden(D_18,k2_tarski(A_19,D_18)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_58,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_55])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    ! [B_16] :
      ( v3_relat_1('#skF_4')
      | k1_xboole_0 = B_16
      | ~ r2_hidden(B_16,k2_relat_1('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_75,plain,(
    ! [B_28] :
      ( k1_xboole_0 = B_28
      | ~ r2_hidden(B_28,k2_relat_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_44])).

tff(c_157,plain,(
    ! [B_47] :
      ( '#skF_1'(k2_relat_1('#skF_4'),B_47) = k1_xboole_0
      | r1_tarski(k2_relat_1('#skF_4'),B_47) ) ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_28,plain,(
    ! [A_13] :
      ( v3_relat_1(A_13)
      | ~ r1_tarski(k2_relat_1(A_13),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_161,plain,
    ( v3_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_1'(k2_relat_1('#skF_4'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_157,c_28])).

tff(c_164,plain,
    ( v3_relat_1('#skF_4')
    | '#skF_1'(k2_relat_1('#skF_4'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_161])).

tff(c_165,plain,(
    '#skF_1'(k2_relat_1('#skF_4'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_164])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_170,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | r1_tarski(k2_relat_1('#skF_4'),k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_4])).

tff(c_177,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_170])).

tff(c_181,plain,
    ( v3_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_177,c_28])).

tff(c_184,plain,(
    v3_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_181])).

tff(c_186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_184])).

tff(c_187,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_188,plain,(
    v3_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_30,plain,(
    ! [A_13] :
      ( r1_tarski(k2_relat_1(A_13),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36,plain,
    ( r2_hidden('#skF_5',k2_relat_1('#skF_4'))
    | ~ v3_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_189,plain,(
    ~ v3_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_189])).

tff(c_192,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_259,plain,(
    ! [C_69,B_70,A_71] :
      ( r2_hidden(C_69,B_70)
      | ~ r2_hidden(C_69,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_276,plain,(
    ! [B_72] :
      ( r2_hidden('#skF_5',B_72)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_72) ) ),
    inference(resolution,[status(thm)],[c_192,c_259])).

tff(c_280,plain,
    ( r2_hidden('#skF_5',k1_tarski(k1_xboole_0))
    | ~ v3_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_276])).

tff(c_287,plain,(
    r2_hidden('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_188,c_280])).

tff(c_224,plain,(
    ! [D_63,B_64,A_65] :
      ( D_63 = B_64
      | D_63 = A_65
      | ~ r2_hidden(D_63,k2_tarski(A_65,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_237,plain,(
    ! [D_63,A_12] :
      ( D_63 = A_12
      | D_63 = A_12
      | ~ r2_hidden(D_63,k1_tarski(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_224])).

tff(c_294,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_287,c_237])).

tff(c_299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_187,c_294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.29  
% 2.10/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.29  %$ r2_hidden > r1_tarski > v3_relat_1 > v1_relat_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.10/1.29  
% 2.10/1.29  %Foreground sorts:
% 2.10/1.29  
% 2.10/1.29  
% 2.10/1.29  %Background operators:
% 2.10/1.29  
% 2.10/1.29  
% 2.10/1.29  %Foreground operators:
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.10/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.29  tff(v3_relat_1, type, v3_relat_1: $i > $o).
% 2.10/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.10/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.10/1.29  
% 2.10/1.31  tff(f_59, negated_conjecture, ~(![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> (![B]: (r2_hidden(B, k2_relat_1(A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t184_relat_1)).
% 2.10/1.31  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.10/1.31  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.10/1.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.10/1.31  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> r1_tarski(k2_relat_1(A), k1_tarski(k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_relat_1)).
% 2.10/1.31  tff(c_34, plain, (k1_xboole_0!='#skF_5' | ~v3_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.31  tff(c_45, plain, (~v3_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_34])).
% 2.10/1.31  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.31  tff(c_26, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.31  tff(c_55, plain, (![D_18, A_19]: (r2_hidden(D_18, k2_tarski(A_19, D_18)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.10/1.31  tff(c_58, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_55])).
% 2.10/1.31  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.10/1.31  tff(c_44, plain, (![B_16]: (v3_relat_1('#skF_4') | k1_xboole_0=B_16 | ~r2_hidden(B_16, k2_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.31  tff(c_75, plain, (![B_28]: (k1_xboole_0=B_28 | ~r2_hidden(B_28, k2_relat_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_45, c_44])).
% 2.10/1.31  tff(c_157, plain, (![B_47]: ('#skF_1'(k2_relat_1('#skF_4'), B_47)=k1_xboole_0 | r1_tarski(k2_relat_1('#skF_4'), B_47))), inference(resolution, [status(thm)], [c_6, c_75])).
% 2.10/1.31  tff(c_28, plain, (![A_13]: (v3_relat_1(A_13) | ~r1_tarski(k2_relat_1(A_13), k1_tarski(k1_xboole_0)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.10/1.31  tff(c_161, plain, (v3_relat_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_1'(k2_relat_1('#skF_4'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_157, c_28])).
% 2.10/1.31  tff(c_164, plain, (v3_relat_1('#skF_4') | '#skF_1'(k2_relat_1('#skF_4'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_161])).
% 2.10/1.31  tff(c_165, plain, ('#skF_1'(k2_relat_1('#skF_4'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_45, c_164])).
% 2.10/1.31  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.10/1.31  tff(c_170, plain, (~r2_hidden(k1_xboole_0, k1_tarski(k1_xboole_0)) | r1_tarski(k2_relat_1('#skF_4'), k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_165, c_4])).
% 2.10/1.31  tff(c_177, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_170])).
% 2.10/1.31  tff(c_181, plain, (v3_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_177, c_28])).
% 2.10/1.31  tff(c_184, plain, (v3_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_181])).
% 2.10/1.31  tff(c_186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_184])).
% 2.10/1.31  tff(c_187, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_34])).
% 2.10/1.31  tff(c_188, plain, (v3_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_34])).
% 2.10/1.31  tff(c_30, plain, (![A_13]: (r1_tarski(k2_relat_1(A_13), k1_tarski(k1_xboole_0)) | ~v3_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.10/1.31  tff(c_36, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_4')) | ~v3_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.31  tff(c_189, plain, (~v3_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_36])).
% 2.10/1.31  tff(c_191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_189])).
% 2.10/1.31  tff(c_192, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_36])).
% 2.10/1.31  tff(c_259, plain, (![C_69, B_70, A_71]: (r2_hidden(C_69, B_70) | ~r2_hidden(C_69, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.10/1.31  tff(c_276, plain, (![B_72]: (r2_hidden('#skF_5', B_72) | ~r1_tarski(k2_relat_1('#skF_4'), B_72))), inference(resolution, [status(thm)], [c_192, c_259])).
% 2.10/1.31  tff(c_280, plain, (r2_hidden('#skF_5', k1_tarski(k1_xboole_0)) | ~v3_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_276])).
% 2.10/1.31  tff(c_287, plain, (r2_hidden('#skF_5', k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_188, c_280])).
% 2.10/1.31  tff(c_224, plain, (![D_63, B_64, A_65]: (D_63=B_64 | D_63=A_65 | ~r2_hidden(D_63, k2_tarski(A_65, B_64)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.10/1.31  tff(c_237, plain, (![D_63, A_12]: (D_63=A_12 | D_63=A_12 | ~r2_hidden(D_63, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_224])).
% 2.10/1.31  tff(c_294, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_287, c_237])).
% 2.10/1.31  tff(c_299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_187, c_187, c_294])).
% 2.10/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.31  
% 2.10/1.31  Inference rules
% 2.10/1.31  ----------------------
% 2.10/1.31  #Ref     : 0
% 2.10/1.31  #Sup     : 49
% 2.10/1.31  #Fact    : 0
% 2.10/1.31  #Define  : 0
% 2.10/1.31  #Split   : 3
% 2.10/1.31  #Chain   : 0
% 2.10/1.31  #Close   : 0
% 2.10/1.31  
% 2.10/1.31  Ordering : KBO
% 2.10/1.31  
% 2.10/1.31  Simplification rules
% 2.10/1.31  ----------------------
% 2.10/1.31  #Subsume      : 5
% 2.10/1.31  #Demod        : 15
% 2.10/1.31  #Tautology    : 24
% 2.10/1.31  #SimpNegUnit  : 4
% 2.10/1.31  #BackRed      : 0
% 2.10/1.31  
% 2.10/1.31  #Partial instantiations: 0
% 2.10/1.31  #Strategies tried      : 1
% 2.10/1.31  
% 2.10/1.31  Timing (in seconds)
% 2.10/1.31  ----------------------
% 2.10/1.31  Preprocessing        : 0.29
% 2.10/1.31  Parsing              : 0.14
% 2.10/1.31  CNF conversion       : 0.02
% 2.10/1.31  Main loop            : 0.19
% 2.10/1.31  Inferencing          : 0.07
% 2.10/1.31  Reduction            : 0.05
% 2.10/1.31  Demodulation         : 0.04
% 2.10/1.31  BG Simplification    : 0.01
% 2.10/1.31  Subsumption          : 0.04
% 2.10/1.31  Abstraction          : 0.01
% 2.10/1.31  MUC search           : 0.00
% 2.10/1.31  Cooper               : 0.00
% 2.10/1.31  Total                : 0.51
% 2.10/1.31  Index Insertion      : 0.00
% 2.10/1.31  Index Deletion       : 0.00
% 2.10/1.31  Index Matching       : 0.00
% 2.10/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
