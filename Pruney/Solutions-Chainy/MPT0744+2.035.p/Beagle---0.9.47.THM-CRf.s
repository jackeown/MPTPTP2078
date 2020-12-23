%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:19 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 126 expanded)
%              Number of leaves         :   23 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 273 expanded)
%              Number of equality atoms :   10 (  21 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_38,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_34,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( r1_ordinal1(B_5,A_4)
      | r1_ordinal1(A_4,B_5)
      | ~ v3_ordinal1(B_5)
      | ~ v3_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_396,plain,(
    ! [B_79] :
      ( ~ v3_ordinal1(B_79)
      | r1_ordinal1(B_79,B_79) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_12])).

tff(c_24,plain,(
    ! [B_11] : r2_hidden(B_11,k1_ordinal1(B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_64,plain,(
    ~ r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_42,plain,
    ( r2_hidden('#skF_1',k1_ordinal1('#skF_2'))
    | r1_ordinal1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_90,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_42])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ r1_ordinal1(A_7,B_8)
      | ~ v3_ordinal1(B_8)
      | ~ v3_ordinal1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46,plain,(
    ! [A_20] :
      ( v1_ordinal1(A_20)
      | ~ v3_ordinal1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_54,plain,(
    v1_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_46])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_114,plain,(
    ! [A_38,B_39] :
      ( r2_hidden(A_38,B_39)
      | ~ r2_xboole_0(A_38,B_39)
      | ~ v3_ordinal1(B_39)
      | ~ v1_ordinal1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_162,plain,(
    ! [A_47,B_48] :
      ( r2_hidden(A_47,B_48)
      | ~ v3_ordinal1(B_48)
      | ~ v1_ordinal1(A_47)
      | B_48 = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(resolution,[status(thm)],[c_2,c_114])).

tff(c_80,plain,(
    ! [A_27,B_28] :
      ( ~ r2_hidden(A_27,B_28)
      | r2_hidden(A_27,k1_ordinal1(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_88,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_64])).

tff(c_169,plain,
    ( ~ v3_ordinal1('#skF_2')
    | ~ v1_ordinal1('#skF_1')
    | '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_162,c_88])).

tff(c_179,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_32,c_169])).

tff(c_184,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_187,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_184])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_90,c_187])).

tff(c_192,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_196,plain,(
    ~ r2_hidden('#skF_1',k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_64])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_196])).

tff(c_203,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_312,plain,(
    ! [B_70,A_71] :
      ( r1_ordinal1(B_70,A_71)
      | r1_ordinal1(A_71,B_70)
      | ~ v3_ordinal1(B_70)
      | ~ v3_ordinal1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_263,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | ~ r1_ordinal1(A_63,B_64)
      | ~ v3_ordinal1(B_64)
      | ~ v3_ordinal1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_204,plain,(
    r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_244,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | r2_hidden(A_62,B_61)
      | ~ r2_hidden(A_62,k1_ordinal1(B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_255,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_204,c_244])).

tff(c_258,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_30,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_262,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_258,c_30])).

tff(c_266,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_263,c_262])).

tff(c_280,plain,(
    ~ r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_266])).

tff(c_319,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_312,c_280])).

tff(c_332,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_319])).

tff(c_334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_332])).

tff(c_335,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_340,plain,(
    ~ r1_ordinal1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_203])).

tff(c_399,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_396,c_340])).

tff(c_403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_399])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:50:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.34  
% 2.08/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.34  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 2.08/1.34  
% 2.08/1.34  %Foreground sorts:
% 2.08/1.34  
% 2.08/1.34  
% 2.08/1.34  %Background operators:
% 2.08/1.34  
% 2.08/1.34  
% 2.08/1.34  %Foreground operators:
% 2.08/1.34  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.08/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.34  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.08/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.34  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.08/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.34  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.08/1.34  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.08/1.34  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.08/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.34  
% 2.38/1.35  tff(f_88, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 2.38/1.35  tff(f_46, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 2.38/1.35  tff(f_64, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 2.38/1.35  tff(f_56, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.38/1.35  tff(f_38, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 2.38/1.35  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.38/1.35  tff(f_73, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 2.38/1.35  tff(f_78, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.38/1.35  tff(c_34, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.38/1.35  tff(c_12, plain, (![B_5, A_4]: (r1_ordinal1(B_5, A_4) | r1_ordinal1(A_4, B_5) | ~v3_ordinal1(B_5) | ~v3_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.38/1.35  tff(c_396, plain, (![B_79]: (~v3_ordinal1(B_79) | r1_ordinal1(B_79, B_79))), inference(factorization, [status(thm), theory('equality')], [c_12])).
% 2.38/1.35  tff(c_24, plain, (![B_11]: (r2_hidden(B_11, k1_ordinal1(B_11)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.38/1.35  tff(c_32, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.38/1.35  tff(c_36, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.38/1.35  tff(c_64, plain, (~r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_36])).
% 2.38/1.35  tff(c_42, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2')) | r1_ordinal1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.38/1.35  tff(c_90, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_64, c_42])).
% 2.38/1.35  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~r1_ordinal1(A_7, B_8) | ~v3_ordinal1(B_8) | ~v3_ordinal1(A_7))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.38/1.35  tff(c_46, plain, (![A_20]: (v1_ordinal1(A_20) | ~v3_ordinal1(A_20))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.38/1.35  tff(c_54, plain, (v1_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_34, c_46])).
% 2.38/1.35  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.38/1.35  tff(c_114, plain, (![A_38, B_39]: (r2_hidden(A_38, B_39) | ~r2_xboole_0(A_38, B_39) | ~v3_ordinal1(B_39) | ~v1_ordinal1(A_38))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.38/1.35  tff(c_162, plain, (![A_47, B_48]: (r2_hidden(A_47, B_48) | ~v3_ordinal1(B_48) | ~v1_ordinal1(A_47) | B_48=A_47 | ~r1_tarski(A_47, B_48))), inference(resolution, [status(thm)], [c_2, c_114])).
% 2.38/1.35  tff(c_80, plain, (![A_27, B_28]: (~r2_hidden(A_27, B_28) | r2_hidden(A_27, k1_ordinal1(B_28)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.38/1.35  tff(c_88, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_80, c_64])).
% 2.38/1.35  tff(c_169, plain, (~v3_ordinal1('#skF_2') | ~v1_ordinal1('#skF_1') | '#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_162, c_88])).
% 2.38/1.35  tff(c_179, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_32, c_169])).
% 2.38/1.35  tff(c_184, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_179])).
% 2.38/1.35  tff(c_187, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_184])).
% 2.38/1.35  tff(c_191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_90, c_187])).
% 2.38/1.35  tff(c_192, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_179])).
% 2.38/1.35  tff(c_196, plain, (~r2_hidden('#skF_1', k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_64])).
% 2.38/1.35  tff(c_202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_196])).
% 2.38/1.35  tff(c_203, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 2.38/1.35  tff(c_312, plain, (![B_70, A_71]: (r1_ordinal1(B_70, A_71) | r1_ordinal1(A_71, B_70) | ~v3_ordinal1(B_70) | ~v3_ordinal1(A_71))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.38/1.35  tff(c_263, plain, (![A_63, B_64]: (r1_tarski(A_63, B_64) | ~r1_ordinal1(A_63, B_64) | ~v3_ordinal1(B_64) | ~v3_ordinal1(A_63))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.38/1.35  tff(c_204, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_36])).
% 2.38/1.35  tff(c_244, plain, (![B_61, A_62]: (B_61=A_62 | r2_hidden(A_62, B_61) | ~r2_hidden(A_62, k1_ordinal1(B_61)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.38/1.35  tff(c_255, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_204, c_244])).
% 2.38/1.35  tff(c_258, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_255])).
% 2.38/1.35  tff(c_30, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.38/1.35  tff(c_262, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_258, c_30])).
% 2.38/1.35  tff(c_266, plain, (~r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_263, c_262])).
% 2.38/1.35  tff(c_280, plain, (~r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_266])).
% 2.38/1.35  tff(c_319, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_312, c_280])).
% 2.38/1.35  tff(c_332, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_319])).
% 2.38/1.35  tff(c_334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_203, c_332])).
% 2.38/1.35  tff(c_335, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_255])).
% 2.38/1.35  tff(c_340, plain, (~r1_ordinal1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_335, c_203])).
% 2.38/1.35  tff(c_399, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_396, c_340])).
% 2.38/1.35  tff(c_403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_399])).
% 2.38/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.35  
% 2.38/1.35  Inference rules
% 2.38/1.35  ----------------------
% 2.38/1.35  #Ref     : 0
% 2.38/1.35  #Sup     : 53
% 2.38/1.35  #Fact    : 6
% 2.38/1.35  #Define  : 0
% 2.38/1.35  #Split   : 4
% 2.38/1.35  #Chain   : 0
% 2.38/1.35  #Close   : 0
% 2.38/1.35  
% 2.38/1.35  Ordering : KBO
% 2.38/1.35  
% 2.38/1.35  Simplification rules
% 2.38/1.35  ----------------------
% 2.38/1.35  #Subsume      : 3
% 2.38/1.35  #Demod        : 32
% 2.38/1.35  #Tautology    : 24
% 2.38/1.35  #SimpNegUnit  : 3
% 2.38/1.35  #BackRed      : 12
% 2.38/1.35  
% 2.38/1.35  #Partial instantiations: 0
% 2.38/1.35  #Strategies tried      : 1
% 2.38/1.35  
% 2.38/1.35  Timing (in seconds)
% 2.38/1.35  ----------------------
% 2.38/1.36  Preprocessing        : 0.29
% 2.38/1.36  Parsing              : 0.17
% 2.38/1.36  CNF conversion       : 0.02
% 2.38/1.36  Main loop            : 0.24
% 2.38/1.36  Inferencing          : 0.10
% 2.38/1.36  Reduction            : 0.06
% 2.38/1.36  Demodulation         : 0.04
% 2.38/1.36  BG Simplification    : 0.01
% 2.38/1.36  Subsumption          : 0.04
% 2.38/1.36  Abstraction          : 0.01
% 2.38/1.36  MUC search           : 0.00
% 2.38/1.36  Cooper               : 0.00
% 2.38/1.36  Total                : 0.56
% 2.38/1.36  Index Insertion      : 0.00
% 2.38/1.36  Index Deletion       : 0.00
% 2.38/1.36  Index Matching       : 0.00
% 2.38/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
