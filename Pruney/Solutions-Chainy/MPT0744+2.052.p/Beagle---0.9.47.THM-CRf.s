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
% DateTime   : Thu Dec  3 10:06:21 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 107 expanded)
%              Number of leaves         :   19 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 235 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_66,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_30,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_534,plain,(
    ! [A_80,B_81] :
      ( r1_ordinal1(A_80,B_81)
      | ~ r1_tarski(A_80,B_81)
      | ~ v3_ordinal1(B_81)
      | ~ v3_ordinal1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_539,plain,(
    ! [B_82] :
      ( r1_ordinal1(B_82,B_82)
      | ~ v3_ordinal1(B_82) ) ),
    inference(resolution,[status(thm)],[c_6,c_534])).

tff(c_32,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_63,plain,(
    ~ r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_20,plain,(
    ! [B_10] : r2_hidden(B_10,k1_ordinal1(B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,
    ( r2_hidden('#skF_1',k1_ordinal1('#skF_2'))
    | r1_ordinal1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_64,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_144,plain,(
    ! [B_40,A_41] :
      ( r2_hidden(B_40,A_41)
      | r1_ordinal1(A_41,B_40)
      | ~ v3_ordinal1(B_40)
      | ~ v3_ordinal1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( ~ r2_hidden(A_9,B_10)
      | r2_hidden(A_9,k1_ordinal1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_68,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_63])).

tff(c_175,plain,
    ( r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_144,c_68])).

tff(c_191,plain,(
    r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_175])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ r1_ordinal1(A_6,B_7)
      | ~ v3_ordinal1(B_7)
      | ~ v3_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_197,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ r1_ordinal1(A_42,B_43)
      | ~ v3_ordinal1(B_43)
      | ~ v3_ordinal1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_255,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_ordinal1(A_52,B_51)
      | ~ v3_ordinal1(B_51)
      | ~ v3_ordinal1(A_52) ) ),
    inference(resolution,[status(thm)],[c_197,c_2])).

tff(c_291,plain,(
    ! [B_55,A_56] :
      ( B_55 = A_56
      | ~ r1_ordinal1(B_55,A_56)
      | ~ r1_ordinal1(A_56,B_55)
      | ~ v3_ordinal1(B_55)
      | ~ v3_ordinal1(A_56) ) ),
    inference(resolution,[status(thm)],[c_14,c_255])).

tff(c_297,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_191,c_291])).

tff(c_310,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_64,c_297])).

tff(c_321,plain,(
    ~ r2_hidden('#skF_1',k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_63])).

tff(c_326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_321])).

tff(c_327,plain,(
    r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_327])).

tff(c_334,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_ordinal1(B_4,A_3)
      | r1_ordinal1(A_3,B_4)
      | ~ v3_ordinal1(B_4)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_474,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(A_77,B_78)
      | ~ r1_ordinal1(A_77,B_78)
      | ~ v3_ordinal1(B_78)
      | ~ v3_ordinal1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_335,plain,(
    r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_385,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | r2_hidden(A_67,B_66)
      | ~ r2_hidden(A_67,k1_ordinal1(B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_395,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_335,c_385])).

tff(c_399,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_395])).

tff(c_26,plain,(
    ! [B_15,A_14] :
      ( ~ r1_tarski(B_15,A_14)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_403,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_399,c_26])).

tff(c_480,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_474,c_403])).

tff(c_497,plain,(
    ~ r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_480])).

tff(c_506,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_497])).

tff(c_512,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_506])).

tff(c_514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_512])).

tff(c_515,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_395])).

tff(c_519,plain,(
    ~ r1_ordinal1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_334])).

tff(c_542,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_539,c_519])).

tff(c_546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_542])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.38  
% 2.29/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.38  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 2.29/1.38  
% 2.29/1.38  %Foreground sorts:
% 2.29/1.38  
% 2.29/1.38  
% 2.29/1.38  %Background operators:
% 2.29/1.38  
% 2.29/1.38  
% 2.29/1.38  %Foreground operators:
% 2.29/1.38  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.29/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.29/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.38  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.29/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.38  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.29/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.29/1.38  
% 2.60/1.40  tff(f_81, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 2.60/1.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.60/1.40  tff(f_49, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.60/1.40  tff(f_57, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 2.60/1.40  tff(f_66, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 2.60/1.40  tff(f_39, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 2.60/1.40  tff(f_71, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.60/1.40  tff(c_30, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.60/1.40  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.40  tff(c_534, plain, (![A_80, B_81]: (r1_ordinal1(A_80, B_81) | ~r1_tarski(A_80, B_81) | ~v3_ordinal1(B_81) | ~v3_ordinal1(A_80))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.40  tff(c_539, plain, (![B_82]: (r1_ordinal1(B_82, B_82) | ~v3_ordinal1(B_82))), inference(resolution, [status(thm)], [c_6, c_534])).
% 2.60/1.40  tff(c_32, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.60/1.40  tff(c_63, plain, (~r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.60/1.40  tff(c_20, plain, (![B_10]: (r2_hidden(B_10, k1_ordinal1(B_10)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.60/1.40  tff(c_28, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.60/1.40  tff(c_38, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2')) | r1_ordinal1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.60/1.40  tff(c_64, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_38])).
% 2.60/1.40  tff(c_144, plain, (![B_40, A_41]: (r2_hidden(B_40, A_41) | r1_ordinal1(A_41, B_40) | ~v3_ordinal1(B_40) | ~v3_ordinal1(A_41))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.60/1.40  tff(c_22, plain, (![A_9, B_10]: (~r2_hidden(A_9, B_10) | r2_hidden(A_9, k1_ordinal1(B_10)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.60/1.40  tff(c_68, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_63])).
% 2.60/1.40  tff(c_175, plain, (r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_144, c_68])).
% 2.60/1.40  tff(c_191, plain, (r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_175])).
% 2.60/1.40  tff(c_14, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~r1_ordinal1(A_6, B_7) | ~v3_ordinal1(B_7) | ~v3_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.40  tff(c_197, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~r1_ordinal1(A_42, B_43) | ~v3_ordinal1(B_43) | ~v3_ordinal1(A_42))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.40  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.40  tff(c_255, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_ordinal1(A_52, B_51) | ~v3_ordinal1(B_51) | ~v3_ordinal1(A_52))), inference(resolution, [status(thm)], [c_197, c_2])).
% 2.60/1.40  tff(c_291, plain, (![B_55, A_56]: (B_55=A_56 | ~r1_ordinal1(B_55, A_56) | ~r1_ordinal1(A_56, B_55) | ~v3_ordinal1(B_55) | ~v3_ordinal1(A_56))), inference(resolution, [status(thm)], [c_14, c_255])).
% 2.60/1.40  tff(c_297, plain, ('#skF_2'='#skF_1' | ~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_191, c_291])).
% 2.60/1.40  tff(c_310, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_64, c_297])).
% 2.60/1.40  tff(c_321, plain, (~r2_hidden('#skF_1', k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_63])).
% 2.60/1.40  tff(c_326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_321])).
% 2.60/1.40  tff(c_327, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_38])).
% 2.60/1.40  tff(c_333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_327])).
% 2.60/1.40  tff(c_334, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_32])).
% 2.60/1.40  tff(c_8, plain, (![B_4, A_3]: (r1_ordinal1(B_4, A_3) | r1_ordinal1(A_3, B_4) | ~v3_ordinal1(B_4) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.60/1.40  tff(c_474, plain, (![A_77, B_78]: (r1_tarski(A_77, B_78) | ~r1_ordinal1(A_77, B_78) | ~v3_ordinal1(B_78) | ~v3_ordinal1(A_77))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.40  tff(c_335, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_32])).
% 2.60/1.40  tff(c_385, plain, (![B_66, A_67]: (B_66=A_67 | r2_hidden(A_67, B_66) | ~r2_hidden(A_67, k1_ordinal1(B_66)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.60/1.40  tff(c_395, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_335, c_385])).
% 2.60/1.40  tff(c_399, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_395])).
% 2.60/1.40  tff(c_26, plain, (![B_15, A_14]: (~r1_tarski(B_15, A_14) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.60/1.40  tff(c_403, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_399, c_26])).
% 2.60/1.40  tff(c_480, plain, (~r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_474, c_403])).
% 2.60/1.40  tff(c_497, plain, (~r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_480])).
% 2.60/1.40  tff(c_506, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_497])).
% 2.60/1.40  tff(c_512, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_506])).
% 2.60/1.40  tff(c_514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_334, c_512])).
% 2.60/1.40  tff(c_515, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_395])).
% 2.60/1.40  tff(c_519, plain, (~r1_ordinal1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_515, c_334])).
% 2.60/1.40  tff(c_542, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_539, c_519])).
% 2.60/1.40  tff(c_546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_542])).
% 2.60/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.40  
% 2.60/1.40  Inference rules
% 2.60/1.40  ----------------------
% 2.60/1.40  #Ref     : 0
% 2.60/1.40  #Sup     : 86
% 2.60/1.40  #Fact    : 4
% 2.60/1.40  #Define  : 0
% 2.60/1.40  #Split   : 4
% 2.60/1.40  #Chain   : 0
% 2.60/1.40  #Close   : 0
% 2.60/1.40  
% 2.60/1.40  Ordering : KBO
% 2.60/1.40  
% 2.60/1.40  Simplification rules
% 2.60/1.40  ----------------------
% 2.60/1.40  #Subsume      : 13
% 2.60/1.40  #Demod        : 34
% 2.60/1.40  #Tautology    : 23
% 2.60/1.40  #SimpNegUnit  : 3
% 2.60/1.40  #BackRed      : 10
% 2.60/1.40  
% 2.60/1.40  #Partial instantiations: 0
% 2.60/1.40  #Strategies tried      : 1
% 2.60/1.40  
% 2.60/1.40  Timing (in seconds)
% 2.60/1.40  ----------------------
% 2.60/1.40  Preprocessing        : 0.29
% 2.60/1.40  Parsing              : 0.16
% 2.60/1.40  CNF conversion       : 0.02
% 2.60/1.40  Main loop            : 0.28
% 2.60/1.40  Inferencing          : 0.11
% 2.60/1.40  Reduction            : 0.07
% 2.60/1.40  Demodulation         : 0.05
% 2.60/1.40  BG Simplification    : 0.01
% 2.60/1.40  Subsumption          : 0.06
% 2.60/1.40  Abstraction          : 0.01
% 2.60/1.40  MUC search           : 0.00
% 2.60/1.40  Cooper               : 0.00
% 2.60/1.40  Total                : 0.60
% 2.60/1.40  Index Insertion      : 0.00
% 2.60/1.40  Index Deletion       : 0.00
% 2.60/1.40  Index Matching       : 0.00
% 2.60/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
