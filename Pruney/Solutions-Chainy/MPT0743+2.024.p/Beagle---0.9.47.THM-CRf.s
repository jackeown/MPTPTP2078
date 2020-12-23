%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:11 EST 2020

% Result     : Theorem 5.50s
% Output     : CNFRefutation 5.50s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 137 expanded)
%              Number of leaves         :   20 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  111 ( 306 expanded)
%              Number of equality atoms :    7 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v1_xboole_0 > #nlpp > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_44,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( ~ v1_xboole_0(k1_ordinal1(A))
        & v3_ordinal1(k1_ordinal1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_ordinal1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_69,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3511,plain,(
    ! [A_224,B_225] :
      ( ~ r2_hidden('#skF_1'(A_224,B_225),B_225)
      | r1_tarski(A_224,B_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3520,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_3511])).

tff(c_32,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10,plain,(
    ! [A_8] :
      ( v3_ordinal1(k1_ordinal1(A_8))
      | ~ v3_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_40,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_56,plain,(
    r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_34,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_83,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_34])).

tff(c_30,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_276,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(A_66,B_67)
      | ~ r1_ordinal1(A_66,B_67)
      | ~ v3_ordinal1(B_67)
      | ~ v3_ordinal1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_57,plain,(
    ! [A_29,B_30] :
      ( ~ r2_hidden(A_29,B_30)
      | r2_hidden(A_29,k1_ordinal1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    ! [B_18,A_17] :
      ( ~ r1_tarski(B_18,A_17)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_67,plain,(
    ! [B_30,A_29] :
      ( ~ r1_tarski(k1_ordinal1(B_30),A_29)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_57,c_28])).

tff(c_3283,plain,(
    ! [B_206,B_207] :
      ( ~ r2_hidden(B_206,B_207)
      | ~ r1_ordinal1(k1_ordinal1(B_207),B_206)
      | ~ v3_ordinal1(B_206)
      | ~ v3_ordinal1(k1_ordinal1(B_207)) ) ),
    inference(resolution,[status(thm)],[c_276,c_67])).

tff(c_3317,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_3283])).

tff(c_3328,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3317])).

tff(c_3329,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3328])).

tff(c_3332,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_3329])).

tff(c_3336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3332])).

tff(c_3338,plain,(
    v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3328])).

tff(c_22,plain,(
    ! [B_13] : r2_hidden(B_13,k1_ordinal1(B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_159,plain,(
    ! [C_52,B_53,A_54] :
      ( r2_hidden(C_52,B_53)
      | ~ r2_hidden(C_52,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_168,plain,(
    ! [B_13,B_53] :
      ( r2_hidden(B_13,B_53)
      | ~ r1_tarski(k1_ordinal1(B_13),B_53) ) ),
    inference(resolution,[status(thm)],[c_22,c_159])).

tff(c_3398,plain,(
    ! [B_211,B_212] :
      ( r2_hidden(B_211,B_212)
      | ~ r1_ordinal1(k1_ordinal1(B_211),B_212)
      | ~ v3_ordinal1(B_212)
      | ~ v3_ordinal1(k1_ordinal1(B_211)) ) ),
    inference(resolution,[status(thm)],[c_276,c_168])).

tff(c_3432,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_3398])).

tff(c_3446,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3338,c_30,c_3432])).

tff(c_3448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_3446])).

tff(c_3449,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_3457,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_3449,c_2])).

tff(c_3797,plain,(
    ! [B_264,A_265] :
      ( r2_hidden(B_264,A_265)
      | r1_ordinal1(A_265,B_264)
      | ~ v3_ordinal1(B_264)
      | ~ v3_ordinal1(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | r2_hidden(A_12,B_13)
      | ~ r2_hidden(A_12,k1_ordinal1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4692,plain,(
    ! [B_325,B_324] :
      ( B_325 = B_324
      | r2_hidden(B_324,B_325)
      | r1_ordinal1(k1_ordinal1(B_325),B_324)
      | ~ v3_ordinal1(B_324)
      | ~ v3_ordinal1(k1_ordinal1(B_325)) ) ),
    inference(resolution,[status(thm)],[c_3797,c_20])).

tff(c_3459,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3449,c_34])).

tff(c_4705,plain,
    ( '#skF_2' = '#skF_3'
    | r2_hidden('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4692,c_3459])).

tff(c_4716,plain,
    ( '#skF_2' = '#skF_3'
    | r2_hidden('#skF_3','#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4705])).

tff(c_4717,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_3457,c_4716])).

tff(c_4718,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4717])).

tff(c_4721,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_4718])).

tff(c_4725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4721])).

tff(c_4726,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4717])).

tff(c_3456,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_3449,c_28])).

tff(c_4760,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4726,c_3456])).

tff(c_4765,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3520,c_4760])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:27:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.50/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.50/2.09  
% 5.50/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.50/2.09  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v1_xboole_0 > #nlpp > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1
% 5.50/2.09  
% 5.50/2.09  %Foreground sorts:
% 5.50/2.09  
% 5.50/2.09  
% 5.50/2.09  %Background operators:
% 5.50/2.09  
% 5.50/2.09  
% 5.50/2.09  %Foreground operators:
% 5.50/2.09  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 5.50/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.50/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.50/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.50/2.09  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 5.50/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.50/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.50/2.09  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 5.50/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.50/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.50/2.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.50/2.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.50/2.09  
% 5.50/2.11  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.50/2.11  tff(f_84, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 5.50/2.11  tff(f_44, axiom, (![A]: (v3_ordinal1(A) => (~v1_xboole_0(k1_ordinal1(A)) & v3_ordinal1(k1_ordinal1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_ordinal1)).
% 5.50/2.11  tff(f_52, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 5.50/2.11  tff(f_60, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 5.50/2.11  tff(f_74, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.50/2.11  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 5.50/2.11  tff(f_69, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 5.50/2.11  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.50/2.11  tff(c_3511, plain, (![A_224, B_225]: (~r2_hidden('#skF_1'(A_224, B_225), B_225) | r1_tarski(A_224, B_225))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.50/2.11  tff(c_3520, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_8, c_3511])).
% 5.50/2.11  tff(c_32, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.50/2.11  tff(c_10, plain, (![A_8]: (v3_ordinal1(k1_ordinal1(A_8)) | ~v3_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.50/2.11  tff(c_40, plain, (r2_hidden('#skF_2', '#skF_3') | r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.50/2.11  tff(c_56, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 5.50/2.11  tff(c_34, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3') | ~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.50/2.11  tff(c_83, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_34])).
% 5.50/2.11  tff(c_30, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.50/2.11  tff(c_276, plain, (![A_66, B_67]: (r1_tarski(A_66, B_67) | ~r1_ordinal1(A_66, B_67) | ~v3_ordinal1(B_67) | ~v3_ordinal1(A_66))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.50/2.11  tff(c_57, plain, (![A_29, B_30]: (~r2_hidden(A_29, B_30) | r2_hidden(A_29, k1_ordinal1(B_30)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.50/2.11  tff(c_28, plain, (![B_18, A_17]: (~r1_tarski(B_18, A_17) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.50/2.11  tff(c_67, plain, (![B_30, A_29]: (~r1_tarski(k1_ordinal1(B_30), A_29) | ~r2_hidden(A_29, B_30))), inference(resolution, [status(thm)], [c_57, c_28])).
% 5.50/2.11  tff(c_3283, plain, (![B_206, B_207]: (~r2_hidden(B_206, B_207) | ~r1_ordinal1(k1_ordinal1(B_207), B_206) | ~v3_ordinal1(B_206) | ~v3_ordinal1(k1_ordinal1(B_207)))), inference(resolution, [status(thm)], [c_276, c_67])).
% 5.50/2.11  tff(c_3317, plain, (~r2_hidden('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_3283])).
% 5.50/2.11  tff(c_3328, plain, (~r2_hidden('#skF_3', '#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3317])).
% 5.50/2.11  tff(c_3329, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_3328])).
% 5.50/2.11  tff(c_3332, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_3329])).
% 5.50/2.11  tff(c_3336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_3332])).
% 5.50/2.11  tff(c_3338, plain, (v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_3328])).
% 5.50/2.11  tff(c_22, plain, (![B_13]: (r2_hidden(B_13, k1_ordinal1(B_13)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.50/2.11  tff(c_159, plain, (![C_52, B_53, A_54]: (r2_hidden(C_52, B_53) | ~r2_hidden(C_52, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.50/2.11  tff(c_168, plain, (![B_13, B_53]: (r2_hidden(B_13, B_53) | ~r1_tarski(k1_ordinal1(B_13), B_53))), inference(resolution, [status(thm)], [c_22, c_159])).
% 5.50/2.11  tff(c_3398, plain, (![B_211, B_212]: (r2_hidden(B_211, B_212) | ~r1_ordinal1(k1_ordinal1(B_211), B_212) | ~v3_ordinal1(B_212) | ~v3_ordinal1(k1_ordinal1(B_211)))), inference(resolution, [status(thm)], [c_276, c_168])).
% 5.50/2.11  tff(c_3432, plain, (r2_hidden('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_3398])).
% 5.50/2.11  tff(c_3446, plain, (r2_hidden('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3338, c_30, c_3432])).
% 5.50/2.11  tff(c_3448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_3446])).
% 5.50/2.11  tff(c_3449, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 5.50/2.11  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.50/2.11  tff(c_3457, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_3449, c_2])).
% 5.50/2.11  tff(c_3797, plain, (![B_264, A_265]: (r2_hidden(B_264, A_265) | r1_ordinal1(A_265, B_264) | ~v3_ordinal1(B_264) | ~v3_ordinal1(A_265))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.50/2.11  tff(c_20, plain, (![B_13, A_12]: (B_13=A_12 | r2_hidden(A_12, B_13) | ~r2_hidden(A_12, k1_ordinal1(B_13)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.50/2.11  tff(c_4692, plain, (![B_325, B_324]: (B_325=B_324 | r2_hidden(B_324, B_325) | r1_ordinal1(k1_ordinal1(B_325), B_324) | ~v3_ordinal1(B_324) | ~v3_ordinal1(k1_ordinal1(B_325)))), inference(resolution, [status(thm)], [c_3797, c_20])).
% 5.50/2.11  tff(c_3459, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3449, c_34])).
% 5.50/2.11  tff(c_4705, plain, ('#skF_2'='#skF_3' | r2_hidden('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_4692, c_3459])).
% 5.50/2.11  tff(c_4716, plain, ('#skF_2'='#skF_3' | r2_hidden('#skF_3', '#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_4705])).
% 5.50/2.11  tff(c_4717, plain, ('#skF_2'='#skF_3' | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_3457, c_4716])).
% 5.50/2.11  tff(c_4718, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_4717])).
% 5.50/2.11  tff(c_4721, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_4718])).
% 5.50/2.11  tff(c_4725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_4721])).
% 5.50/2.11  tff(c_4726, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_4717])).
% 5.50/2.11  tff(c_3456, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_3449, c_28])).
% 5.50/2.11  tff(c_4760, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4726, c_3456])).
% 5.50/2.11  tff(c_4765, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3520, c_4760])).
% 5.50/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.50/2.11  
% 5.50/2.11  Inference rules
% 5.50/2.11  ----------------------
% 5.50/2.11  #Ref     : 0
% 5.50/2.11  #Sup     : 953
% 5.50/2.11  #Fact    : 2
% 5.50/2.11  #Define  : 0
% 5.50/2.11  #Split   : 4
% 5.50/2.11  #Chain   : 0
% 5.50/2.11  #Close   : 0
% 5.50/2.11  
% 5.50/2.11  Ordering : KBO
% 5.50/2.11  
% 5.50/2.11  Simplification rules
% 5.50/2.11  ----------------------
% 5.50/2.11  #Subsume      : 294
% 5.50/2.11  #Demod        : 128
% 5.50/2.11  #Tautology    : 51
% 5.50/2.11  #SimpNegUnit  : 15
% 5.50/2.11  #BackRed      : 34
% 5.50/2.11  
% 5.50/2.11  #Partial instantiations: 0
% 5.50/2.11  #Strategies tried      : 1
% 5.50/2.11  
% 5.50/2.11  Timing (in seconds)
% 5.50/2.11  ----------------------
% 5.50/2.11  Preprocessing        : 0.32
% 5.50/2.11  Parsing              : 0.18
% 5.50/2.11  CNF conversion       : 0.02
% 5.50/2.11  Main loop            : 0.95
% 5.50/2.11  Inferencing          : 0.32
% 5.50/2.11  Reduction            : 0.23
% 5.50/2.11  Demodulation         : 0.15
% 5.50/2.11  BG Simplification    : 0.04
% 5.50/2.11  Subsumption          : 0.29
% 5.50/2.11  Abstraction          : 0.04
% 5.50/2.11  MUC search           : 0.00
% 5.50/2.11  Cooper               : 0.00
% 5.50/2.11  Total                : 1.30
% 5.50/2.11  Index Insertion      : 0.00
% 5.50/2.11  Index Deletion       : 0.00
% 5.50/2.11  Index Matching       : 0.00
% 5.50/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
