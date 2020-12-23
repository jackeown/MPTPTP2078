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
% DateTime   : Thu Dec  3 10:06:10 EST 2020

% Result     : Theorem 5.44s
% Output     : CNFRefutation 5.44s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 110 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :  101 ( 234 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_66,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_62,axiom,(
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

tff(c_3282,plain,(
    ! [A_196,B_197] :
      ( ~ r2_hidden('#skF_1'(A_196,B_197),B_197)
      | r1_tarski(A_196,B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3291,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_3282])).

tff(c_28,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    ! [A_16] :
      ( v3_ordinal1(k1_ordinal1(A_16))
      | ~ v3_ordinal1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_53,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_54,plain,(
    r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_36])).

tff(c_253,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ r1_ordinal1(A_57,B_58)
      | ~ v3_ordinal1(B_58)
      | ~ v3_ordinal1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [B_12] : r2_hidden(B_12,k1_ordinal1(B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_140,plain,(
    ! [C_43,B_44,A_45] :
      ( r2_hidden(C_43,B_44)
      | ~ r2_hidden(C_43,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_149,plain,(
    ! [B_12,B_44] :
      ( r2_hidden(B_12,B_44)
      | ~ r1_tarski(k1_ordinal1(B_12),B_44) ) ),
    inference(resolution,[status(thm)],[c_18,c_140])).

tff(c_3177,plain,(
    ! [B_185,B_186] :
      ( r2_hidden(B_185,B_186)
      | ~ r1_ordinal1(k1_ordinal1(B_185),B_186)
      | ~ v3_ordinal1(B_186)
      | ~ v3_ordinal1(k1_ordinal1(B_185)) ) ),
    inference(resolution,[status(thm)],[c_253,c_149])).

tff(c_3211,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_3177])).

tff(c_3225,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3211])).

tff(c_3226,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_3225])).

tff(c_3229,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_3226])).

tff(c_3233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3229])).

tff(c_3235,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_3238,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_3235,c_2])).

tff(c_3396,plain,(
    ! [B_220,A_221] :
      ( r2_hidden(B_220,A_221)
      | r1_ordinal1(A_221,B_220)
      | ~ v3_ordinal1(B_220)
      | ~ v3_ordinal1(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | r2_hidden(A_11,B_12)
      | ~ r2_hidden(A_11,k1_ordinal1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4475,plain,(
    ! [B_291,B_290] :
      ( B_291 = B_290
      | r2_hidden(B_290,B_291)
      | r1_ordinal1(k1_ordinal1(B_291),B_290)
      | ~ v3_ordinal1(B_290)
      | ~ v3_ordinal1(k1_ordinal1(B_291)) ) ),
    inference(resolution,[status(thm)],[c_3396,c_16])).

tff(c_3234,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_4478,plain,
    ( '#skF_2' = '#skF_3'
    | r2_hidden('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4475,c_3234])).

tff(c_4481,plain,
    ( '#skF_2' = '#skF_3'
    | r2_hidden('#skF_3','#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4478])).

tff(c_4482,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_3238,c_4481])).

tff(c_4483,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4482])).

tff(c_4486,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_4483])).

tff(c_4490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4486])).

tff(c_4491,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4482])).

tff(c_3294,plain,(
    ! [C_199,B_200,A_201] :
      ( r2_hidden(C_199,B_200)
      | ~ r2_hidden(C_199,A_201)
      | ~ r1_tarski(A_201,B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3305,plain,(
    ! [B_200] :
      ( r2_hidden('#skF_2',B_200)
      | ~ r1_tarski('#skF_3',B_200) ) ),
    inference(resolution,[status(thm)],[c_3235,c_3294])).

tff(c_3307,plain,(
    ! [B_202] :
      ( r2_hidden('#skF_2',B_202)
      | ~ r1_tarski('#skF_3',B_202) ) ),
    inference(resolution,[status(thm)],[c_3235,c_3294])).

tff(c_3314,plain,(
    ! [B_203] :
      ( ~ r2_hidden(B_203,'#skF_2')
      | ~ r1_tarski('#skF_3',B_203) ) ),
    inference(resolution,[status(thm)],[c_3307,c_2])).

tff(c_3323,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_3305,c_3314])).

tff(c_4522,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4491,c_3323])).

tff(c_4534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3291,c_4522])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:31:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.44/2.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.44/2.03  
% 5.44/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.44/2.03  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1
% 5.44/2.03  
% 5.44/2.03  %Foreground sorts:
% 5.44/2.03  
% 5.44/2.03  
% 5.44/2.03  %Background operators:
% 5.44/2.03  
% 5.44/2.03  
% 5.44/2.03  %Foreground operators:
% 5.44/2.03  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 5.44/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.44/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.44/2.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.44/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.44/2.03  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 5.44/2.03  tff('#skF_2', type, '#skF_2': $i).
% 5.44/2.03  tff('#skF_3', type, '#skF_3': $i).
% 5.44/2.03  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 5.44/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.44/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.44/2.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.44/2.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.44/2.03  
% 5.44/2.04  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.44/2.04  tff(f_76, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 5.44/2.04  tff(f_66, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 5.44/2.04  tff(f_47, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 5.44/2.04  tff(f_53, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 5.44/2.04  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 5.44/2.04  tff(f_62, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 5.44/2.04  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.44/2.04  tff(c_3282, plain, (![A_196, B_197]: (~r2_hidden('#skF_1'(A_196, B_197), B_197) | r1_tarski(A_196, B_197))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.44/2.04  tff(c_3291, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_8, c_3282])).
% 5.44/2.04  tff(c_28, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.44/2.04  tff(c_24, plain, (![A_16]: (v3_ordinal1(k1_ordinal1(A_16)) | ~v3_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.44/2.04  tff(c_30, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3') | ~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.44/2.04  tff(c_53, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 5.44/2.04  tff(c_26, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.44/2.04  tff(c_36, plain, (r2_hidden('#skF_2', '#skF_3') | r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.44/2.04  tff(c_54, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_53, c_36])).
% 5.44/2.04  tff(c_253, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~r1_ordinal1(A_57, B_58) | ~v3_ordinal1(B_58) | ~v3_ordinal1(A_57))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.44/2.04  tff(c_18, plain, (![B_12]: (r2_hidden(B_12, k1_ordinal1(B_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.44/2.04  tff(c_140, plain, (![C_43, B_44, A_45]: (r2_hidden(C_43, B_44) | ~r2_hidden(C_43, A_45) | ~r1_tarski(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.44/2.04  tff(c_149, plain, (![B_12, B_44]: (r2_hidden(B_12, B_44) | ~r1_tarski(k1_ordinal1(B_12), B_44))), inference(resolution, [status(thm)], [c_18, c_140])).
% 5.44/2.04  tff(c_3177, plain, (![B_185, B_186]: (r2_hidden(B_185, B_186) | ~r1_ordinal1(k1_ordinal1(B_185), B_186) | ~v3_ordinal1(B_186) | ~v3_ordinal1(k1_ordinal1(B_185)))), inference(resolution, [status(thm)], [c_253, c_149])).
% 5.44/2.04  tff(c_3211, plain, (r2_hidden('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_3177])).
% 5.44/2.04  tff(c_3225, plain, (r2_hidden('#skF_2', '#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3211])).
% 5.44/2.04  tff(c_3226, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_53, c_3225])).
% 5.44/2.04  tff(c_3229, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_3226])).
% 5.44/2.04  tff(c_3233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_3229])).
% 5.44/2.04  tff(c_3235, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 5.44/2.04  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.44/2.04  tff(c_3238, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_3235, c_2])).
% 5.44/2.04  tff(c_3396, plain, (![B_220, A_221]: (r2_hidden(B_220, A_221) | r1_ordinal1(A_221, B_220) | ~v3_ordinal1(B_220) | ~v3_ordinal1(A_221))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.44/2.04  tff(c_16, plain, (![B_12, A_11]: (B_12=A_11 | r2_hidden(A_11, B_12) | ~r2_hidden(A_11, k1_ordinal1(B_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.44/2.04  tff(c_4475, plain, (![B_291, B_290]: (B_291=B_290 | r2_hidden(B_290, B_291) | r1_ordinal1(k1_ordinal1(B_291), B_290) | ~v3_ordinal1(B_290) | ~v3_ordinal1(k1_ordinal1(B_291)))), inference(resolution, [status(thm)], [c_3396, c_16])).
% 5.44/2.04  tff(c_3234, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 5.44/2.04  tff(c_4478, plain, ('#skF_2'='#skF_3' | r2_hidden('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_4475, c_3234])).
% 5.44/2.04  tff(c_4481, plain, ('#skF_2'='#skF_3' | r2_hidden('#skF_3', '#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4478])).
% 5.44/2.04  tff(c_4482, plain, ('#skF_2'='#skF_3' | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_3238, c_4481])).
% 5.44/2.04  tff(c_4483, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_4482])).
% 5.44/2.04  tff(c_4486, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_4483])).
% 5.44/2.04  tff(c_4490, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_4486])).
% 5.44/2.04  tff(c_4491, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_4482])).
% 5.44/2.04  tff(c_3294, plain, (![C_199, B_200, A_201]: (r2_hidden(C_199, B_200) | ~r2_hidden(C_199, A_201) | ~r1_tarski(A_201, B_200))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.44/2.04  tff(c_3305, plain, (![B_200]: (r2_hidden('#skF_2', B_200) | ~r1_tarski('#skF_3', B_200))), inference(resolution, [status(thm)], [c_3235, c_3294])).
% 5.44/2.04  tff(c_3307, plain, (![B_202]: (r2_hidden('#skF_2', B_202) | ~r1_tarski('#skF_3', B_202))), inference(resolution, [status(thm)], [c_3235, c_3294])).
% 5.44/2.04  tff(c_3314, plain, (![B_203]: (~r2_hidden(B_203, '#skF_2') | ~r1_tarski('#skF_3', B_203))), inference(resolution, [status(thm)], [c_3307, c_2])).
% 5.44/2.04  tff(c_3323, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_3305, c_3314])).
% 5.44/2.04  tff(c_4522, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4491, c_3323])).
% 5.44/2.04  tff(c_4534, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3291, c_4522])).
% 5.44/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.44/2.04  
% 5.44/2.04  Inference rules
% 5.44/2.04  ----------------------
% 5.44/2.04  #Ref     : 0
% 5.44/2.04  #Sup     : 914
% 5.44/2.04  #Fact    : 2
% 5.44/2.04  #Define  : 0
% 5.44/2.04  #Split   : 4
% 5.44/2.04  #Chain   : 0
% 5.44/2.04  #Close   : 0
% 5.44/2.04  
% 5.44/2.04  Ordering : KBO
% 5.44/2.04  
% 5.44/2.04  Simplification rules
% 5.44/2.04  ----------------------
% 5.44/2.04  #Subsume      : 234
% 5.44/2.04  #Demod        : 136
% 5.44/2.04  #Tautology    : 70
% 5.44/2.04  #SimpNegUnit  : 3
% 5.44/2.04  #BackRed      : 35
% 5.44/2.04  
% 5.44/2.04  #Partial instantiations: 0
% 5.44/2.04  #Strategies tried      : 1
% 5.44/2.04  
% 5.44/2.04  Timing (in seconds)
% 5.44/2.04  ----------------------
% 5.44/2.05  Preprocessing        : 0.29
% 5.44/2.05  Parsing              : 0.16
% 5.44/2.05  CNF conversion       : 0.02
% 5.44/2.05  Main loop            : 1.00
% 5.44/2.05  Inferencing          : 0.32
% 5.44/2.05  Reduction            : 0.25
% 5.44/2.05  Demodulation         : 0.17
% 5.44/2.05  BG Simplification    : 0.03
% 5.44/2.05  Subsumption          : 0.31
% 5.44/2.05  Abstraction          : 0.04
% 5.44/2.05  MUC search           : 0.00
% 5.44/2.05  Cooper               : 0.00
% 5.44/2.05  Total                : 1.31
% 5.44/2.05  Index Insertion      : 0.00
% 5.44/2.05  Index Deletion       : 0.00
% 5.44/2.05  Index Matching       : 0.00
% 5.44/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
