%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:18 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 117 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  100 ( 252 expanded)
%              Number of equality atoms :    4 (  14 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v1_xboole_0 > #nlpp > k1_ordinal1 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_37,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( ~ v1_xboole_0(k1_ordinal1(A))
        & v3_ordinal1(k1_ordinal1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_ordinal1)).

tff(f_62,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_71,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
          <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_76,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

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

tff(c_30,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_54,plain,(
    ~ r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,
    ( r2_hidden('#skF_1',k1_ordinal1('#skF_2'))
    | r1_ordinal1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_55,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_38])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ r1_ordinal1(A_4,B_5)
      | ~ v3_ordinal1(B_5)
      | ~ v3_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_3] :
      ( v3_ordinal1(k1_ordinal1(A_3))
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_107,plain,(
    ! [B_37,A_38] :
      ( r2_hidden(B_37,A_38)
      | r1_ordinal1(A_38,B_37)
      | ~ v3_ordinal1(B_37)
      | ~ v3_ordinal1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_129,plain,
    ( r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_107,c_54])).

tff(c_148,plain,
    ( r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_129])).

tff(c_152,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_155,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_152])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_155])).

tff(c_160,plain,(
    r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_276,plain,(
    ! [A_57,B_58] :
      ( r2_hidden(A_57,B_58)
      | ~ r1_ordinal1(k1_ordinal1(A_57),B_58)
      | ~ v3_ordinal1(B_58)
      | ~ v3_ordinal1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_286,plain,
    ( r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_160,c_276])).

tff(c_291,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_286])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_303,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_291,c_26])).

tff(c_307,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_303])).

tff(c_311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_55,c_307])).

tff(c_312,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_370,plain,(
    ! [B_65,A_66] :
      ( r2_hidden(B_65,A_66)
      | r1_ordinal1(A_66,B_65)
      | ~ v3_ordinal1(B_65)
      | ~ v3_ordinal1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_313,plain,(
    r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_342,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | r2_hidden(A_63,B_62)
      | ~ r2_hidden(A_63,k1_ordinal1(B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_353,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_313,c_342])).

tff(c_356,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_353])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_363,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_356,c_2])).

tff(c_377,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_370,c_363])).

tff(c_401,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_377])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_401])).

tff(c_404,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_409,plain,(
    ~ r1_ordinal1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_312])).

tff(c_418,plain,(
    ! [B_67,A_68] :
      ( r2_hidden(B_67,A_68)
      | r1_ordinal1(A_68,B_67)
      | ~ v3_ordinal1(B_67)
      | ~ v3_ordinal1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_405,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_417,plain,(
    ~ r2_hidden('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_405])).

tff(c_421,plain,
    ( r1_ordinal1('#skF_1','#skF_1')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_418,c_417])).

tff(c_441,plain,(
    r1_ordinal1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_421])).

tff(c_443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_409,c_441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:44:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.31  
% 2.24/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.31  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v1_xboole_0 > #nlpp > k1_ordinal1 > #skF_2 > #skF_1
% 2.24/1.31  
% 2.24/1.31  %Foreground sorts:
% 2.24/1.31  
% 2.24/1.31  
% 2.24/1.31  %Background operators:
% 2.24/1.31  
% 2.24/1.31  
% 2.24/1.31  %Foreground operators:
% 2.24/1.31  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.31  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.24/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.31  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.24/1.31  
% 2.57/1.33  tff(f_86, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 2.57/1.33  tff(f_45, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.57/1.33  tff(f_37, axiom, (![A]: (v3_ordinal1(A) => (~v1_xboole_0(k1_ordinal1(A)) & v3_ordinal1(k1_ordinal1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_ordinal1)).
% 2.57/1.33  tff(f_62, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 2.57/1.33  tff(f_71, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 2.57/1.33  tff(f_76, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.57/1.33  tff(f_53, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 2.57/1.33  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 2.57/1.33  tff(c_30, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.57/1.33  tff(c_28, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.57/1.33  tff(c_32, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.57/1.33  tff(c_54, plain, (~r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.57/1.33  tff(c_38, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2')) | r1_ordinal1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.57/1.33  tff(c_55, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_38])).
% 2.57/1.33  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~r1_ordinal1(A_4, B_5) | ~v3_ordinal1(B_5) | ~v3_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.57/1.33  tff(c_4, plain, (![A_3]: (v3_ordinal1(k1_ordinal1(A_3)) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.57/1.33  tff(c_107, plain, (![B_37, A_38]: (r2_hidden(B_37, A_38) | r1_ordinal1(A_38, B_37) | ~v3_ordinal1(B_37) | ~v3_ordinal1(A_38))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.57/1.33  tff(c_129, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_107, c_54])).
% 2.57/1.33  tff(c_148, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_129])).
% 2.57/1.33  tff(c_152, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_148])).
% 2.57/1.33  tff(c_155, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_4, c_152])).
% 2.57/1.33  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_155])).
% 2.57/1.33  tff(c_160, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_148])).
% 2.57/1.33  tff(c_276, plain, (![A_57, B_58]: (r2_hidden(A_57, B_58) | ~r1_ordinal1(k1_ordinal1(A_57), B_58) | ~v3_ordinal1(B_58) | ~v3_ordinal1(A_57))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.57/1.33  tff(c_286, plain, (r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_160, c_276])).
% 2.57/1.33  tff(c_291, plain, (r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_286])).
% 2.57/1.33  tff(c_26, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.57/1.33  tff(c_303, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_291, c_26])).
% 2.57/1.33  tff(c_307, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_303])).
% 2.57/1.33  tff(c_311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_55, c_307])).
% 2.57/1.33  tff(c_312, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_32])).
% 2.57/1.33  tff(c_370, plain, (![B_65, A_66]: (r2_hidden(B_65, A_66) | r1_ordinal1(A_66, B_65) | ~v3_ordinal1(B_65) | ~v3_ordinal1(A_66))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.57/1.33  tff(c_313, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_32])).
% 2.57/1.33  tff(c_342, plain, (![B_62, A_63]: (B_62=A_63 | r2_hidden(A_63, B_62) | ~r2_hidden(A_63, k1_ordinal1(B_62)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.57/1.33  tff(c_353, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_313, c_342])).
% 2.57/1.33  tff(c_356, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_353])).
% 2.57/1.33  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.57/1.33  tff(c_363, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_356, c_2])).
% 2.57/1.33  tff(c_377, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_370, c_363])).
% 2.57/1.33  tff(c_401, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_377])).
% 2.57/1.33  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_312, c_401])).
% 2.57/1.33  tff(c_404, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_353])).
% 2.57/1.33  tff(c_409, plain, (~r1_ordinal1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_404, c_312])).
% 2.57/1.33  tff(c_418, plain, (![B_67, A_68]: (r2_hidden(B_67, A_68) | r1_ordinal1(A_68, B_67) | ~v3_ordinal1(B_67) | ~v3_ordinal1(A_68))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.57/1.33  tff(c_405, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_353])).
% 2.57/1.33  tff(c_417, plain, (~r2_hidden('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_404, c_405])).
% 2.57/1.33  tff(c_421, plain, (r1_ordinal1('#skF_1', '#skF_1') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_418, c_417])).
% 2.57/1.33  tff(c_441, plain, (r1_ordinal1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_421])).
% 2.57/1.33  tff(c_443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_409, c_441])).
% 2.57/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.33  
% 2.57/1.33  Inference rules
% 2.57/1.33  ----------------------
% 2.57/1.33  #Ref     : 0
% 2.57/1.33  #Sup     : 79
% 2.57/1.33  #Fact    : 0
% 2.57/1.33  #Define  : 0
% 2.57/1.33  #Split   : 3
% 2.57/1.33  #Chain   : 0
% 2.57/1.33  #Close   : 0
% 2.57/1.33  
% 2.57/1.33  Ordering : KBO
% 2.57/1.33  
% 2.57/1.33  Simplification rules
% 2.57/1.33  ----------------------
% 2.57/1.33  #Subsume      : 7
% 2.57/1.33  #Demod        : 27
% 2.57/1.33  #Tautology    : 15
% 2.57/1.33  #SimpNegUnit  : 4
% 2.57/1.33  #BackRed      : 5
% 2.57/1.33  
% 2.57/1.33  #Partial instantiations: 0
% 2.57/1.33  #Strategies tried      : 1
% 2.57/1.33  
% 2.57/1.33  Timing (in seconds)
% 2.57/1.33  ----------------------
% 2.57/1.33  Preprocessing        : 0.28
% 2.57/1.33  Parsing              : 0.15
% 2.57/1.33  CNF conversion       : 0.02
% 2.57/1.33  Main loop            : 0.25
% 2.57/1.33  Inferencing          : 0.10
% 2.57/1.33  Reduction            : 0.06
% 2.57/1.33  Demodulation         : 0.04
% 2.57/1.33  BG Simplification    : 0.02
% 2.57/1.33  Subsumption          : 0.06
% 2.57/1.33  Abstraction          : 0.01
% 2.57/1.33  MUC search           : 0.00
% 2.57/1.33  Cooper               : 0.00
% 2.57/1.33  Total                : 0.56
% 2.57/1.33  Index Insertion      : 0.00
% 2.57/1.33  Index Deletion       : 0.00
% 2.57/1.33  Index Matching       : 0.00
% 2.57/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
