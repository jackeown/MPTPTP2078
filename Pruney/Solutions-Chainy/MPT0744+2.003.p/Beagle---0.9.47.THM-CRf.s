%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:15 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 132 expanded)
%              Number of leaves         :   22 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  111 ( 287 expanded)
%              Number of equality atoms :    4 (  15 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_36,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_95,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_91,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ! [C] :
              ( v3_ordinal1(C)
             => ( ( r1_tarski(A,B)
                  & r2_hidden(B,C) )
               => r2_hidden(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_34,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_32,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_42,plain,
    ( r2_hidden('#skF_1',k1_ordinal1('#skF_2'))
    | r1_ordinal1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_63,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ r1_ordinal1(A_7,B_8)
      | ~ v3_ordinal1(B_8)
      | ~ v3_ordinal1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_44,plain,(
    ! [A_26] :
      ( v1_ordinal1(A_26)
      | ~ v3_ordinal1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_52,plain,(
    v1_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_44])).

tff(c_30,plain,(
    ! [A_24] :
      ( v3_ordinal1(k1_ordinal1(A_24))
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_170,plain,(
    ! [B_52,A_53] :
      ( r2_hidden(B_52,A_53)
      | r1_ordinal1(A_53,B_52)
      | ~ v3_ordinal1(B_52)
      | ~ v3_ordinal1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_36,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_100,plain,(
    ~ r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_36])).

tff(c_199,plain,
    ( r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_170,c_100])).

tff(c_220,plain,
    ( r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_199])).

tff(c_224,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_227,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_224])).

tff(c_231,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_227])).

tff(c_233,plain,(
    v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_20,plain,(
    ! [B_11] : r2_hidden(B_11,k1_ordinal1(B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_318,plain,(
    ! [A_66,C_67,B_68] :
      ( r2_hidden(A_66,C_67)
      | ~ r2_hidden(B_68,C_67)
      | ~ r1_tarski(A_66,B_68)
      | ~ v3_ordinal1(C_67)
      | ~ v3_ordinal1(B_68)
      | ~ v1_ordinal1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_395,plain,(
    ! [A_81,B_82] :
      ( r2_hidden(A_81,k1_ordinal1(B_82))
      | ~ r1_tarski(A_81,B_82)
      | ~ v3_ordinal1(k1_ordinal1(B_82))
      | ~ v3_ordinal1(B_82)
      | ~ v1_ordinal1(A_81) ) ),
    inference(resolution,[status(thm)],[c_20,c_318])).

tff(c_452,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1('#skF_2')
    | ~ v1_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_395,c_100])).

tff(c_479,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_32,c_233,c_452])).

tff(c_485,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_479])).

tff(c_489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_63,c_485])).

tff(c_491,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_640,plain,(
    ! [B_112,A_113] :
      ( r2_hidden(B_112,A_113)
      | r1_ordinal1(A_113,B_112)
      | ~ v3_ordinal1(B_112)
      | ~ v3_ordinal1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_490,plain,(
    r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_583,plain,(
    ! [B_102,A_103] :
      ( B_102 = A_103
      | r2_hidden(A_103,B_102)
      | ~ r2_hidden(A_103,k1_ordinal1(B_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_594,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_490,c_583])).

tff(c_597,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_594])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_606,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_597,c_2])).

tff(c_658,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_640,c_606])).

tff(c_697,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_658])).

tff(c_699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_491,c_697])).

tff(c_700,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_594])).

tff(c_705,plain,(
    ~ r1_ordinal1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_700,c_491])).

tff(c_772,plain,(
    ! [B_126,A_127] :
      ( r2_hidden(B_126,A_127)
      | r1_ordinal1(A_127,B_126)
      | ~ v3_ordinal1(B_126)
      | ~ v3_ordinal1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_701,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_594])).

tff(c_717,plain,(
    ~ r2_hidden('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_700,c_701])).

tff(c_790,plain,
    ( r1_ordinal1('#skF_1','#skF_1')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_772,c_717])).

tff(c_826,plain,(
    r1_ordinal1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_790])).

tff(c_828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_705,c_826])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n009.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 18:22:11 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.40  
% 2.79/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.40  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 2.79/1.40  
% 2.79/1.40  %Foreground sorts:
% 2.79/1.40  
% 2.79/1.40  
% 2.79/1.40  %Background operators:
% 2.79/1.40  
% 2.79/1.40  
% 2.79/1.40  %Foreground operators:
% 2.79/1.40  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.79/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.79/1.40  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.79/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.40  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.79/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.40  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.79/1.40  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.79/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.79/1.40  
% 2.79/1.42  tff(f_105, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 2.79/1.42  tff(f_54, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.79/1.42  tff(f_36, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 2.79/1.42  tff(f_95, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 2.79/1.42  tff(f_91, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 2.79/1.42  tff(f_62, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 2.79/1.42  tff(f_76, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (![C]: (v3_ordinal1(C) => ((r1_tarski(A, B) & r2_hidden(B, C)) => r2_hidden(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_ordinal1)).
% 2.79/1.42  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 2.79/1.42  tff(c_34, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.79/1.42  tff(c_32, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.79/1.42  tff(c_42, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2')) | r1_ordinal1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.79/1.42  tff(c_63, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_42])).
% 2.79/1.42  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~r1_ordinal1(A_7, B_8) | ~v3_ordinal1(B_8) | ~v3_ordinal1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.79/1.42  tff(c_44, plain, (![A_26]: (v1_ordinal1(A_26) | ~v3_ordinal1(A_26))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.79/1.42  tff(c_52, plain, (v1_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_34, c_44])).
% 2.79/1.42  tff(c_30, plain, (![A_24]: (v3_ordinal1(k1_ordinal1(A_24)) | ~v3_ordinal1(A_24))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.79/1.42  tff(c_170, plain, (![B_52, A_53]: (r2_hidden(B_52, A_53) | r1_ordinal1(A_53, B_52) | ~v3_ordinal1(B_52) | ~v3_ordinal1(A_53))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.79/1.42  tff(c_36, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.79/1.42  tff(c_100, plain, (~r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_36])).
% 2.79/1.42  tff(c_199, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_170, c_100])).
% 2.79/1.42  tff(c_220, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_199])).
% 2.79/1.42  tff(c_224, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_220])).
% 2.79/1.42  tff(c_227, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_224])).
% 2.79/1.42  tff(c_231, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_227])).
% 2.79/1.42  tff(c_233, plain, (v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_220])).
% 2.79/1.42  tff(c_20, plain, (![B_11]: (r2_hidden(B_11, k1_ordinal1(B_11)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.79/1.42  tff(c_318, plain, (![A_66, C_67, B_68]: (r2_hidden(A_66, C_67) | ~r2_hidden(B_68, C_67) | ~r1_tarski(A_66, B_68) | ~v3_ordinal1(C_67) | ~v3_ordinal1(B_68) | ~v1_ordinal1(A_66))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.79/1.42  tff(c_395, plain, (![A_81, B_82]: (r2_hidden(A_81, k1_ordinal1(B_82)) | ~r1_tarski(A_81, B_82) | ~v3_ordinal1(k1_ordinal1(B_82)) | ~v3_ordinal1(B_82) | ~v1_ordinal1(A_81))), inference(resolution, [status(thm)], [c_20, c_318])).
% 2.79/1.42  tff(c_452, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_2')) | ~v3_ordinal1('#skF_2') | ~v1_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_395, c_100])).
% 2.79/1.42  tff(c_479, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_32, c_233, c_452])).
% 2.79/1.42  tff(c_485, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_14, c_479])).
% 2.79/1.42  tff(c_489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_63, c_485])).
% 2.79/1.42  tff(c_491, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 2.79/1.42  tff(c_640, plain, (![B_112, A_113]: (r2_hidden(B_112, A_113) | r1_ordinal1(A_113, B_112) | ~v3_ordinal1(B_112) | ~v3_ordinal1(A_113))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.79/1.42  tff(c_490, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_42])).
% 2.79/1.42  tff(c_583, plain, (![B_102, A_103]: (B_102=A_103 | r2_hidden(A_103, B_102) | ~r2_hidden(A_103, k1_ordinal1(B_102)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.79/1.42  tff(c_594, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_490, c_583])).
% 2.79/1.42  tff(c_597, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_594])).
% 2.79/1.42  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.79/1.42  tff(c_606, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_597, c_2])).
% 2.79/1.42  tff(c_658, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_640, c_606])).
% 2.79/1.42  tff(c_697, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_658])).
% 2.79/1.42  tff(c_699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_491, c_697])).
% 2.79/1.42  tff(c_700, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_594])).
% 2.79/1.42  tff(c_705, plain, (~r1_ordinal1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_700, c_491])).
% 2.79/1.42  tff(c_772, plain, (![B_126, A_127]: (r2_hidden(B_126, A_127) | r1_ordinal1(A_127, B_126) | ~v3_ordinal1(B_126) | ~v3_ordinal1(A_127))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.79/1.42  tff(c_701, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_594])).
% 2.79/1.42  tff(c_717, plain, (~r2_hidden('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_700, c_701])).
% 2.79/1.42  tff(c_790, plain, (r1_ordinal1('#skF_1', '#skF_1') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_772, c_717])).
% 2.79/1.42  tff(c_826, plain, (r1_ordinal1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_790])).
% 2.79/1.42  tff(c_828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_705, c_826])).
% 2.79/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.42  
% 2.79/1.42  Inference rules
% 2.79/1.42  ----------------------
% 2.79/1.42  #Ref     : 0
% 2.79/1.42  #Sup     : 151
% 2.79/1.42  #Fact    : 4
% 2.79/1.42  #Define  : 0
% 2.79/1.42  #Split   : 3
% 2.79/1.42  #Chain   : 0
% 2.79/1.42  #Close   : 0
% 2.79/1.42  
% 2.79/1.42  Ordering : KBO
% 2.79/1.42  
% 2.79/1.42  Simplification rules
% 2.79/1.42  ----------------------
% 2.79/1.42  #Subsume      : 17
% 2.79/1.42  #Demod        : 32
% 2.79/1.42  #Tautology    : 26
% 2.79/1.42  #SimpNegUnit  : 2
% 2.79/1.42  #BackRed      : 6
% 2.79/1.42  
% 2.79/1.42  #Partial instantiations: 0
% 2.79/1.42  #Strategies tried      : 1
% 2.79/1.42  
% 2.79/1.42  Timing (in seconds)
% 2.79/1.42  ----------------------
% 2.79/1.42  Preprocessing        : 0.30
% 2.79/1.42  Parsing              : 0.17
% 2.79/1.42  CNF conversion       : 0.02
% 2.79/1.42  Main loop            : 0.35
% 2.79/1.42  Inferencing          : 0.14
% 2.79/1.42  Reduction            : 0.08
% 2.79/1.42  Demodulation         : 0.06
% 2.79/1.42  BG Simplification    : 0.02
% 2.79/1.42  Subsumption          : 0.09
% 2.79/1.42  Abstraction          : 0.01
% 2.79/1.42  MUC search           : 0.00
% 2.79/1.42  Cooper               : 0.00
% 2.79/1.42  Total                : 0.68
% 2.79/1.42  Index Insertion      : 0.00
% 2.79/1.42  Index Deletion       : 0.00
% 2.79/1.42  Index Matching       : 0.00
% 2.79/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
