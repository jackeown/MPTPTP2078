%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:34 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 152 expanded)
%              Number of leaves         :   23 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  129 ( 421 expanded)
%              Number of equality atoms :   36 ( 154 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ! [D] :
                ( v1_relat_1(D)
               => ( ( r1_tarski(k2_relat_1(B),A)
                    & k5_relat_1(B,C) = k6_relat_1(k1_relat_1(D))
                    & k5_relat_1(C,D) = k6_relat_1(A) )
                 => D = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(c_30,plain,(
    '#skF_2' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    k6_relat_1(k1_relat_1('#skF_4')) = k5_relat_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_70,plain,(
    k2_relat_1(k5_relat_1('#skF_2','#skF_3')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_20])).

tff(c_215,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_42,B_43)),k2_relat_1(B_43))
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_232,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_215])).

tff(c_249,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_232])).

tff(c_293,plain,(
    ! [B_48,A_49] :
      ( k2_relat_1(k5_relat_1(B_48,A_49)) = k2_relat_1(A_49)
      | ~ r1_tarski(k1_relat_1(A_49),k2_relat_1(B_48))
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_296,plain,
    ( k2_relat_1(k5_relat_1('#skF_3','#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_249,c_293])).

tff(c_311,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_20,c_32,c_296])).

tff(c_238,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_215])).

tff(c_251,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_20,c_238])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_270,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_251,c_2])).

tff(c_274,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_314,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_274])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_314])).

tff(c_319,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_373,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k2_relat_1(A_51),k2_relat_1(B_52))
      | ~ r1_tarski(A_51,B_52)
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_378,plain,(
    ! [B_52] :
      ( r1_tarski('#skF_1',k2_relat_1(B_52))
      | ~ r1_tarski('#skF_4',B_52)
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_373])).

tff(c_399,plain,(
    ! [B_53] :
      ( r1_tarski('#skF_1',k2_relat_1(B_53))
      | ~ r1_tarski('#skF_4',B_53)
      | ~ v1_relat_1(B_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_378])).

tff(c_36,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_150,plain,(
    ! [B_37,A_38] :
      ( B_37 = A_38
      | ~ r1_tarski(B_37,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_150])).

tff(c_166,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_402,plain,
    ( ~ r1_tarski('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_399,c_166])).

tff(c_416,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_402])).

tff(c_718,plain,(
    ! [A_75,B_76,C_77] :
      ( k5_relat_1(k5_relat_1(A_75,B_76),C_77) = k5_relat_1(A_75,k5_relat_1(B_76,C_77))
      | ~ v1_relat_1(C_77)
      | ~ v1_relat_1(B_76)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_91,plain,(
    ! [A_35] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_35)),A_35) = A_35
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_110,plain,
    ( k5_relat_1(k5_relat_1('#skF_2','#skF_3'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_91])).

tff(c_120,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_3'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_110])).

tff(c_754,plain,
    ( k5_relat_1('#skF_2',k5_relat_1('#skF_3','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_718,c_120])).

tff(c_800,plain,(
    k5_relat_1('#skF_2',k6_relat_1('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_32,c_754])).

tff(c_24,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k5_relat_1(B_21,k6_relat_1(A_20)),B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_825,plain,
    ( r1_tarski('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_800,c_24])).

tff(c_838,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_825])).

tff(c_840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_416,c_838])).

tff(c_841,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_28,plain,(
    ! [A_23] :
      ( k5_relat_1(A_23,k6_relat_1(k2_relat_1(A_23))) = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_848,plain,
    ( k5_relat_1('#skF_2',k6_relat_1('#skF_1')) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_841,c_28])).

tff(c_852,plain,(
    k5_relat_1('#skF_2',k6_relat_1('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_848])).

tff(c_1581,plain,(
    ! [A_121,B_122,C_123] :
      ( k5_relat_1(k5_relat_1(A_121,B_122),C_123) = k5_relat_1(A_121,k5_relat_1(B_122,C_123))
      | ~ v1_relat_1(C_123)
      | ~ v1_relat_1(B_122)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1617,plain,
    ( k5_relat_1('#skF_2',k5_relat_1('#skF_3','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1581,c_120])).

tff(c_1670,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_852,c_32,c_1617])).

tff(c_1672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1670])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.59  
% 3.56/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.59  %$ r1_tarski > v1_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.56/1.59  
% 3.56/1.59  %Foreground sorts:
% 3.56/1.59  
% 3.56/1.59  
% 3.56/1.59  %Background operators:
% 3.56/1.59  
% 3.56/1.59  
% 3.56/1.59  %Foreground operators:
% 3.56/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.56/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.56/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.56/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.56/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.56/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.56/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.56/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.56/1.59  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.56/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.56/1.59  
% 3.56/1.61  tff(f_103, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => (((r1_tarski(k2_relat_1(B), A) & (k5_relat_1(B, C) = k6_relat_1(k1_relat_1(D)))) & (k5_relat_1(C, D) = k6_relat_1(A))) => (D = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_relat_1)).
% 3.56/1.61  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.56/1.61  tff(f_72, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.56/1.61  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.56/1.61  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 3.56/1.61  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 3.56/1.61  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 3.56/1.61  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 3.56/1.61  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 3.56/1.61  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 3.56/1.61  tff(c_30, plain, ('#skF_2'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.56/1.61  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.56/1.61  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.56/1.61  tff(c_38, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.56/1.61  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.61  tff(c_20, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.56/1.61  tff(c_32, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.56/1.61  tff(c_34, plain, (k6_relat_1(k1_relat_1('#skF_4'))=k5_relat_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.56/1.61  tff(c_70, plain, (k2_relat_1(k5_relat_1('#skF_2', '#skF_3'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_34, c_20])).
% 3.56/1.61  tff(c_215, plain, (![A_42, B_43]: (r1_tarski(k2_relat_1(k5_relat_1(A_42, B_43)), k2_relat_1(B_43)) | ~v1_relat_1(B_43) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.56/1.61  tff(c_232, plain, (r1_tarski(k1_relat_1('#skF_4'), k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_70, c_215])).
% 3.56/1.61  tff(c_249, plain, (r1_tarski(k1_relat_1('#skF_4'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_232])).
% 3.56/1.61  tff(c_293, plain, (![B_48, A_49]: (k2_relat_1(k5_relat_1(B_48, A_49))=k2_relat_1(A_49) | ~r1_tarski(k1_relat_1(A_49), k2_relat_1(B_48)) | ~v1_relat_1(B_48) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.56/1.61  tff(c_296, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_4'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_249, c_293])).
% 3.56/1.61  tff(c_311, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_20, c_32, c_296])).
% 3.56/1.61  tff(c_238, plain, (r1_tarski(k2_relat_1(k6_relat_1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_215])).
% 3.56/1.61  tff(c_251, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_20, c_238])).
% 3.56/1.61  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.61  tff(c_270, plain, (k2_relat_1('#skF_4')='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_251, c_2])).
% 3.56/1.61  tff(c_274, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_270])).
% 3.56/1.61  tff(c_314, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_311, c_274])).
% 3.56/1.61  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_314])).
% 3.56/1.61  tff(c_319, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_270])).
% 3.56/1.61  tff(c_373, plain, (![A_51, B_52]: (r1_tarski(k2_relat_1(A_51), k2_relat_1(B_52)) | ~r1_tarski(A_51, B_52) | ~v1_relat_1(B_52) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.56/1.61  tff(c_378, plain, (![B_52]: (r1_tarski('#skF_1', k2_relat_1(B_52)) | ~r1_tarski('#skF_4', B_52) | ~v1_relat_1(B_52) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_319, c_373])).
% 3.56/1.61  tff(c_399, plain, (![B_53]: (r1_tarski('#skF_1', k2_relat_1(B_53)) | ~r1_tarski('#skF_4', B_53) | ~v1_relat_1(B_53))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_378])).
% 3.56/1.61  tff(c_36, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.56/1.61  tff(c_150, plain, (![B_37, A_38]: (B_37=A_38 | ~r1_tarski(B_37, A_38) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.61  tff(c_161, plain, (k2_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_150])).
% 3.56/1.61  tff(c_166, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_161])).
% 3.56/1.61  tff(c_402, plain, (~r1_tarski('#skF_4', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_399, c_166])).
% 3.56/1.61  tff(c_416, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_402])).
% 3.56/1.61  tff(c_718, plain, (![A_75, B_76, C_77]: (k5_relat_1(k5_relat_1(A_75, B_76), C_77)=k5_relat_1(A_75, k5_relat_1(B_76, C_77)) | ~v1_relat_1(C_77) | ~v1_relat_1(B_76) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.56/1.61  tff(c_91, plain, (![A_35]: (k5_relat_1(k6_relat_1(k1_relat_1(A_35)), A_35)=A_35 | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.56/1.61  tff(c_110, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_34, c_91])).
% 3.56/1.61  tff(c_120, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_110])).
% 3.56/1.61  tff(c_754, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_3', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_718, c_120])).
% 3.56/1.61  tff(c_800, plain, (k5_relat_1('#skF_2', k6_relat_1('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_32, c_754])).
% 3.56/1.61  tff(c_24, plain, (![B_21, A_20]: (r1_tarski(k5_relat_1(B_21, k6_relat_1(A_20)), B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.56/1.61  tff(c_825, plain, (r1_tarski('#skF_4', '#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_800, c_24])).
% 3.56/1.61  tff(c_838, plain, (r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_825])).
% 3.56/1.61  tff(c_840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_416, c_838])).
% 3.56/1.61  tff(c_841, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_161])).
% 3.56/1.61  tff(c_28, plain, (![A_23]: (k5_relat_1(A_23, k6_relat_1(k2_relat_1(A_23)))=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.56/1.61  tff(c_848, plain, (k5_relat_1('#skF_2', k6_relat_1('#skF_1'))='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_841, c_28])).
% 3.56/1.61  tff(c_852, plain, (k5_relat_1('#skF_2', k6_relat_1('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_848])).
% 3.56/1.61  tff(c_1581, plain, (![A_121, B_122, C_123]: (k5_relat_1(k5_relat_1(A_121, B_122), C_123)=k5_relat_1(A_121, k5_relat_1(B_122, C_123)) | ~v1_relat_1(C_123) | ~v1_relat_1(B_122) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.56/1.61  tff(c_1617, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_3', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1581, c_120])).
% 3.56/1.61  tff(c_1670, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_852, c_32, c_1617])).
% 3.56/1.61  tff(c_1672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1670])).
% 3.56/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.61  
% 3.56/1.61  Inference rules
% 3.56/1.61  ----------------------
% 3.56/1.61  #Ref     : 0
% 3.56/1.61  #Sup     : 379
% 3.56/1.61  #Fact    : 0
% 3.56/1.61  #Define  : 0
% 3.56/1.61  #Split   : 11
% 3.56/1.61  #Chain   : 0
% 3.56/1.61  #Close   : 0
% 3.56/1.61  
% 3.56/1.61  Ordering : KBO
% 3.56/1.61  
% 3.56/1.61  Simplification rules
% 3.56/1.61  ----------------------
% 3.56/1.61  #Subsume      : 70
% 3.56/1.61  #Demod        : 420
% 3.56/1.61  #Tautology    : 131
% 3.56/1.61  #SimpNegUnit  : 3
% 3.56/1.61  #BackRed      : 7
% 3.56/1.61  
% 3.56/1.61  #Partial instantiations: 0
% 3.56/1.61  #Strategies tried      : 1
% 3.56/1.61  
% 3.56/1.61  Timing (in seconds)
% 3.56/1.61  ----------------------
% 3.56/1.61  Preprocessing        : 0.32
% 3.56/1.61  Parsing              : 0.17
% 3.56/1.61  CNF conversion       : 0.02
% 3.56/1.61  Main loop            : 0.53
% 3.56/1.61  Inferencing          : 0.18
% 3.56/1.61  Reduction            : 0.19
% 3.56/1.61  Demodulation         : 0.13
% 3.56/1.61  BG Simplification    : 0.02
% 3.56/1.61  Subsumption          : 0.11
% 3.56/1.61  Abstraction          : 0.03
% 3.56/1.61  MUC search           : 0.00
% 3.56/1.61  Cooper               : 0.00
% 3.56/1.61  Total                : 0.88
% 3.56/1.61  Index Insertion      : 0.00
% 3.56/1.61  Index Deletion       : 0.00
% 3.56/1.61  Index Matching       : 0.00
% 3.56/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
