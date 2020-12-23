%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:40 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 138 expanded)
%              Number of leaves         :   28 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :   97 ( 264 expanded)
%              Number of equality atoms :   14 (  53 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k10_relat_1(B,A),k10_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_257,plain,(
    ! [A_60,B_61] :
      ( k5_relat_1(k6_relat_1(A_60),B_61) = k7_relat_1(B_61,A_60)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_25),B_26),B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_498,plain,(
    ! [B_73,A_74] :
      ( r1_tarski(k7_relat_1(B_73,A_74),B_73)
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_28])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_535,plain,(
    ! [A_77,B_78,A_79] :
      ( r1_tarski(A_77,B_78)
      | ~ r1_tarski(A_77,k7_relat_1(B_78,A_79))
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_498,c_8])).

tff(c_555,plain,(
    ! [B_78,A_79] :
      ( r1_tarski(k7_relat_1(B_78,A_79),B_78)
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_6,c_535])).

tff(c_22,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(k7_relat_1(B_19,A_18)) = k9_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k7_relat_1(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_391,plain,(
    ! [B_68,A_69] :
      ( k1_relat_1(k7_relat_1(B_68,A_69)) = A_69
      | ~ r1_tarski(A_69,k1_relat_1(B_68))
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_405,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_391])).

tff(c_417,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_405])).

tff(c_450,plain,(
    ! [B_71] :
      ( k1_relat_1(k7_relat_1(B_71,k1_relat_1(B_71))) = k1_relat_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(resolution,[status(thm)],[c_6,c_391])).

tff(c_479,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_450])).

tff(c_486,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_479])).

tff(c_694,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_486])).

tff(c_697,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_694])).

tff(c_701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_697])).

tff(c_703,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_486])).

tff(c_24,plain,(
    ! [A_20] :
      ( k10_relat_1(A_20,k2_relat_1(A_20)) = k1_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_604,plain,(
    ! [B_84,A_85,C_86] :
      ( r1_tarski(k10_relat_1(B_84,A_85),k10_relat_1(C_86,A_85))
      | ~ r1_tarski(B_84,C_86)
      | ~ v1_relat_1(C_86)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1471,plain,(
    ! [A_151,C_152] :
      ( r1_tarski(k1_relat_1(A_151),k10_relat_1(C_152,k2_relat_1(A_151)))
      | ~ r1_tarski(A_151,C_152)
      | ~ v1_relat_1(C_152)
      | ~ v1_relat_1(A_151)
      | ~ v1_relat_1(A_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_604])).

tff(c_1502,plain,(
    ! [C_152] :
      ( r1_tarski('#skF_1',k10_relat_1(C_152,k2_relat_1(k7_relat_1('#skF_2','#skF_1'))))
      | ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),C_152)
      | ~ v1_relat_1(C_152)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_1471])).

tff(c_1565,plain,(
    ! [C_155] :
      ( r1_tarski('#skF_1',k10_relat_1(C_155,k2_relat_1(k7_relat_1('#skF_2','#skF_1'))))
      | ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),C_155)
      | ~ v1_relat_1(C_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_703,c_703,c_1502])).

tff(c_1577,plain,(
    ! [C_155] :
      ( r1_tarski('#skF_1',k10_relat_1(C_155,k9_relat_1('#skF_2','#skF_1')))
      | ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),C_155)
      | ~ v1_relat_1(C_155)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1565])).

tff(c_1612,plain,(
    ! [C_159] :
      ( r1_tarski('#skF_1',k10_relat_1(C_159,k9_relat_1('#skF_2','#skF_1')))
      | ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),C_159)
      | ~ v1_relat_1(C_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1577])).

tff(c_36,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1624,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1612,c_36])).

tff(c_1632,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1624])).

tff(c_1635,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_555,c_1632])).

tff(c_1639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1635])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n003.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 10:41:12 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.63/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.60  
% 3.63/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.61  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.63/1.61  
% 3.63/1.61  %Foreground sorts:
% 3.63/1.61  
% 3.63/1.61  
% 3.63/1.61  %Background operators:
% 3.63/1.61  
% 3.63/1.61  
% 3.63/1.61  %Foreground operators:
% 3.63/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.63/1.61  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.63/1.61  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.63/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.63/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.63/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.63/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.63/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.63/1.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.63/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.63/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.63/1.61  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.63/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.63/1.61  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.63/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.63/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.63/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.63/1.61  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.63/1.61  
% 3.63/1.62  tff(f_95, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 3.63/1.62  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.63/1.62  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.63/1.62  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 3.63/1.62  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.63/1.62  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.63/1.62  tff(f_51, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.63/1.62  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 3.63/1.62  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.63/1.62  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k10_relat_1(B, A), k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t179_relat_1)).
% 3.63/1.62  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.63/1.62  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.63/1.62  tff(c_257, plain, (![A_60, B_61]: (k5_relat_1(k6_relat_1(A_60), B_61)=k7_relat_1(B_61, A_60) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.63/1.62  tff(c_28, plain, (![A_25, B_26]: (r1_tarski(k5_relat_1(k6_relat_1(A_25), B_26), B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.63/1.62  tff(c_498, plain, (![B_73, A_74]: (r1_tarski(k7_relat_1(B_73, A_74), B_73) | ~v1_relat_1(B_73) | ~v1_relat_1(B_73))), inference(superposition, [status(thm), theory('equality')], [c_257, c_28])).
% 3.63/1.62  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.63/1.62  tff(c_535, plain, (![A_77, B_78, A_79]: (r1_tarski(A_77, B_78) | ~r1_tarski(A_77, k7_relat_1(B_78, A_79)) | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_498, c_8])).
% 3.63/1.62  tff(c_555, plain, (![B_78, A_79]: (r1_tarski(k7_relat_1(B_78, A_79), B_78) | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_6, c_535])).
% 3.63/1.62  tff(c_22, plain, (![B_19, A_18]: (k2_relat_1(k7_relat_1(B_19, A_18))=k9_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.63/1.62  tff(c_18, plain, (![A_14, B_15]: (v1_relat_1(k7_relat_1(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.63/1.62  tff(c_38, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.63/1.62  tff(c_391, plain, (![B_68, A_69]: (k1_relat_1(k7_relat_1(B_68, A_69))=A_69 | ~r1_tarski(A_69, k1_relat_1(B_68)) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.63/1.62  tff(c_405, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_391])).
% 3.63/1.62  tff(c_417, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_405])).
% 3.63/1.62  tff(c_450, plain, (![B_71]: (k1_relat_1(k7_relat_1(B_71, k1_relat_1(B_71)))=k1_relat_1(B_71) | ~v1_relat_1(B_71))), inference(resolution, [status(thm)], [c_6, c_391])).
% 3.63/1.62  tff(c_479, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_417, c_450])).
% 3.63/1.62  tff(c_486, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))='#skF_1' | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_417, c_479])).
% 3.63/1.62  tff(c_694, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_486])).
% 3.63/1.62  tff(c_697, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_694])).
% 3.63/1.62  tff(c_701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_697])).
% 3.63/1.62  tff(c_703, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_486])).
% 3.63/1.62  tff(c_24, plain, (![A_20]: (k10_relat_1(A_20, k2_relat_1(A_20))=k1_relat_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.63/1.62  tff(c_604, plain, (![B_84, A_85, C_86]: (r1_tarski(k10_relat_1(B_84, A_85), k10_relat_1(C_86, A_85)) | ~r1_tarski(B_84, C_86) | ~v1_relat_1(C_86) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.63/1.62  tff(c_1471, plain, (![A_151, C_152]: (r1_tarski(k1_relat_1(A_151), k10_relat_1(C_152, k2_relat_1(A_151))) | ~r1_tarski(A_151, C_152) | ~v1_relat_1(C_152) | ~v1_relat_1(A_151) | ~v1_relat_1(A_151))), inference(superposition, [status(thm), theory('equality')], [c_24, c_604])).
% 3.63/1.62  tff(c_1502, plain, (![C_152]: (r1_tarski('#skF_1', k10_relat_1(C_152, k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))) | ~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), C_152) | ~v1_relat_1(C_152) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_417, c_1471])).
% 3.63/1.62  tff(c_1565, plain, (![C_155]: (r1_tarski('#skF_1', k10_relat_1(C_155, k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))) | ~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), C_155) | ~v1_relat_1(C_155))), inference(demodulation, [status(thm), theory('equality')], [c_703, c_703, c_1502])).
% 3.63/1.62  tff(c_1577, plain, (![C_155]: (r1_tarski('#skF_1', k10_relat_1(C_155, k9_relat_1('#skF_2', '#skF_1'))) | ~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), C_155) | ~v1_relat_1(C_155) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1565])).
% 3.63/1.62  tff(c_1612, plain, (![C_159]: (r1_tarski('#skF_1', k10_relat_1(C_159, k9_relat_1('#skF_2', '#skF_1'))) | ~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), C_159) | ~v1_relat_1(C_159))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1577])).
% 3.63/1.62  tff(c_36, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.63/1.62  tff(c_1624, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1612, c_36])).
% 3.63/1.62  tff(c_1632, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1624])).
% 3.63/1.62  tff(c_1635, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_555, c_1632])).
% 3.63/1.62  tff(c_1639, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1635])).
% 3.63/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.62  
% 3.63/1.62  Inference rules
% 3.63/1.62  ----------------------
% 3.63/1.62  #Ref     : 0
% 3.63/1.62  #Sup     : 388
% 3.63/1.62  #Fact    : 0
% 3.63/1.62  #Define  : 0
% 3.63/1.62  #Split   : 3
% 3.63/1.62  #Chain   : 0
% 3.63/1.62  #Close   : 0
% 3.63/1.62  
% 3.63/1.62  Ordering : KBO
% 3.63/1.62  
% 3.63/1.62  Simplification rules
% 3.63/1.62  ----------------------
% 3.63/1.62  #Subsume      : 94
% 3.63/1.62  #Demod        : 82
% 3.63/1.62  #Tautology    : 96
% 3.63/1.62  #SimpNegUnit  : 0
% 3.63/1.62  #BackRed      : 0
% 3.63/1.62  
% 3.63/1.62  #Partial instantiations: 0
% 3.63/1.62  #Strategies tried      : 1
% 3.63/1.62  
% 3.63/1.62  Timing (in seconds)
% 3.63/1.62  ----------------------
% 3.63/1.62  Preprocessing        : 0.32
% 3.63/1.62  Parsing              : 0.17
% 3.63/1.62  CNF conversion       : 0.02
% 3.63/1.62  Main loop            : 0.56
% 3.63/1.62  Inferencing          : 0.20
% 3.63/1.62  Reduction            : 0.17
% 3.63/1.62  Demodulation         : 0.12
% 3.63/1.62  BG Simplification    : 0.02
% 3.63/1.62  Subsumption          : 0.13
% 3.63/1.62  Abstraction          : 0.03
% 3.63/1.62  MUC search           : 0.00
% 3.63/1.62  Cooper               : 0.00
% 3.63/1.62  Total                : 0.91
% 3.63/1.62  Index Insertion      : 0.00
% 3.63/1.62  Index Deletion       : 0.00
% 3.63/1.62  Index Matching       : 0.00
% 3.63/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
