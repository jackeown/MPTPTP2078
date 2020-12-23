%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:31 EST 2020

% Result     : Theorem 6.64s
% Output     : CNFRefutation 6.64s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 103 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  134 ( 244 expanded)
%              Number of equality atoms :    2 (   8 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_50,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
          & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( v1_relat_1(D)
     => ( r2_hidden(k4_tarski(A,B),k5_relat_1(k6_relat_1(C),D))
      <=> ( r2_hidden(A,C)
          & r2_hidden(k4_tarski(A,B),D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( v1_relat_1(D)
     => ( r2_hidden(k4_tarski(A,B),k5_relat_1(D,k6_relat_1(C)))
      <=> ( r2_hidden(B,C)
          & r2_hidden(k4_tarski(A,B),D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_relat_1)).

tff(c_16,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14,plain,(
    ! [A_24,B_25] :
      ( v1_relat_1(k5_relat_1(A_24,B_25))
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_38,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44,B_45),A_44)
      | r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,(
    ! [A_44] : r1_tarski(A_44,A_44) ),
    inference(resolution,[status(thm)],[c_38,c_4])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,(
    ! [C_47,B_48,A_49] :
      ( r2_hidden(C_47,B_48)
      | ~ r2_hidden(C_47,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ! [A_1,B_2,B_48] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_48)
      | ~ r1_tarski(A_1,B_48)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_45])).

tff(c_8,plain,(
    ! [A_6,B_21] :
      ( k4_tarski('#skF_3'(A_6,B_21),'#skF_4'(A_6,B_21)) = B_21
      | ~ r2_hidden(B_21,A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2371,plain,(
    ! [A_493,B_494,D_495,C_496] :
      ( r2_hidden(k4_tarski(A_493,B_494),D_495)
      | ~ r2_hidden(k4_tarski(A_493,B_494),k5_relat_1(k6_relat_1(C_496),D_495))
      | ~ v1_relat_1(D_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2618,plain,(
    ! [A_562,B_563,D_564,C_565] :
      ( r2_hidden(k4_tarski('#skF_3'(A_562,B_563),'#skF_4'(A_562,B_563)),D_564)
      | ~ r2_hidden(B_563,k5_relat_1(k6_relat_1(C_565),D_564))
      | ~ v1_relat_1(D_564)
      | ~ r2_hidden(B_563,A_562)
      | ~ v1_relat_1(A_562) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2371])).

tff(c_3470,plain,(
    ! [A_722,C_723,D_724,B_725] :
      ( r2_hidden(k4_tarski('#skF_3'(A_722,'#skF_1'(k5_relat_1(k6_relat_1(C_723),D_724),B_725)),'#skF_4'(A_722,'#skF_1'(k5_relat_1(k6_relat_1(C_723),D_724),B_725))),D_724)
      | ~ v1_relat_1(D_724)
      | ~ r2_hidden('#skF_1'(k5_relat_1(k6_relat_1(C_723),D_724),B_725),A_722)
      | ~ v1_relat_1(A_722)
      | r1_tarski(k5_relat_1(k6_relat_1(C_723),D_724),B_725) ) ),
    inference(resolution,[status(thm)],[c_6,c_2618])).

tff(c_4192,plain,(
    ! [C_844,D_845,B_846,A_847] :
      ( r2_hidden('#skF_1'(k5_relat_1(k6_relat_1(C_844),D_845),B_846),D_845)
      | ~ v1_relat_1(D_845)
      | ~ r2_hidden('#skF_1'(k5_relat_1(k6_relat_1(C_844),D_845),B_846),A_847)
      | ~ v1_relat_1(A_847)
      | r1_tarski(k5_relat_1(k6_relat_1(C_844),D_845),B_846)
      | ~ r2_hidden('#skF_1'(k5_relat_1(k6_relat_1(C_844),D_845),B_846),A_847)
      | ~ v1_relat_1(A_847) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3470])).

tff(c_4217,plain,(
    ! [C_853,D_854,B_855,B_856] :
      ( r2_hidden('#skF_1'(k5_relat_1(k6_relat_1(C_853),D_854),B_855),D_854)
      | ~ v1_relat_1(D_854)
      | ~ r2_hidden('#skF_1'(k5_relat_1(k6_relat_1(C_853),D_854),B_855),B_856)
      | ~ v1_relat_1(B_856)
      | ~ r1_tarski(k5_relat_1(k6_relat_1(C_853),D_854),B_856)
      | r1_tarski(k5_relat_1(k6_relat_1(C_853),D_854),B_855) ) ),
    inference(resolution,[status(thm)],[c_50,c_4192])).

tff(c_4223,plain,(
    ! [C_853,D_854,B_2] :
      ( r2_hidden('#skF_1'(k5_relat_1(k6_relat_1(C_853),D_854),B_2),D_854)
      | ~ v1_relat_1(D_854)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_853),D_854))
      | ~ r1_tarski(k5_relat_1(k6_relat_1(C_853),D_854),k5_relat_1(k6_relat_1(C_853),D_854))
      | r1_tarski(k5_relat_1(k6_relat_1(C_853),D_854),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_4217])).

tff(c_4228,plain,(
    ! [C_857,D_858,B_859] :
      ( r2_hidden('#skF_1'(k5_relat_1(k6_relat_1(C_857),D_858),B_859),D_858)
      | ~ v1_relat_1(D_858)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_857),D_858))
      | r1_tarski(k5_relat_1(k6_relat_1(C_857),D_858),B_859) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_4223])).

tff(c_4283,plain,(
    ! [D_860,C_861] :
      ( ~ v1_relat_1(D_860)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_861),D_860))
      | r1_tarski(k5_relat_1(k6_relat_1(C_861),D_860),D_860) ) ),
    inference(resolution,[status(thm)],[c_4228,c_4])).

tff(c_111,plain,(
    ! [A_79,B_80,D_81,C_82] :
      ( r2_hidden(k4_tarski(A_79,B_80),D_81)
      | ~ r2_hidden(k4_tarski(A_79,B_80),k5_relat_1(D_81,k6_relat_1(C_82)))
      | ~ v1_relat_1(D_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_253,plain,(
    ! [A_137,B_138,D_139,C_140] :
      ( r2_hidden(k4_tarski('#skF_3'(A_137,B_138),'#skF_4'(A_137,B_138)),D_139)
      | ~ r2_hidden(B_138,k5_relat_1(D_139,k6_relat_1(C_140)))
      | ~ v1_relat_1(D_139)
      | ~ r2_hidden(B_138,A_137)
      | ~ v1_relat_1(A_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_111])).

tff(c_1255,plain,(
    ! [A_341,D_342,C_343,B_344] :
      ( r2_hidden(k4_tarski('#skF_3'(A_341,'#skF_1'(k5_relat_1(D_342,k6_relat_1(C_343)),B_344)),'#skF_4'(A_341,'#skF_1'(k5_relat_1(D_342,k6_relat_1(C_343)),B_344))),D_342)
      | ~ v1_relat_1(D_342)
      | ~ r2_hidden('#skF_1'(k5_relat_1(D_342,k6_relat_1(C_343)),B_344),A_341)
      | ~ v1_relat_1(A_341)
      | r1_tarski(k5_relat_1(D_342,k6_relat_1(C_343)),B_344) ) ),
    inference(resolution,[status(thm)],[c_6,c_253])).

tff(c_2045,plain,(
    ! [D_438,C_439,B_440,A_441] :
      ( r2_hidden('#skF_1'(k5_relat_1(D_438,k6_relat_1(C_439)),B_440),D_438)
      | ~ v1_relat_1(D_438)
      | ~ r2_hidden('#skF_1'(k5_relat_1(D_438,k6_relat_1(C_439)),B_440),A_441)
      | ~ v1_relat_1(A_441)
      | r1_tarski(k5_relat_1(D_438,k6_relat_1(C_439)),B_440)
      | ~ r2_hidden('#skF_1'(k5_relat_1(D_438,k6_relat_1(C_439)),B_440),A_441)
      | ~ v1_relat_1(A_441) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1255])).

tff(c_2066,plain,(
    ! [D_442,C_443,B_444,B_445] :
      ( r2_hidden('#skF_1'(k5_relat_1(D_442,k6_relat_1(C_443)),B_444),D_442)
      | ~ v1_relat_1(D_442)
      | ~ r2_hidden('#skF_1'(k5_relat_1(D_442,k6_relat_1(C_443)),B_444),B_445)
      | ~ v1_relat_1(B_445)
      | ~ r1_tarski(k5_relat_1(D_442,k6_relat_1(C_443)),B_445)
      | r1_tarski(k5_relat_1(D_442,k6_relat_1(C_443)),B_444) ) ),
    inference(resolution,[status(thm)],[c_50,c_2045])).

tff(c_2078,plain,(
    ! [D_442,C_443,B_2] :
      ( r2_hidden('#skF_1'(k5_relat_1(D_442,k6_relat_1(C_443)),B_2),D_442)
      | ~ v1_relat_1(D_442)
      | ~ v1_relat_1(k5_relat_1(D_442,k6_relat_1(C_443)))
      | ~ r1_tarski(k5_relat_1(D_442,k6_relat_1(C_443)),k5_relat_1(D_442,k6_relat_1(C_443)))
      | r1_tarski(k5_relat_1(D_442,k6_relat_1(C_443)),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_2066])).

tff(c_2089,plain,(
    ! [D_446,C_447,B_448] :
      ( r2_hidden('#skF_1'(k5_relat_1(D_446,k6_relat_1(C_447)),B_448),D_446)
      | ~ v1_relat_1(D_446)
      | ~ v1_relat_1(k5_relat_1(D_446,k6_relat_1(C_447)))
      | r1_tarski(k5_relat_1(D_446,k6_relat_1(C_447)),B_448) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_2078])).

tff(c_2156,plain,(
    ! [D_449,C_450] :
      ( ~ v1_relat_1(D_449)
      | ~ v1_relat_1(k5_relat_1(D_449,k6_relat_1(C_450)))
      | r1_tarski(k5_relat_1(D_449,k6_relat_1(C_450)),D_449) ) ),
    inference(resolution,[status(thm)],[c_2089,c_4])).

tff(c_30,plain,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1('#skF_5'),'#skF_6'),'#skF_6')
    | ~ r1_tarski(k5_relat_1('#skF_6',k6_relat_1('#skF_5')),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_52,plain,(
    ~ r1_tarski(k5_relat_1('#skF_6',k6_relat_1('#skF_5')),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_2218,plain,
    ( ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1(k5_relat_1('#skF_6',k6_relat_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_2156,c_52])).

tff(c_2252,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_6',k6_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2218])).

tff(c_2268,plain,
    ( ~ v1_relat_1(k6_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_14,c_2252])).

tff(c_2272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_16,c_2268])).

tff(c_2273,plain,(
    ~ r1_tarski(k5_relat_1(k6_relat_1('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_4343,plain,
    ( ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_4283,c_2273])).

tff(c_4382,plain,(
    ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_5'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4343])).

tff(c_4385,plain,
    ( ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1(k6_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_14,c_4382])).

tff(c_4389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_32,c_4385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.64/2.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.64/2.41  
% 6.64/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.64/2.41  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 6.64/2.41  
% 6.64/2.41  %Foreground sorts:
% 6.64/2.41  
% 6.64/2.41  
% 6.64/2.41  %Background operators:
% 6.64/2.41  
% 6.64/2.41  
% 6.64/2.41  %Foreground operators:
% 6.64/2.41  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.64/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.64/2.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.64/2.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.64/2.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.64/2.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.64/2.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.64/2.41  tff('#skF_5', type, '#skF_5': $i).
% 6.64/2.41  tff('#skF_6', type, '#skF_6': $i).
% 6.64/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.64/2.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.64/2.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.64/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.64/2.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.64/2.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.64/2.41  
% 6.64/2.43  tff(f_50, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 6.64/2.43  tff(f_73, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 6.64/2.43  tff(f_48, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 6.64/2.43  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.64/2.43  tff(f_42, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 6.64/2.43  tff(f_58, axiom, (![A, B, C, D]: (v1_relat_1(D) => (r2_hidden(k4_tarski(A, B), k5_relat_1(k6_relat_1(C), D)) <=> (r2_hidden(A, C) & r2_hidden(k4_tarski(A, B), D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_relat_1)).
% 6.64/2.43  tff(f_66, axiom, (![A, B, C, D]: (v1_relat_1(D) => (r2_hidden(k4_tarski(A, B), k5_relat_1(D, k6_relat_1(C))) <=> (r2_hidden(B, C) & r2_hidden(k4_tarski(A, B), D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_relat_1)).
% 6.64/2.43  tff(c_16, plain, (![A_26]: (v1_relat_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.64/2.43  tff(c_32, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.64/2.43  tff(c_14, plain, (![A_24, B_25]: (v1_relat_1(k5_relat_1(A_24, B_25)) | ~v1_relat_1(B_25) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.64/2.43  tff(c_38, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44, B_45), A_44) | r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.64/2.43  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.64/2.43  tff(c_43, plain, (![A_44]: (r1_tarski(A_44, A_44))), inference(resolution, [status(thm)], [c_38, c_4])).
% 6.64/2.43  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.64/2.43  tff(c_45, plain, (![C_47, B_48, A_49]: (r2_hidden(C_47, B_48) | ~r2_hidden(C_47, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.64/2.43  tff(c_50, plain, (![A_1, B_2, B_48]: (r2_hidden('#skF_1'(A_1, B_2), B_48) | ~r1_tarski(A_1, B_48) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_45])).
% 6.64/2.43  tff(c_8, plain, (![A_6, B_21]: (k4_tarski('#skF_3'(A_6, B_21), '#skF_4'(A_6, B_21))=B_21 | ~r2_hidden(B_21, A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.64/2.43  tff(c_2371, plain, (![A_493, B_494, D_495, C_496]: (r2_hidden(k4_tarski(A_493, B_494), D_495) | ~r2_hidden(k4_tarski(A_493, B_494), k5_relat_1(k6_relat_1(C_496), D_495)) | ~v1_relat_1(D_495))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.64/2.43  tff(c_2618, plain, (![A_562, B_563, D_564, C_565]: (r2_hidden(k4_tarski('#skF_3'(A_562, B_563), '#skF_4'(A_562, B_563)), D_564) | ~r2_hidden(B_563, k5_relat_1(k6_relat_1(C_565), D_564)) | ~v1_relat_1(D_564) | ~r2_hidden(B_563, A_562) | ~v1_relat_1(A_562))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2371])).
% 6.64/2.43  tff(c_3470, plain, (![A_722, C_723, D_724, B_725]: (r2_hidden(k4_tarski('#skF_3'(A_722, '#skF_1'(k5_relat_1(k6_relat_1(C_723), D_724), B_725)), '#skF_4'(A_722, '#skF_1'(k5_relat_1(k6_relat_1(C_723), D_724), B_725))), D_724) | ~v1_relat_1(D_724) | ~r2_hidden('#skF_1'(k5_relat_1(k6_relat_1(C_723), D_724), B_725), A_722) | ~v1_relat_1(A_722) | r1_tarski(k5_relat_1(k6_relat_1(C_723), D_724), B_725))), inference(resolution, [status(thm)], [c_6, c_2618])).
% 6.64/2.43  tff(c_4192, plain, (![C_844, D_845, B_846, A_847]: (r2_hidden('#skF_1'(k5_relat_1(k6_relat_1(C_844), D_845), B_846), D_845) | ~v1_relat_1(D_845) | ~r2_hidden('#skF_1'(k5_relat_1(k6_relat_1(C_844), D_845), B_846), A_847) | ~v1_relat_1(A_847) | r1_tarski(k5_relat_1(k6_relat_1(C_844), D_845), B_846) | ~r2_hidden('#skF_1'(k5_relat_1(k6_relat_1(C_844), D_845), B_846), A_847) | ~v1_relat_1(A_847))), inference(superposition, [status(thm), theory('equality')], [c_8, c_3470])).
% 6.64/2.43  tff(c_4217, plain, (![C_853, D_854, B_855, B_856]: (r2_hidden('#skF_1'(k5_relat_1(k6_relat_1(C_853), D_854), B_855), D_854) | ~v1_relat_1(D_854) | ~r2_hidden('#skF_1'(k5_relat_1(k6_relat_1(C_853), D_854), B_855), B_856) | ~v1_relat_1(B_856) | ~r1_tarski(k5_relat_1(k6_relat_1(C_853), D_854), B_856) | r1_tarski(k5_relat_1(k6_relat_1(C_853), D_854), B_855))), inference(resolution, [status(thm)], [c_50, c_4192])).
% 6.64/2.43  tff(c_4223, plain, (![C_853, D_854, B_2]: (r2_hidden('#skF_1'(k5_relat_1(k6_relat_1(C_853), D_854), B_2), D_854) | ~v1_relat_1(D_854) | ~v1_relat_1(k5_relat_1(k6_relat_1(C_853), D_854)) | ~r1_tarski(k5_relat_1(k6_relat_1(C_853), D_854), k5_relat_1(k6_relat_1(C_853), D_854)) | r1_tarski(k5_relat_1(k6_relat_1(C_853), D_854), B_2))), inference(resolution, [status(thm)], [c_6, c_4217])).
% 6.64/2.43  tff(c_4228, plain, (![C_857, D_858, B_859]: (r2_hidden('#skF_1'(k5_relat_1(k6_relat_1(C_857), D_858), B_859), D_858) | ~v1_relat_1(D_858) | ~v1_relat_1(k5_relat_1(k6_relat_1(C_857), D_858)) | r1_tarski(k5_relat_1(k6_relat_1(C_857), D_858), B_859))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_4223])).
% 6.64/2.43  tff(c_4283, plain, (![D_860, C_861]: (~v1_relat_1(D_860) | ~v1_relat_1(k5_relat_1(k6_relat_1(C_861), D_860)) | r1_tarski(k5_relat_1(k6_relat_1(C_861), D_860), D_860))), inference(resolution, [status(thm)], [c_4228, c_4])).
% 6.64/2.43  tff(c_111, plain, (![A_79, B_80, D_81, C_82]: (r2_hidden(k4_tarski(A_79, B_80), D_81) | ~r2_hidden(k4_tarski(A_79, B_80), k5_relat_1(D_81, k6_relat_1(C_82))) | ~v1_relat_1(D_81))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.64/2.43  tff(c_253, plain, (![A_137, B_138, D_139, C_140]: (r2_hidden(k4_tarski('#skF_3'(A_137, B_138), '#skF_4'(A_137, B_138)), D_139) | ~r2_hidden(B_138, k5_relat_1(D_139, k6_relat_1(C_140))) | ~v1_relat_1(D_139) | ~r2_hidden(B_138, A_137) | ~v1_relat_1(A_137))), inference(superposition, [status(thm), theory('equality')], [c_8, c_111])).
% 6.64/2.43  tff(c_1255, plain, (![A_341, D_342, C_343, B_344]: (r2_hidden(k4_tarski('#skF_3'(A_341, '#skF_1'(k5_relat_1(D_342, k6_relat_1(C_343)), B_344)), '#skF_4'(A_341, '#skF_1'(k5_relat_1(D_342, k6_relat_1(C_343)), B_344))), D_342) | ~v1_relat_1(D_342) | ~r2_hidden('#skF_1'(k5_relat_1(D_342, k6_relat_1(C_343)), B_344), A_341) | ~v1_relat_1(A_341) | r1_tarski(k5_relat_1(D_342, k6_relat_1(C_343)), B_344))), inference(resolution, [status(thm)], [c_6, c_253])).
% 6.64/2.43  tff(c_2045, plain, (![D_438, C_439, B_440, A_441]: (r2_hidden('#skF_1'(k5_relat_1(D_438, k6_relat_1(C_439)), B_440), D_438) | ~v1_relat_1(D_438) | ~r2_hidden('#skF_1'(k5_relat_1(D_438, k6_relat_1(C_439)), B_440), A_441) | ~v1_relat_1(A_441) | r1_tarski(k5_relat_1(D_438, k6_relat_1(C_439)), B_440) | ~r2_hidden('#skF_1'(k5_relat_1(D_438, k6_relat_1(C_439)), B_440), A_441) | ~v1_relat_1(A_441))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1255])).
% 6.64/2.43  tff(c_2066, plain, (![D_442, C_443, B_444, B_445]: (r2_hidden('#skF_1'(k5_relat_1(D_442, k6_relat_1(C_443)), B_444), D_442) | ~v1_relat_1(D_442) | ~r2_hidden('#skF_1'(k5_relat_1(D_442, k6_relat_1(C_443)), B_444), B_445) | ~v1_relat_1(B_445) | ~r1_tarski(k5_relat_1(D_442, k6_relat_1(C_443)), B_445) | r1_tarski(k5_relat_1(D_442, k6_relat_1(C_443)), B_444))), inference(resolution, [status(thm)], [c_50, c_2045])).
% 6.64/2.43  tff(c_2078, plain, (![D_442, C_443, B_2]: (r2_hidden('#skF_1'(k5_relat_1(D_442, k6_relat_1(C_443)), B_2), D_442) | ~v1_relat_1(D_442) | ~v1_relat_1(k5_relat_1(D_442, k6_relat_1(C_443))) | ~r1_tarski(k5_relat_1(D_442, k6_relat_1(C_443)), k5_relat_1(D_442, k6_relat_1(C_443))) | r1_tarski(k5_relat_1(D_442, k6_relat_1(C_443)), B_2))), inference(resolution, [status(thm)], [c_6, c_2066])).
% 6.64/2.43  tff(c_2089, plain, (![D_446, C_447, B_448]: (r2_hidden('#skF_1'(k5_relat_1(D_446, k6_relat_1(C_447)), B_448), D_446) | ~v1_relat_1(D_446) | ~v1_relat_1(k5_relat_1(D_446, k6_relat_1(C_447))) | r1_tarski(k5_relat_1(D_446, k6_relat_1(C_447)), B_448))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_2078])).
% 6.64/2.43  tff(c_2156, plain, (![D_449, C_450]: (~v1_relat_1(D_449) | ~v1_relat_1(k5_relat_1(D_449, k6_relat_1(C_450))) | r1_tarski(k5_relat_1(D_449, k6_relat_1(C_450)), D_449))), inference(resolution, [status(thm)], [c_2089, c_4])).
% 6.64/2.43  tff(c_30, plain, (~r1_tarski(k5_relat_1(k6_relat_1('#skF_5'), '#skF_6'), '#skF_6') | ~r1_tarski(k5_relat_1('#skF_6', k6_relat_1('#skF_5')), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.64/2.43  tff(c_52, plain, (~r1_tarski(k5_relat_1('#skF_6', k6_relat_1('#skF_5')), '#skF_6')), inference(splitLeft, [status(thm)], [c_30])).
% 6.64/2.43  tff(c_2218, plain, (~v1_relat_1('#skF_6') | ~v1_relat_1(k5_relat_1('#skF_6', k6_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_2156, c_52])).
% 6.64/2.43  tff(c_2252, plain, (~v1_relat_1(k5_relat_1('#skF_6', k6_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2218])).
% 6.64/2.43  tff(c_2268, plain, (~v1_relat_1(k6_relat_1('#skF_5')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_14, c_2252])).
% 6.64/2.43  tff(c_2272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_16, c_2268])).
% 6.64/2.43  tff(c_2273, plain, (~r1_tarski(k5_relat_1(k6_relat_1('#skF_5'), '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_30])).
% 6.64/2.43  tff(c_4343, plain, (~v1_relat_1('#skF_6') | ~v1_relat_1(k5_relat_1(k6_relat_1('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_4283, c_2273])).
% 6.64/2.43  tff(c_4382, plain, (~v1_relat_1(k5_relat_1(k6_relat_1('#skF_5'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4343])).
% 6.64/2.43  tff(c_4385, plain, (~v1_relat_1('#skF_6') | ~v1_relat_1(k6_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_14, c_4382])).
% 6.64/2.43  tff(c_4389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_32, c_4385])).
% 6.64/2.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.64/2.43  
% 6.64/2.43  Inference rules
% 6.64/2.43  ----------------------
% 6.64/2.43  #Ref     : 2
% 6.64/2.43  #Sup     : 1083
% 6.64/2.43  #Fact    : 0
% 6.64/2.43  #Define  : 0
% 6.64/2.43  #Split   : 1
% 6.64/2.43  #Chain   : 0
% 6.64/2.43  #Close   : 0
% 6.64/2.43  
% 6.64/2.43  Ordering : KBO
% 6.64/2.43  
% 6.64/2.43  Simplification rules
% 6.64/2.43  ----------------------
% 6.64/2.43  #Subsume      : 182
% 6.64/2.43  #Demod        : 186
% 6.64/2.43  #Tautology    : 47
% 6.64/2.43  #SimpNegUnit  : 0
% 6.64/2.43  #BackRed      : 0
% 6.64/2.43  
% 6.64/2.43  #Partial instantiations: 0
% 6.64/2.43  #Strategies tried      : 1
% 6.64/2.43  
% 6.64/2.43  Timing (in seconds)
% 6.64/2.43  ----------------------
% 6.64/2.43  Preprocessing        : 0.27
% 6.64/2.43  Parsing              : 0.15
% 6.64/2.43  CNF conversion       : 0.02
% 6.64/2.43  Main loop            : 1.40
% 6.64/2.43  Inferencing          : 0.39
% 6.64/2.43  Reduction            : 0.32
% 6.64/2.43  Demodulation         : 0.21
% 6.64/2.43  BG Simplification    : 0.05
% 6.64/2.43  Subsumption          : 0.56
% 6.91/2.43  Abstraction          : 0.06
% 6.91/2.43  MUC search           : 0.00
% 6.91/2.43  Cooper               : 0.00
% 6.91/2.43  Total                : 1.70
% 6.91/2.43  Index Insertion      : 0.00
% 6.91/2.43  Index Deletion       : 0.00
% 6.91/2.43  Index Matching       : 0.00
% 6.91/2.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
