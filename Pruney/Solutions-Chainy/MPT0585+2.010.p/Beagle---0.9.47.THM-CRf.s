%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:01 EST 2020

% Result     : Theorem 11.70s
% Output     : CNFRefutation 11.78s
% Verified   : 
% Statistics : Number of formulae       :   49 (  56 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :   73 (  93 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    ! [B_33,A_32] :
      ( k3_xboole_0(k1_relat_1(B_33),A_32) = k1_relat_1(k7_relat_1(B_33,A_32))
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_74,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_1'(A_47,B_48),A_47)
      | r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [A_47] : r1_tarski(A_47,A_47) ),
    inference(resolution,[status(thm)],[c_74,c_4])).

tff(c_20,plain,(
    ! [A_24,B_25] :
      ( v1_relat_1(k7_relat_1(A_24,B_25))
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_201,plain,(
    ! [A_76,C_77,B_78] :
      ( r2_hidden(A_76,k1_relat_1(C_77))
      | ~ r2_hidden(A_76,k1_relat_1(k7_relat_1(C_77,B_78)))
      | ~ v1_relat_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_601,plain,(
    ! [C_110,B_111,B_112] :
      ( r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_110,B_111)),B_112),k1_relat_1(C_110))
      | ~ v1_relat_1(C_110)
      | r1_tarski(k1_relat_1(k7_relat_1(C_110,B_111)),B_112) ) ),
    inference(resolution,[status(thm)],[c_6,c_201])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8261,plain,(
    ! [C_331,B_332,B_333,B_334] :
      ( r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_331,B_332)),B_333),B_334)
      | ~ r1_tarski(k1_relat_1(C_331),B_334)
      | ~ v1_relat_1(C_331)
      | r1_tarski(k1_relat_1(k7_relat_1(C_331,B_332)),B_333) ) ),
    inference(resolution,[status(thm)],[c_601,c_2])).

tff(c_8403,plain,(
    ! [C_335,B_336,B_337] :
      ( ~ r1_tarski(k1_relat_1(C_335),B_336)
      | ~ v1_relat_1(C_335)
      | r1_tarski(k1_relat_1(k7_relat_1(C_335,B_337)),B_336) ) ),
    inference(resolution,[status(thm)],[c_8261,c_4])).

tff(c_32,plain,(
    ! [B_35,A_34] :
      ( k7_relat_1(B_35,A_34) = B_35
      | ~ r1_tarski(k1_relat_1(B_35),A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8655,plain,(
    ! [C_343,B_344,B_345] :
      ( k7_relat_1(k7_relat_1(C_343,B_344),B_345) = k7_relat_1(C_343,B_344)
      | ~ v1_relat_1(k7_relat_1(C_343,B_344))
      | ~ r1_tarski(k1_relat_1(C_343),B_345)
      | ~ v1_relat_1(C_343) ) ),
    inference(resolution,[status(thm)],[c_8403,c_32])).

tff(c_8830,plain,(
    ! [A_348,B_349,B_350] :
      ( k7_relat_1(k7_relat_1(A_348,B_349),B_350) = k7_relat_1(A_348,B_349)
      | ~ r1_tarski(k1_relat_1(A_348),B_350)
      | ~ v1_relat_1(A_348) ) ),
    inference(resolution,[status(thm)],[c_20,c_8655])).

tff(c_8901,plain,(
    ! [A_351,B_352] :
      ( k7_relat_1(k7_relat_1(A_351,B_352),k1_relat_1(A_351)) = k7_relat_1(A_351,B_352)
      | ~ v1_relat_1(A_351) ) ),
    inference(resolution,[status(thm)],[c_79,c_8830])).

tff(c_22,plain,(
    ! [C_28,A_26,B_27] :
      ( k7_relat_1(k7_relat_1(C_28,A_26),B_27) = k7_relat_1(C_28,k3_xboole_0(A_26,B_27))
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_9202,plain,(
    ! [A_353,B_354] :
      ( k7_relat_1(A_353,k3_xboole_0(B_354,k1_relat_1(A_353))) = k7_relat_1(A_353,B_354)
      | ~ v1_relat_1(A_353)
      | ~ v1_relat_1(A_353) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8901,c_22])).

tff(c_21044,plain,(
    ! [A_462,B_463] :
      ( k7_relat_1(A_462,k1_relat_1(k7_relat_1(B_463,k1_relat_1(A_462)))) = k7_relat_1(A_462,k1_relat_1(B_463))
      | ~ v1_relat_1(A_462)
      | ~ v1_relat_1(A_462)
      | ~ v1_relat_1(B_463) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_9202])).

tff(c_34,plain,(
    k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_3',k1_relat_1('#skF_2')))) != k7_relat_1('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_21324,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_21044,c_34])).

tff(c_21463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_21324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:37:35 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.70/4.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.78/4.89  
% 11.78/4.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.78/4.89  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 11.78/4.89  
% 11.78/4.89  %Foreground sorts:
% 11.78/4.89  
% 11.78/4.89  
% 11.78/4.89  %Background operators:
% 11.78/4.89  
% 11.78/4.89  
% 11.78/4.89  %Foreground operators:
% 11.78/4.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.78/4.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.78/4.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.78/4.89  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 11.78/4.89  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.78/4.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.78/4.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.78/4.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.78/4.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.78/4.89  tff('#skF_2', type, '#skF_2': $i).
% 11.78/4.89  tff('#skF_3', type, '#skF_3': $i).
% 11.78/4.89  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.78/4.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.78/4.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.78/4.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.78/4.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.78/4.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.78/4.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.78/4.89  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.78/4.89  
% 11.78/4.90  tff(f_78, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_relat_1)).
% 11.78/4.90  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 11.78/4.90  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.78/4.90  tff(f_48, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 11.78/4.90  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 11.78/4.90  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 11.78/4.90  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 11.78/4.90  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.78/4.90  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.78/4.90  tff(c_30, plain, (![B_33, A_32]: (k3_xboole_0(k1_relat_1(B_33), A_32)=k1_relat_1(k7_relat_1(B_33, A_32)) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.78/4.90  tff(c_74, plain, (![A_47, B_48]: (r2_hidden('#skF_1'(A_47, B_48), A_47) | r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.78/4.90  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.78/4.90  tff(c_79, plain, (![A_47]: (r1_tarski(A_47, A_47))), inference(resolution, [status(thm)], [c_74, c_4])).
% 11.78/4.90  tff(c_20, plain, (![A_24, B_25]: (v1_relat_1(k7_relat_1(A_24, B_25)) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.78/4.90  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.78/4.90  tff(c_201, plain, (![A_76, C_77, B_78]: (r2_hidden(A_76, k1_relat_1(C_77)) | ~r2_hidden(A_76, k1_relat_1(k7_relat_1(C_77, B_78))) | ~v1_relat_1(C_77))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.78/4.90  tff(c_601, plain, (![C_110, B_111, B_112]: (r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_110, B_111)), B_112), k1_relat_1(C_110)) | ~v1_relat_1(C_110) | r1_tarski(k1_relat_1(k7_relat_1(C_110, B_111)), B_112))), inference(resolution, [status(thm)], [c_6, c_201])).
% 11.78/4.90  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.78/4.90  tff(c_8261, plain, (![C_331, B_332, B_333, B_334]: (r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_331, B_332)), B_333), B_334) | ~r1_tarski(k1_relat_1(C_331), B_334) | ~v1_relat_1(C_331) | r1_tarski(k1_relat_1(k7_relat_1(C_331, B_332)), B_333))), inference(resolution, [status(thm)], [c_601, c_2])).
% 11.78/4.90  tff(c_8403, plain, (![C_335, B_336, B_337]: (~r1_tarski(k1_relat_1(C_335), B_336) | ~v1_relat_1(C_335) | r1_tarski(k1_relat_1(k7_relat_1(C_335, B_337)), B_336))), inference(resolution, [status(thm)], [c_8261, c_4])).
% 11.78/4.90  tff(c_32, plain, (![B_35, A_34]: (k7_relat_1(B_35, A_34)=B_35 | ~r1_tarski(k1_relat_1(B_35), A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.78/4.90  tff(c_8655, plain, (![C_343, B_344, B_345]: (k7_relat_1(k7_relat_1(C_343, B_344), B_345)=k7_relat_1(C_343, B_344) | ~v1_relat_1(k7_relat_1(C_343, B_344)) | ~r1_tarski(k1_relat_1(C_343), B_345) | ~v1_relat_1(C_343))), inference(resolution, [status(thm)], [c_8403, c_32])).
% 11.78/4.90  tff(c_8830, plain, (![A_348, B_349, B_350]: (k7_relat_1(k7_relat_1(A_348, B_349), B_350)=k7_relat_1(A_348, B_349) | ~r1_tarski(k1_relat_1(A_348), B_350) | ~v1_relat_1(A_348))), inference(resolution, [status(thm)], [c_20, c_8655])).
% 11.78/4.90  tff(c_8901, plain, (![A_351, B_352]: (k7_relat_1(k7_relat_1(A_351, B_352), k1_relat_1(A_351))=k7_relat_1(A_351, B_352) | ~v1_relat_1(A_351))), inference(resolution, [status(thm)], [c_79, c_8830])).
% 11.78/4.90  tff(c_22, plain, (![C_28, A_26, B_27]: (k7_relat_1(k7_relat_1(C_28, A_26), B_27)=k7_relat_1(C_28, k3_xboole_0(A_26, B_27)) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.78/4.90  tff(c_9202, plain, (![A_353, B_354]: (k7_relat_1(A_353, k3_xboole_0(B_354, k1_relat_1(A_353)))=k7_relat_1(A_353, B_354) | ~v1_relat_1(A_353) | ~v1_relat_1(A_353))), inference(superposition, [status(thm), theory('equality')], [c_8901, c_22])).
% 11.78/4.90  tff(c_21044, plain, (![A_462, B_463]: (k7_relat_1(A_462, k1_relat_1(k7_relat_1(B_463, k1_relat_1(A_462))))=k7_relat_1(A_462, k1_relat_1(B_463)) | ~v1_relat_1(A_462) | ~v1_relat_1(A_462) | ~v1_relat_1(B_463))), inference(superposition, [status(thm), theory('equality')], [c_30, c_9202])).
% 11.78/4.90  tff(c_34, plain, (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_3', k1_relat_1('#skF_2'))))!=k7_relat_1('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.78/4.90  tff(c_21324, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_21044, c_34])).
% 11.78/4.90  tff(c_21463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_21324])).
% 11.78/4.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.78/4.90  
% 11.78/4.90  Inference rules
% 11.78/4.90  ----------------------
% 11.78/4.90  #Ref     : 0
% 11.78/4.90  #Sup     : 6312
% 11.78/4.90  #Fact    : 0
% 11.78/4.90  #Define  : 0
% 11.78/4.90  #Split   : 1
% 11.78/4.90  #Chain   : 0
% 11.78/4.90  #Close   : 0
% 11.78/4.90  
% 11.78/4.90  Ordering : KBO
% 11.78/4.90  
% 11.78/4.90  Simplification rules
% 11.78/4.90  ----------------------
% 11.78/4.90  #Subsume      : 1563
% 11.78/4.90  #Demod        : 423
% 11.78/4.90  #Tautology    : 887
% 11.78/4.90  #SimpNegUnit  : 0
% 11.78/4.90  #BackRed      : 0
% 11.78/4.90  
% 11.78/4.90  #Partial instantiations: 0
% 11.78/4.90  #Strategies tried      : 1
% 11.78/4.90  
% 11.78/4.90  Timing (in seconds)
% 11.78/4.90  ----------------------
% 11.78/4.90  Preprocessing        : 0.33
% 11.78/4.90  Parsing              : 0.18
% 11.78/4.90  CNF conversion       : 0.02
% 11.78/4.90  Main loop            : 3.76
% 11.78/4.90  Inferencing          : 0.91
% 11.78/4.90  Reduction            : 0.70
% 11.78/4.90  Demodulation         : 0.49
% 11.78/4.90  BG Simplification    : 0.14
% 11.78/4.90  Subsumption          : 1.83
% 11.78/4.90  Abstraction          : 0.18
% 11.78/4.90  MUC search           : 0.00
% 11.78/4.90  Cooper               : 0.00
% 11.78/4.90  Total                : 4.12
% 11.78/4.91  Index Insertion      : 0.00
% 11.78/4.91  Index Deletion       : 0.00
% 11.78/4.91  Index Matching       : 0.00
% 11.78/4.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
