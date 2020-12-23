%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0958+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:08 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  29 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_relat_2 > r2_hidden > r1_tarski > v4_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_relat_2,type,(
    r4_relat_2: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_49,axiom,(
    ! [A] : v4_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_wellord2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v4_relat_2(A)
      <=> r4_relat_2(A,k3_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_2)).

tff(f_52,negated_conjecture,(
    ~ ! [A] : r4_relat_2(k1_wellord2(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_wellord2)).

tff(c_24,plain,(
    ! [A_10] : v1_relat_1(k1_wellord2(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_11] : v4_relat_2(k1_wellord2(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_2] :
      ( k3_relat_1(k1_wellord2(A_2)) = A_2
      | ~ v1_relat_1(k1_wellord2(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    ! [A_2] : k3_relat_1(k1_wellord2(A_2)) = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18])).

tff(c_46,plain,(
    ! [A_15] :
      ( r4_relat_2(A_15,k3_relat_1(A_15))
      | ~ v4_relat_2(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_49,plain,(
    ! [A_2] :
      ( r4_relat_2(k1_wellord2(A_2),A_2)
      | ~ v4_relat_2(k1_wellord2(A_2))
      | ~ v1_relat_1(k1_wellord2(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_46])).

tff(c_51,plain,(
    ! [A_2] : r4_relat_2(k1_wellord2(A_2),A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_49])).

tff(c_28,plain,(
    ~ r4_relat_2(k1_wellord2('#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_64,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_28])).

%------------------------------------------------------------------------------
