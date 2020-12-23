%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0944+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:07 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  42 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k2_wellord1 > #nlpp > k1_wellord2 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( r1_tarski(B,A)
           => v2_wellord1(k1_wellord2(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_wellord2)).

tff(f_36,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_26,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v2_wellord1(B)
       => v2_wellord1(k2_wellord1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_wellord1)).

tff(c_10,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_4] :
      ( v2_wellord1(k1_wellord2(A_4))
      | ~ v3_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k1_wellord2(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_22,plain,(
    ! [B_12,A_13] :
      ( k2_wellord1(k1_wellord2(B_12),A_13) = k1_wellord2(A_13)
      | ~ r1_tarski(A_13,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( v2_wellord1(k2_wellord1(B_3,A_2))
      | ~ v2_wellord1(B_3)
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [A_13,B_12] :
      ( v2_wellord1(k1_wellord2(A_13))
      | ~ v2_wellord1(k1_wellord2(B_12))
      | ~ v1_relat_1(k1_wellord2(B_12))
      | ~ r1_tarski(A_13,B_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4])).

tff(c_36,plain,(
    ! [A_14,B_15] :
      ( v2_wellord1(k1_wellord2(A_14))
      | ~ v2_wellord1(k1_wellord2(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_40,plain,(
    ! [A_16,A_17] :
      ( v2_wellord1(k1_wellord2(A_16))
      | ~ r1_tarski(A_16,A_17)
      | ~ v3_ordinal1(A_17) ) ),
    inference(resolution,[status(thm)],[c_6,c_36])).

tff(c_42,plain,
    ( v2_wellord1(k1_wellord2('#skF_2'))
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_40])).

tff(c_45,plain,(
    v2_wellord1(k1_wellord2('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_42])).

tff(c_47,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_45])).

%------------------------------------------------------------------------------
