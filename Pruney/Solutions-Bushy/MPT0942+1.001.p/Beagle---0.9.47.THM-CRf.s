%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0942+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:07 EST 2020

% Result     : Theorem 1.39s
% Output     : CNFRefutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  56 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v8_relat_2 > v6_relat_2 > v4_relat_2 > v3_ordinal1 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > #nlpp > k1_wellord2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(v6_relat_2,type,(
    v6_relat_2: $i > $o )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

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

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_54,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v1_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_wellord2)).

tff(f_48,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v6_relat_2(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_wellord2)).

tff(f_40,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_42,axiom,(
    ! [A] : v1_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord2)).

tff(f_50,axiom,(
    ! [A] : v4_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_wellord2)).

tff(f_44,axiom,(
    ! [A] : v8_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_wellord2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

tff(c_28,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    ! [A_7] :
      ( v1_wellord1(k1_wellord2(A_7))
      | ~ v3_ordinal1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    ! [A_5] :
      ( v6_relat_2(k1_wellord2(A_5))
      | ~ v3_ordinal1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    ! [A_2] : v1_relat_1(k1_wellord2(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_3] : v1_relat_2(k1_wellord2(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_6] : v4_relat_2(k1_wellord2(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    ! [A_4] : v8_relat_2(k1_wellord2(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_40,plain,(
    ! [A_19] :
      ( v2_wellord1(A_19)
      | ~ v1_wellord1(A_19)
      | ~ v6_relat_2(A_19)
      | ~ v4_relat_2(A_19)
      | ~ v8_relat_2(A_19)
      | ~ v1_relat_2(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_46,plain,(
    ! [A_4] :
      ( v2_wellord1(k1_wellord2(A_4))
      | ~ v1_wellord1(k1_wellord2(A_4))
      | ~ v6_relat_2(k1_wellord2(A_4))
      | ~ v4_relat_2(k1_wellord2(A_4))
      | ~ v1_relat_2(k1_wellord2(A_4))
      | ~ v1_relat_1(k1_wellord2(A_4)) ) ),
    inference(resolution,[status(thm)],[c_18,c_40])).

tff(c_51,plain,(
    ! [A_20] :
      ( v2_wellord1(k1_wellord2(A_20))
      | ~ v1_wellord1(k1_wellord2(A_20))
      | ~ v6_relat_2(k1_wellord2(A_20)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_22,c_46])).

tff(c_62,plain,(
    ! [A_21] :
      ( v2_wellord1(k1_wellord2(A_21))
      | ~ v1_wellord1(k1_wellord2(A_21))
      | ~ v3_ordinal1(A_21) ) ),
    inference(resolution,[status(thm)],[c_20,c_51])).

tff(c_26,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_71,plain,
    ( ~ v1_wellord1(k1_wellord2('#skF_1'))
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_26])).

tff(c_80,plain,(
    ~ v1_wellord1(k1_wellord2('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_71])).

tff(c_83,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_80])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_83])).

%------------------------------------------------------------------------------
