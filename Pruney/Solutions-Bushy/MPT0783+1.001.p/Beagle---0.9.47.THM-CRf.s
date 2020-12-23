%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0783+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:51 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 193 expanded)
%              Number of leaves         :   21 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :  149 ( 663 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k2_wellord1 > #nlpp > #skF_2 > #skF_1

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

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( v2_wellord1(B)
         => v2_wellord1(k2_wellord1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k2_wellord1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v1_relat_2(B)
       => v1_relat_2(k2_wellord1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_wellord1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v1_wellord1(B)
       => v1_wellord1(k2_wellord1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_wellord1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_2(B)
       => v4_relat_2(k2_wellord1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_wellord1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v6_relat_2(B)
       => v6_relat_2(k2_wellord1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_wellord1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v8_relat_2(B)
       => v8_relat_2(k2_wellord1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_wellord1)).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14,plain,(
    ! [A_2,B_3] :
      ( v1_relat_1(k2_wellord1(A_2,B_3))
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    v2_wellord1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10,plain,(
    ! [A_1] :
      ( v8_relat_2(A_1)
      | ~ v2_wellord1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    ! [A_16] :
      ( v1_relat_2(A_16)
      | ~ v2_wellord1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_35,plain,
    ( v1_relat_2('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_32])).

tff(c_38,plain,(
    v1_relat_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_35])).

tff(c_16,plain,(
    ! [B_5,A_4] :
      ( v1_relat_2(k2_wellord1(B_5,A_4))
      | ~ v1_relat_2(B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_1] :
      ( v6_relat_2(A_1)
      | ~ v2_wellord1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_40,plain,(
    ! [A_18] :
      ( v1_wellord1(A_18)
      | ~ v2_wellord1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_43,plain,
    ( v1_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_40])).

tff(c_46,plain,(
    v1_wellord1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_43])).

tff(c_24,plain,(
    ! [B_13,A_12] :
      ( v1_wellord1(k2_wellord1(B_13,A_12))
      | ~ v1_wellord1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [A_1] :
      ( v4_relat_2(A_1)
      | ~ v2_wellord1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ! [B_11,A_10] :
      ( v4_relat_2(k2_wellord1(B_11,A_10))
      | ~ v4_relat_2(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [B_7,A_6] :
      ( v6_relat_2(k2_wellord1(B_7,A_6))
      | ~ v6_relat_2(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    ! [B_9,A_8] :
      ( v8_relat_2(k2_wellord1(B_9,A_8))
      | ~ v8_relat_2(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_54,plain,(
    ! [A_31] :
      ( v2_wellord1(A_31)
      | ~ v1_wellord1(A_31)
      | ~ v6_relat_2(A_31)
      | ~ v4_relat_2(A_31)
      | ~ v8_relat_2(A_31)
      | ~ v1_relat_2(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_63,plain,(
    ! [B_32,A_33] :
      ( v2_wellord1(k2_wellord1(B_32,A_33))
      | ~ v1_wellord1(k2_wellord1(B_32,A_33))
      | ~ v6_relat_2(k2_wellord1(B_32,A_33))
      | ~ v4_relat_2(k2_wellord1(B_32,A_33))
      | ~ v1_relat_2(k2_wellord1(B_32,A_33))
      | ~ v1_relat_1(k2_wellord1(B_32,A_33))
      | ~ v8_relat_2(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(resolution,[status(thm)],[c_20,c_54])).

tff(c_72,plain,(
    ! [B_34,A_35] :
      ( v2_wellord1(k2_wellord1(B_34,A_35))
      | ~ v1_wellord1(k2_wellord1(B_34,A_35))
      | ~ v4_relat_2(k2_wellord1(B_34,A_35))
      | ~ v1_relat_2(k2_wellord1(B_34,A_35))
      | ~ v1_relat_1(k2_wellord1(B_34,A_35))
      | ~ v8_relat_2(B_34)
      | ~ v6_relat_2(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(resolution,[status(thm)],[c_18,c_63])).

tff(c_81,plain,(
    ! [B_36,A_37] :
      ( v2_wellord1(k2_wellord1(B_36,A_37))
      | ~ v1_wellord1(k2_wellord1(B_36,A_37))
      | ~ v1_relat_2(k2_wellord1(B_36,A_37))
      | ~ v1_relat_1(k2_wellord1(B_36,A_37))
      | ~ v8_relat_2(B_36)
      | ~ v6_relat_2(B_36)
      | ~ v4_relat_2(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_22,c_72])).

tff(c_26,plain,(
    ~ v2_wellord1(k2_wellord1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_90,plain,
    ( ~ v1_wellord1(k2_wellord1('#skF_2','#skF_1'))
    | ~ v1_relat_2(k2_wellord1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1'))
    | ~ v8_relat_2('#skF_2')
    | ~ v6_relat_2('#skF_2')
    | ~ v4_relat_2('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_81,c_26])).

tff(c_95,plain,
    ( ~ v1_wellord1(k2_wellord1('#skF_2','#skF_1'))
    | ~ v1_relat_2(k2_wellord1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1'))
    | ~ v8_relat_2('#skF_2')
    | ~ v6_relat_2('#skF_2')
    | ~ v4_relat_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_90])).

tff(c_96,plain,(
    ~ v4_relat_2('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_99,plain,
    ( ~ v2_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_96])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_99])).

tff(c_104,plain,
    ( ~ v6_relat_2('#skF_2')
    | ~ v8_relat_2('#skF_2')
    | ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1'))
    | ~ v1_relat_2(k2_wellord1('#skF_2','#skF_1'))
    | ~ v1_wellord1(k2_wellord1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_106,plain,(
    ~ v1_wellord1(k2_wellord1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_109,plain,
    ( ~ v1_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_106])).

tff(c_113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_46,c_109])).

tff(c_114,plain,
    ( ~ v1_relat_2(k2_wellord1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1'))
    | ~ v8_relat_2('#skF_2')
    | ~ v6_relat_2('#skF_2') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_116,plain,(
    ~ v6_relat_2('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_119,plain,
    ( ~ v2_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_116])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_119])).

tff(c_124,plain,
    ( ~ v8_relat_2('#skF_2')
    | ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1'))
    | ~ v1_relat_2(k2_wellord1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_126,plain,(
    ~ v1_relat_2(k2_wellord1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_129,plain,
    ( ~ v1_relat_2('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_126])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_38,c_129])).

tff(c_134,plain,
    ( ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1'))
    | ~ v8_relat_2('#skF_2') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_136,plain,(
    ~ v8_relat_2('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_139,plain,
    ( ~ v2_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_136])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_139])).

tff(c_144,plain,(
    ~ v1_relat_1(k2_wellord1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_154,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_144])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_154])).

%------------------------------------------------------------------------------
