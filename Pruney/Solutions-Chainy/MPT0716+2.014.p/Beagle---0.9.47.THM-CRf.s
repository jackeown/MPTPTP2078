%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:38 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 654 expanded)
%              Number of leaves         :   34 ( 231 expanded)
%              Depth                    :   16
%              Number of atoms          :  213 (1846 expanded)
%              Number of equality atoms :   24 ( 176 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( r1_tarski(C,k1_relat_1(k5_relat_1(A,B)))
              <=> ( r1_tarski(C,k1_relat_1(A))
                  & r1_tarski(k9_relat_1(A,C),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_18,plain,(
    ! [A_20,B_22] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_20,B_22)),k1_relat_1(A_20))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_54,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_68,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,(
    k2_xboole_0('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) = k1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_120,plain,(
    ! [C_59] :
      ( r1_tarski('#skF_4',C_59)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),C_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2])).

tff(c_124,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_120])).

tff(c_127,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_124])).

tff(c_48,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_299,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_48])).

tff(c_300,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( k2_relat_1(k7_relat_1(B_16,A_15)) = k9_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_28,plain,(
    ! [A_29] : v1_relat_1(k6_relat_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    ! [A_29] : v1_funct_1(k6_relat_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22,plain,(
    ! [A_25,B_26] :
      ( k5_relat_1(k6_relat_1(A_25),B_26) = k7_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_276,plain,(
    ! [A_68,B_69] :
      ( v1_funct_1(k5_relat_1(A_68,B_69))
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_279,plain,(
    ! [B_26,A_25] :
      ( v1_funct_1(k7_relat_1(B_26,A_25))
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(k6_relat_1(A_25))
      | ~ v1_relat_1(k6_relat_1(A_25))
      | ~ v1_relat_1(B_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_276])).

tff(c_281,plain,(
    ! [B_26,A_25] :
      ( v1_funct_1(k7_relat_1(B_26,A_25))
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_279])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k7_relat_1(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_141,plain,(
    ! [B_61,A_62] :
      ( k1_relat_1(k7_relat_1(B_61,A_62)) = A_62
      | ~ r1_tarski(A_62,k1_relat_1(B_61))
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_144,plain,
    ( k1_relat_1(k7_relat_1('#skF_1','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_127,c_141])).

tff(c_156,plain,(
    k1_relat_1(k7_relat_1('#skF_1','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_144])).

tff(c_382,plain,(
    ! [B_81,C_82,A_83] :
      ( k7_relat_1(k5_relat_1(B_81,C_82),A_83) = k5_relat_1(k7_relat_1(B_81,A_83),C_82)
      | ~ v1_relat_1(C_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k5_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_161,plain,
    ( k1_relat_1(k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_4')) = '#skF_4'
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_141])).

tff(c_227,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_230,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_227])).

tff(c_234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_230])).

tff(c_235,plain,(
    k1_relat_1(k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_397,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_235])).

tff(c_415,plain,(
    k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_397])).

tff(c_434,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k7_relat_1('#skF_1','#skF_4')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_18])).

tff(c_447,plain,
    ( r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_156,c_434])).

tff(c_449,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_447])).

tff(c_452,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_449])).

tff(c_456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_452])).

tff(c_458,plain,(
    v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_12,plain,(
    ! [A_14] :
      ( k9_relat_1(A_14,k1_relat_1(A_14)) = k2_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_174,plain,
    ( k9_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_4') = k2_relat_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_12])).

tff(c_501,plain,(
    k9_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_4') = k2_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_174])).

tff(c_255,plain,(
    ! [A_66,B_67] :
      ( k10_relat_1(A_66,k1_relat_1(B_67)) = k1_relat_1(k5_relat_1(A_66,B_67))
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_32,plain,(
    ! [B_31,A_30] :
      ( r1_tarski(k9_relat_1(B_31,k10_relat_1(B_31,A_30)),A_30)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_919,plain,(
    ! [A_109,B_110] :
      ( r1_tarski(k9_relat_1(A_109,k1_relat_1(k5_relat_1(A_109,B_110))),k1_relat_1(B_110))
      | ~ v1_funct_1(A_109)
      | ~ v1_relat_1(A_109)
      | ~ v1_relat_1(B_110)
      | ~ v1_relat_1(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_32])).

tff(c_949,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_4'),k1_relat_1('#skF_2'))
    | ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_919])).

tff(c_969,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1('#skF_1','#skF_4')),k1_relat_1('#skF_2'))
    | ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_38,c_458,c_501,c_949])).

tff(c_978,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_969])).

tff(c_981,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_281,c_978])).

tff(c_985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_981])).

tff(c_986,plain,(
    r1_tarski(k2_relat_1(k7_relat_1('#skF_1','#skF_4')),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_969])).

tff(c_1086,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_986])).

tff(c_1092,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1086])).

tff(c_1094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_1092])).

tff(c_1096,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_44,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1262,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_1096,c_44])).

tff(c_16,plain,(
    ! [A_17,B_19] :
      ( k10_relat_1(A_17,k1_relat_1(B_19)) = k1_relat_1(k5_relat_1(A_17,B_19))
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1095,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_46,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1229,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_1096,c_46])).

tff(c_1348,plain,(
    ! [A_119,C_120,B_121] :
      ( r1_tarski(A_119,k10_relat_1(C_120,B_121))
      | ~ r1_tarski(k9_relat_1(C_120,A_119),B_121)
      | ~ r1_tarski(A_119,k1_relat_1(C_120))
      | ~ v1_funct_1(C_120)
      | ~ v1_relat_1(C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1357,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1229,c_1348])).

tff(c_1375,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1095,c_1357])).

tff(c_1385,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1375])).

tff(c_1388,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_1385])).

tff(c_1390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1262,c_1388])).

tff(c_1392,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_50,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1397,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1392,c_50])).

tff(c_1391,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1463,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_1392,c_52])).

tff(c_1963,plain,(
    ! [A_168,C_169,B_170] :
      ( r1_tarski(A_168,k10_relat_1(C_169,B_170))
      | ~ r1_tarski(k9_relat_1(C_169,A_168),B_170)
      | ~ r1_tarski(A_168,k1_relat_1(C_169))
      | ~ v1_funct_1(C_169)
      | ~ v1_relat_1(C_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1982,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1463,c_1963])).

tff(c_1998,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1391,c_1982])).

tff(c_2004,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1998])).

tff(c_2007,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_2004])).

tff(c_2009,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1397,c_2007])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:23:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.07/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/1.74  
% 4.07/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/1.74  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.07/1.74  
% 4.07/1.74  %Foreground sorts:
% 4.07/1.74  
% 4.07/1.74  
% 4.07/1.74  %Background operators:
% 4.07/1.74  
% 4.07/1.74  
% 4.07/1.74  %Foreground operators:
% 4.07/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.07/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.07/1.74  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.07/1.74  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.07/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.07/1.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.07/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.07/1.74  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.07/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.07/1.74  tff('#skF_1', type, '#skF_1': $i).
% 4.07/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.07/1.74  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.07/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.07/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.07/1.74  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.07/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.07/1.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.07/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.07/1.74  
% 4.07/1.76  tff(f_131, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 4.07/1.76  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 4.07/1.76  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.07/1.76  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.07/1.76  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.07/1.76  tff(f_98, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.07/1.76  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 4.07/1.76  tff(f_94, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 4.07/1.76  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.07/1.76  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 4.07/1.76  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 4.07/1.76  tff(f_39, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 4.07/1.76  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 4.07/1.76  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 4.07/1.76  tff(f_104, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 4.07/1.76  tff(f_114, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 4.07/1.76  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.07/1.76  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.07/1.76  tff(c_18, plain, (![A_20, B_22]: (r1_tarski(k1_relat_1(k5_relat_1(A_20, B_22)), k1_relat_1(A_20)) | ~v1_relat_1(B_22) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.07/1.76  tff(c_54, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.07/1.76  tff(c_68, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_54])).
% 4.07/1.76  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.07/1.76  tff(c_72, plain, (k2_xboole_0('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))=k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_4])).
% 4.07/1.76  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.07/1.76  tff(c_120, plain, (![C_59]: (r1_tarski('#skF_4', C_59) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), C_59))), inference(superposition, [status(thm), theory('equality')], [c_72, c_2])).
% 4.07/1.76  tff(c_124, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_120])).
% 4.07/1.76  tff(c_127, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_124])).
% 4.07/1.76  tff(c_48, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.07/1.76  tff(c_299, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_48])).
% 4.07/1.76  tff(c_300, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_299])).
% 4.07/1.76  tff(c_14, plain, (![B_16, A_15]: (k2_relat_1(k7_relat_1(B_16, A_15))=k9_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.07/1.76  tff(c_40, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.07/1.76  tff(c_28, plain, (![A_29]: (v1_relat_1(k6_relat_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.07/1.76  tff(c_30, plain, (![A_29]: (v1_funct_1(k6_relat_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.07/1.76  tff(c_22, plain, (![A_25, B_26]: (k5_relat_1(k6_relat_1(A_25), B_26)=k7_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.07/1.76  tff(c_276, plain, (![A_68, B_69]: (v1_funct_1(k5_relat_1(A_68, B_69)) | ~v1_funct_1(B_69) | ~v1_relat_1(B_69) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.07/1.76  tff(c_279, plain, (![B_26, A_25]: (v1_funct_1(k7_relat_1(B_26, A_25)) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(k6_relat_1(A_25)) | ~v1_relat_1(k6_relat_1(A_25)) | ~v1_relat_1(B_26))), inference(superposition, [status(thm), theory('equality')], [c_22, c_276])).
% 4.07/1.76  tff(c_281, plain, (![B_26, A_25]: (v1_funct_1(k7_relat_1(B_26, A_25)) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_279])).
% 4.07/1.76  tff(c_8, plain, (![A_8, B_9]: (v1_relat_1(k7_relat_1(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.07/1.76  tff(c_141, plain, (![B_61, A_62]: (k1_relat_1(k7_relat_1(B_61, A_62))=A_62 | ~r1_tarski(A_62, k1_relat_1(B_61)) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.07/1.76  tff(c_144, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_127, c_141])).
% 4.07/1.76  tff(c_156, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_144])).
% 4.07/1.76  tff(c_382, plain, (![B_81, C_82, A_83]: (k7_relat_1(k5_relat_1(B_81, C_82), A_83)=k5_relat_1(k7_relat_1(B_81, A_83), C_82) | ~v1_relat_1(C_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.07/1.76  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k5_relat_1(A_6, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.07/1.76  tff(c_161, plain, (k1_relat_1(k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_4'))='#skF_4' | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_141])).
% 4.07/1.76  tff(c_227, plain, (~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_161])).
% 4.07/1.76  tff(c_230, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_227])).
% 4.07/1.76  tff(c_234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_230])).
% 4.07/1.76  tff(c_235, plain, (k1_relat_1(k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_161])).
% 4.07/1.76  tff(c_397, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_382, c_235])).
% 4.07/1.76  tff(c_415, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_397])).
% 4.07/1.76  tff(c_434, plain, (r1_tarski('#skF_4', k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_415, c_18])).
% 4.07/1.76  tff(c_447, plain, (r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_156, c_434])).
% 4.07/1.76  tff(c_449, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitLeft, [status(thm)], [c_447])).
% 4.07/1.76  tff(c_452, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_449])).
% 4.07/1.76  tff(c_456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_452])).
% 4.07/1.76  tff(c_458, plain, (v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitRight, [status(thm)], [c_447])).
% 4.07/1.76  tff(c_12, plain, (![A_14]: (k9_relat_1(A_14, k1_relat_1(A_14))=k2_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.07/1.76  tff(c_174, plain, (k9_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_4')=k2_relat_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_156, c_12])).
% 4.07/1.76  tff(c_501, plain, (k9_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_4')=k2_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_458, c_174])).
% 4.07/1.76  tff(c_255, plain, (![A_66, B_67]: (k10_relat_1(A_66, k1_relat_1(B_67))=k1_relat_1(k5_relat_1(A_66, B_67)) | ~v1_relat_1(B_67) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.07/1.76  tff(c_32, plain, (![B_31, A_30]: (r1_tarski(k9_relat_1(B_31, k10_relat_1(B_31, A_30)), A_30) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.07/1.76  tff(c_919, plain, (![A_109, B_110]: (r1_tarski(k9_relat_1(A_109, k1_relat_1(k5_relat_1(A_109, B_110))), k1_relat_1(B_110)) | ~v1_funct_1(A_109) | ~v1_relat_1(A_109) | ~v1_relat_1(B_110) | ~v1_relat_1(A_109))), inference(superposition, [status(thm), theory('equality')], [c_255, c_32])).
% 4.07/1.76  tff(c_949, plain, (r1_tarski(k9_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_4'), k1_relat_1('#skF_2')) | ~v1_funct_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_415, c_919])).
% 4.07/1.76  tff(c_969, plain, (r1_tarski(k2_relat_1(k7_relat_1('#skF_1', '#skF_4')), k1_relat_1('#skF_2')) | ~v1_funct_1(k7_relat_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_458, c_38, c_458, c_501, c_949])).
% 4.07/1.76  tff(c_978, plain, (~v1_funct_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitLeft, [status(thm)], [c_969])).
% 4.07/1.76  tff(c_981, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_281, c_978])).
% 4.07/1.76  tff(c_985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_981])).
% 4.07/1.76  tff(c_986, plain, (r1_tarski(k2_relat_1(k7_relat_1('#skF_1', '#skF_4')), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_969])).
% 4.07/1.76  tff(c_1086, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_986])).
% 4.07/1.76  tff(c_1092, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1086])).
% 4.07/1.76  tff(c_1094, plain, $false, inference(negUnitSimplification, [status(thm)], [c_300, c_1092])).
% 4.07/1.76  tff(c_1096, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_299])).
% 4.07/1.76  tff(c_44, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.07/1.76  tff(c_1262, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_1096, c_44])).
% 4.07/1.76  tff(c_16, plain, (![A_17, B_19]: (k10_relat_1(A_17, k1_relat_1(B_19))=k1_relat_1(k5_relat_1(A_17, B_19)) | ~v1_relat_1(B_19) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.07/1.76  tff(c_1095, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_299])).
% 4.07/1.76  tff(c_46, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.07/1.76  tff(c_1229, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_1096, c_46])).
% 4.07/1.76  tff(c_1348, plain, (![A_119, C_120, B_121]: (r1_tarski(A_119, k10_relat_1(C_120, B_121)) | ~r1_tarski(k9_relat_1(C_120, A_119), B_121) | ~r1_tarski(A_119, k1_relat_1(C_120)) | ~v1_funct_1(C_120) | ~v1_relat_1(C_120))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.07/1.76  tff(c_1357, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1229, c_1348])).
% 4.07/1.76  tff(c_1375, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1095, c_1357])).
% 4.07/1.76  tff(c_1385, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_1375])).
% 4.07/1.76  tff(c_1388, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_1385])).
% 4.07/1.76  tff(c_1390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1262, c_1388])).
% 4.07/1.76  tff(c_1392, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_54])).
% 4.07/1.76  tff(c_50, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.07/1.76  tff(c_1397, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_1392, c_50])).
% 4.07/1.76  tff(c_1391, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_54])).
% 4.07/1.76  tff(c_52, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.07/1.76  tff(c_1463, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1392, c_52])).
% 4.07/1.76  tff(c_1963, plain, (![A_168, C_169, B_170]: (r1_tarski(A_168, k10_relat_1(C_169, B_170)) | ~r1_tarski(k9_relat_1(C_169, A_168), B_170) | ~r1_tarski(A_168, k1_relat_1(C_169)) | ~v1_funct_1(C_169) | ~v1_relat_1(C_169))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.07/1.76  tff(c_1982, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1463, c_1963])).
% 4.07/1.76  tff(c_1998, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1391, c_1982])).
% 4.07/1.76  tff(c_2004, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_1998])).
% 4.07/1.76  tff(c_2007, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_2004])).
% 4.07/1.76  tff(c_2009, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1397, c_2007])).
% 4.07/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/1.76  
% 4.07/1.76  Inference rules
% 4.07/1.76  ----------------------
% 4.07/1.76  #Ref     : 0
% 4.07/1.76  #Sup     : 474
% 4.07/1.76  #Fact    : 0
% 4.07/1.76  #Define  : 0
% 4.07/1.76  #Split   : 11
% 4.07/1.76  #Chain   : 0
% 4.07/1.76  #Close   : 0
% 4.07/1.76  
% 4.07/1.76  Ordering : KBO
% 4.07/1.76  
% 4.07/1.76  Simplification rules
% 4.07/1.76  ----------------------
% 4.07/1.76  #Subsume      : 25
% 4.07/1.76  #Demod        : 214
% 4.07/1.76  #Tautology    : 147
% 4.07/1.76  #SimpNegUnit  : 5
% 4.07/1.76  #BackRed      : 0
% 4.07/1.76  
% 4.07/1.76  #Partial instantiations: 0
% 4.07/1.76  #Strategies tried      : 1
% 4.07/1.76  
% 4.07/1.76  Timing (in seconds)
% 4.07/1.76  ----------------------
% 4.07/1.77  Preprocessing        : 0.35
% 4.07/1.77  Parsing              : 0.19
% 4.07/1.77  CNF conversion       : 0.02
% 4.07/1.77  Main loop            : 0.57
% 4.07/1.77  Inferencing          : 0.21
% 4.07/1.77  Reduction            : 0.18
% 4.07/1.77  Demodulation         : 0.13
% 4.07/1.77  BG Simplification    : 0.03
% 4.07/1.77  Subsumption          : 0.10
% 4.07/1.77  Abstraction          : 0.03
% 4.07/1.77  MUC search           : 0.00
% 4.07/1.77  Cooper               : 0.00
% 4.07/1.77  Total                : 0.95
% 4.07/1.77  Index Insertion      : 0.00
% 4.07/1.77  Index Deletion       : 0.00
% 4.07/1.77  Index Matching       : 0.00
% 4.07/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
