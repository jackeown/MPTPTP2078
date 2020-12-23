%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:30 EST 2020

% Result     : Theorem 5.10s
% Output     : CNFRefutation 5.10s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 177 expanded)
%              Number of leaves         :   35 (  78 expanded)
%              Depth                    :   18
%              Number of atoms          :  132 ( 280 expanded)
%              Number of equality atoms :   38 ( 101 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_99,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_44,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_46,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_30,plain,(
    ! [A_23] : v1_relat_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    ! [A_23] : v1_funct_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_289,plain,(
    ! [B_74,A_75] : k5_relat_1(k6_relat_1(B_74),k6_relat_1(A_75)) = k6_relat_1(k3_xboole_0(A_75,B_74)) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( k5_relat_1(k6_relat_1(A_21),B_22) = k7_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_295,plain,(
    ! [A_75,B_74] :
      ( k7_relat_1(k6_relat_1(A_75),B_74) = k6_relat_1(k3_xboole_0(A_75,B_74))
      | ~ v1_relat_1(k6_relat_1(A_75)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_28])).

tff(c_305,plain,(
    ! [A_75,B_74] : k7_relat_1(k6_relat_1(A_75),B_74) = k6_relat_1(k3_xboole_0(A_75,B_74)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_295])).

tff(c_319,plain,(
    ! [B_78,A_79] :
      ( k2_relat_1(k7_relat_1(B_78,A_79)) = k9_relat_1(B_78,A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_331,plain,(
    ! [A_75,B_74] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_75,B_74))) = k9_relat_1(k6_relat_1(A_75),B_74)
      | ~ v1_relat_1(k6_relat_1(A_75)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_319])).

tff(c_335,plain,(
    ! [A_75,B_74] : k9_relat_1(k6_relat_1(A_75),B_74) = k3_xboole_0(A_75,B_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_331])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1695,plain,(
    ! [A_159,C_160,B_161] :
      ( r1_tarski(A_159,k10_relat_1(C_160,B_161))
      | ~ r1_tarski(k9_relat_1(C_160,A_159),B_161)
      | ~ r1_tarski(A_159,k1_relat_1(C_160))
      | ~ v1_funct_1(C_160)
      | ~ v1_relat_1(C_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3794,plain,(
    ! [A_236,C_237] :
      ( r1_tarski(A_236,k10_relat_1(C_237,k9_relat_1(C_237,A_236)))
      | ~ r1_tarski(A_236,k1_relat_1(C_237))
      | ~ v1_funct_1(C_237)
      | ~ v1_relat_1(C_237) ) ),
    inference(resolution,[status(thm)],[c_6,c_1695])).

tff(c_118,plain,(
    ! [A_55] :
      ( k10_relat_1(A_55,k2_relat_1(A_55)) = k1_relat_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_134,plain,(
    ! [A_20] :
      ( k10_relat_1(k6_relat_1(A_20),A_20) = k1_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_118])).

tff(c_141,plain,(
    ! [A_20] : k10_relat_1(k6_relat_1(A_20),A_20) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_134])).

tff(c_620,plain,(
    ! [B_111,A_112] :
      ( k9_relat_1(B_111,k10_relat_1(B_111,A_112)) = A_112
      | ~ r1_tarski(A_112,k2_relat_1(B_111))
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2556,plain,(
    ! [B_200] :
      ( k9_relat_1(B_200,k10_relat_1(B_200,k2_relat_1(B_200))) = k2_relat_1(B_200)
      | ~ v1_funct_1(B_200)
      | ~ v1_relat_1(B_200) ) ),
    inference(resolution,[status(thm)],[c_6,c_620])).

tff(c_2585,plain,(
    ! [A_20] :
      ( k9_relat_1(k6_relat_1(A_20),k10_relat_1(k6_relat_1(A_20),A_20)) = k2_relat_1(k6_relat_1(A_20))
      | ~ v1_funct_1(k6_relat_1(A_20))
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2556])).

tff(c_2594,plain,(
    ! [A_20] : k3_xboole_0(A_20,A_20) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_335,c_141,c_26,c_2585])).

tff(c_34,plain,(
    ! [A_24,C_26,B_25] :
      ( k3_xboole_0(A_24,k10_relat_1(C_26,B_25)) = k10_relat_1(k7_relat_1(C_26,A_24),B_25)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1188,plain,(
    ! [A_133,B_134] :
      ( k3_xboole_0(A_133,k9_relat_1(B_134,k1_relat_1(B_134))) = k9_relat_1(B_134,k10_relat_1(B_134,A_133))
      | ~ v1_funct_1(B_134)
      | ~ v1_relat_1(B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1948,plain,(
    ! [B_175,A_176] :
      ( r1_tarski(k9_relat_1(B_175,k10_relat_1(B_175,A_176)),A_176)
      | ~ v1_funct_1(B_175)
      | ~ v1_relat_1(B_175) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1188,c_8])).

tff(c_1984,plain,(
    ! [A_75,A_176] :
      ( r1_tarski(k3_xboole_0(A_75,k10_relat_1(k6_relat_1(A_75),A_176)),A_176)
      | ~ v1_funct_1(k6_relat_1(A_75))
      | ~ v1_relat_1(k6_relat_1(A_75)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_1948])).

tff(c_2008,plain,(
    ! [A_177,A_178] : r1_tarski(k3_xboole_0(A_177,k10_relat_1(k6_relat_1(A_177),A_178)),A_178) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_1984])).

tff(c_2041,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(k10_relat_1(k7_relat_1(k6_relat_1(A_24),A_24),B_25),B_25)
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2008])).

tff(c_2059,plain,(
    ! [A_24,B_25] : r1_tarski(k10_relat_1(k6_relat_1(k3_xboole_0(A_24,A_24)),B_25),B_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_305,c_2041])).

tff(c_2950,plain,(
    ! [A_204,B_205] : r1_tarski(k10_relat_1(k6_relat_1(A_204),B_205),B_205) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2594,c_2059])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2997,plain,(
    ! [A_5,B_205,A_204] :
      ( r1_tarski(A_5,B_205)
      | ~ r1_tarski(A_5,k10_relat_1(k6_relat_1(A_204),B_205)) ) ),
    inference(resolution,[status(thm)],[c_2950,c_10])).

tff(c_3798,plain,(
    ! [A_236,A_204] :
      ( r1_tarski(A_236,k9_relat_1(k6_relat_1(A_204),A_236))
      | ~ r1_tarski(A_236,k1_relat_1(k6_relat_1(A_204)))
      | ~ v1_funct_1(k6_relat_1(A_204))
      | ~ v1_relat_1(k6_relat_1(A_204)) ) ),
    inference(resolution,[status(thm)],[c_3794,c_2997])).

tff(c_3840,plain,(
    ! [A_238,A_239] :
      ( r1_tarski(A_238,k3_xboole_0(A_239,A_238))
      | ~ r1_tarski(A_238,A_239) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_24,c_335,c_3798])).

tff(c_22,plain,(
    ! [A_19] :
      ( k10_relat_1(A_19,k2_relat_1(A_19)) = k1_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_392,plain,(
    ! [A_90,C_91,B_92] :
      ( k3_xboole_0(A_90,k10_relat_1(C_91,B_92)) = k10_relat_1(k7_relat_1(C_91,A_90),B_92)
      | ~ v1_relat_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_468,plain,(
    ! [C_96,A_97,B_98] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_96,A_97),B_98),A_97)
      | ~ v1_relat_1(C_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_8])).

tff(c_487,plain,(
    ! [A_75,B_74,B_98] :
      ( r1_tarski(k10_relat_1(k6_relat_1(k3_xboole_0(A_75,B_74)),B_98),B_74)
      | ~ v1_relat_1(k6_relat_1(A_75)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_468])).

tff(c_499,plain,(
    ! [A_99,B_100,B_101] : r1_tarski(k10_relat_1(k6_relat_1(k3_xboole_0(A_99,B_100)),B_101),B_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_487])).

tff(c_526,plain,(
    ! [A_99,B_100] :
      ( r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(A_99,B_100))),B_100)
      | ~ v1_relat_1(k6_relat_1(k3_xboole_0(A_99,B_100))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_499])).

tff(c_549,plain,(
    ! [A_104,B_105] : r1_tarski(k3_xboole_0(A_104,B_105),B_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_526])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_573,plain,(
    ! [A_104,B_105] :
      ( k3_xboole_0(A_104,B_105) = B_105
      | ~ r1_tarski(B_105,k3_xboole_0(A_104,B_105)) ) ),
    inference(resolution,[status(thm)],[c_549,c_2])).

tff(c_4107,plain,(
    ! [A_242,A_243] :
      ( k3_xboole_0(A_242,A_243) = A_243
      | ~ r1_tarski(A_243,A_242) ) ),
    inference(resolution,[status(thm)],[c_3840,c_573])).

tff(c_4308,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_4107])).

tff(c_4403,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4308,c_34])).

tff(c_4458,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4403])).

tff(c_4460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_4458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.10/2.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/2.02  
% 5.10/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/2.02  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.10/2.02  
% 5.10/2.02  %Foreground sorts:
% 5.10/2.02  
% 5.10/2.02  
% 5.10/2.02  %Background operators:
% 5.10/2.02  
% 5.10/2.02  
% 5.10/2.02  %Foreground operators:
% 5.10/2.02  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.10/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.10/2.02  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.10/2.02  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.10/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.10/2.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.10/2.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.10/2.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.10/2.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.10/2.02  tff('#skF_2', type, '#skF_2': $i).
% 5.10/2.02  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.10/2.02  tff('#skF_3', type, '#skF_3': $i).
% 5.10/2.02  tff('#skF_1', type, '#skF_1': $i).
% 5.10/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.10/2.02  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.10/2.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.10/2.02  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.10/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.10/2.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.10/2.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.10/2.02  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.10/2.02  
% 5.10/2.04  tff(f_109, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 5.10/2.04  tff(f_69, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.10/2.04  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.10/2.04  tff(f_99, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 5.10/2.04  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 5.10/2.04  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 5.10/2.04  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.10/2.04  tff(f_97, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 5.10/2.04  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 5.10/2.04  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 5.10/2.04  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 5.10/2.04  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 5.10/2.04  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.10/2.04  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.10/2.04  tff(c_44, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.10/2.04  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.10/2.04  tff(c_46, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.10/2.04  tff(c_30, plain, (![A_23]: (v1_relat_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.10/2.04  tff(c_32, plain, (![A_23]: (v1_funct_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.10/2.04  tff(c_24, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.10/2.04  tff(c_26, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.10/2.04  tff(c_289, plain, (![B_74, A_75]: (k5_relat_1(k6_relat_1(B_74), k6_relat_1(A_75))=k6_relat_1(k3_xboole_0(A_75, B_74)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.10/2.04  tff(c_28, plain, (![A_21, B_22]: (k5_relat_1(k6_relat_1(A_21), B_22)=k7_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.10/2.04  tff(c_295, plain, (![A_75, B_74]: (k7_relat_1(k6_relat_1(A_75), B_74)=k6_relat_1(k3_xboole_0(A_75, B_74)) | ~v1_relat_1(k6_relat_1(A_75)))), inference(superposition, [status(thm), theory('equality')], [c_289, c_28])).
% 5.10/2.04  tff(c_305, plain, (![A_75, B_74]: (k7_relat_1(k6_relat_1(A_75), B_74)=k6_relat_1(k3_xboole_0(A_75, B_74)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_295])).
% 5.10/2.04  tff(c_319, plain, (![B_78, A_79]: (k2_relat_1(k7_relat_1(B_78, A_79))=k9_relat_1(B_78, A_79) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.10/2.04  tff(c_331, plain, (![A_75, B_74]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_75, B_74)))=k9_relat_1(k6_relat_1(A_75), B_74) | ~v1_relat_1(k6_relat_1(A_75)))), inference(superposition, [status(thm), theory('equality')], [c_305, c_319])).
% 5.10/2.04  tff(c_335, plain, (![A_75, B_74]: (k9_relat_1(k6_relat_1(A_75), B_74)=k3_xboole_0(A_75, B_74))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_331])).
% 5.10/2.04  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.10/2.04  tff(c_1695, plain, (![A_159, C_160, B_161]: (r1_tarski(A_159, k10_relat_1(C_160, B_161)) | ~r1_tarski(k9_relat_1(C_160, A_159), B_161) | ~r1_tarski(A_159, k1_relat_1(C_160)) | ~v1_funct_1(C_160) | ~v1_relat_1(C_160))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.10/2.04  tff(c_3794, plain, (![A_236, C_237]: (r1_tarski(A_236, k10_relat_1(C_237, k9_relat_1(C_237, A_236))) | ~r1_tarski(A_236, k1_relat_1(C_237)) | ~v1_funct_1(C_237) | ~v1_relat_1(C_237))), inference(resolution, [status(thm)], [c_6, c_1695])).
% 5.10/2.04  tff(c_118, plain, (![A_55]: (k10_relat_1(A_55, k2_relat_1(A_55))=k1_relat_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.10/2.04  tff(c_134, plain, (![A_20]: (k10_relat_1(k6_relat_1(A_20), A_20)=k1_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_118])).
% 5.10/2.04  tff(c_141, plain, (![A_20]: (k10_relat_1(k6_relat_1(A_20), A_20)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_134])).
% 5.10/2.04  tff(c_620, plain, (![B_111, A_112]: (k9_relat_1(B_111, k10_relat_1(B_111, A_112))=A_112 | ~r1_tarski(A_112, k2_relat_1(B_111)) | ~v1_funct_1(B_111) | ~v1_relat_1(B_111))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.10/2.04  tff(c_2556, plain, (![B_200]: (k9_relat_1(B_200, k10_relat_1(B_200, k2_relat_1(B_200)))=k2_relat_1(B_200) | ~v1_funct_1(B_200) | ~v1_relat_1(B_200))), inference(resolution, [status(thm)], [c_6, c_620])).
% 5.10/2.04  tff(c_2585, plain, (![A_20]: (k9_relat_1(k6_relat_1(A_20), k10_relat_1(k6_relat_1(A_20), A_20))=k2_relat_1(k6_relat_1(A_20)) | ~v1_funct_1(k6_relat_1(A_20)) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2556])).
% 5.10/2.04  tff(c_2594, plain, (![A_20]: (k3_xboole_0(A_20, A_20)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_335, c_141, c_26, c_2585])).
% 5.10/2.04  tff(c_34, plain, (![A_24, C_26, B_25]: (k3_xboole_0(A_24, k10_relat_1(C_26, B_25))=k10_relat_1(k7_relat_1(C_26, A_24), B_25) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.10/2.04  tff(c_1188, plain, (![A_133, B_134]: (k3_xboole_0(A_133, k9_relat_1(B_134, k1_relat_1(B_134)))=k9_relat_1(B_134, k10_relat_1(B_134, A_133)) | ~v1_funct_1(B_134) | ~v1_relat_1(B_134))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.10/2.04  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.10/2.04  tff(c_1948, plain, (![B_175, A_176]: (r1_tarski(k9_relat_1(B_175, k10_relat_1(B_175, A_176)), A_176) | ~v1_funct_1(B_175) | ~v1_relat_1(B_175))), inference(superposition, [status(thm), theory('equality')], [c_1188, c_8])).
% 5.10/2.04  tff(c_1984, plain, (![A_75, A_176]: (r1_tarski(k3_xboole_0(A_75, k10_relat_1(k6_relat_1(A_75), A_176)), A_176) | ~v1_funct_1(k6_relat_1(A_75)) | ~v1_relat_1(k6_relat_1(A_75)))), inference(superposition, [status(thm), theory('equality')], [c_335, c_1948])).
% 5.10/2.04  tff(c_2008, plain, (![A_177, A_178]: (r1_tarski(k3_xboole_0(A_177, k10_relat_1(k6_relat_1(A_177), A_178)), A_178))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_1984])).
% 5.10/2.04  tff(c_2041, plain, (![A_24, B_25]: (r1_tarski(k10_relat_1(k7_relat_1(k6_relat_1(A_24), A_24), B_25), B_25) | ~v1_relat_1(k6_relat_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2008])).
% 5.10/2.04  tff(c_2059, plain, (![A_24, B_25]: (r1_tarski(k10_relat_1(k6_relat_1(k3_xboole_0(A_24, A_24)), B_25), B_25))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_305, c_2041])).
% 5.10/2.04  tff(c_2950, plain, (![A_204, B_205]: (r1_tarski(k10_relat_1(k6_relat_1(A_204), B_205), B_205))), inference(demodulation, [status(thm), theory('equality')], [c_2594, c_2059])).
% 5.10/2.04  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.10/2.04  tff(c_2997, plain, (![A_5, B_205, A_204]: (r1_tarski(A_5, B_205) | ~r1_tarski(A_5, k10_relat_1(k6_relat_1(A_204), B_205)))), inference(resolution, [status(thm)], [c_2950, c_10])).
% 5.10/2.04  tff(c_3798, plain, (![A_236, A_204]: (r1_tarski(A_236, k9_relat_1(k6_relat_1(A_204), A_236)) | ~r1_tarski(A_236, k1_relat_1(k6_relat_1(A_204))) | ~v1_funct_1(k6_relat_1(A_204)) | ~v1_relat_1(k6_relat_1(A_204)))), inference(resolution, [status(thm)], [c_3794, c_2997])).
% 5.10/2.04  tff(c_3840, plain, (![A_238, A_239]: (r1_tarski(A_238, k3_xboole_0(A_239, A_238)) | ~r1_tarski(A_238, A_239))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_24, c_335, c_3798])).
% 5.10/2.04  tff(c_22, plain, (![A_19]: (k10_relat_1(A_19, k2_relat_1(A_19))=k1_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.10/2.04  tff(c_392, plain, (![A_90, C_91, B_92]: (k3_xboole_0(A_90, k10_relat_1(C_91, B_92))=k10_relat_1(k7_relat_1(C_91, A_90), B_92) | ~v1_relat_1(C_91))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.10/2.04  tff(c_468, plain, (![C_96, A_97, B_98]: (r1_tarski(k10_relat_1(k7_relat_1(C_96, A_97), B_98), A_97) | ~v1_relat_1(C_96))), inference(superposition, [status(thm), theory('equality')], [c_392, c_8])).
% 5.10/2.04  tff(c_487, plain, (![A_75, B_74, B_98]: (r1_tarski(k10_relat_1(k6_relat_1(k3_xboole_0(A_75, B_74)), B_98), B_74) | ~v1_relat_1(k6_relat_1(A_75)))), inference(superposition, [status(thm), theory('equality')], [c_305, c_468])).
% 5.10/2.04  tff(c_499, plain, (![A_99, B_100, B_101]: (r1_tarski(k10_relat_1(k6_relat_1(k3_xboole_0(A_99, B_100)), B_101), B_100))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_487])).
% 5.10/2.04  tff(c_526, plain, (![A_99, B_100]: (r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(A_99, B_100))), B_100) | ~v1_relat_1(k6_relat_1(k3_xboole_0(A_99, B_100))))), inference(superposition, [status(thm), theory('equality')], [c_22, c_499])).
% 5.10/2.04  tff(c_549, plain, (![A_104, B_105]: (r1_tarski(k3_xboole_0(A_104, B_105), B_105))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_526])).
% 5.10/2.04  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.10/2.04  tff(c_573, plain, (![A_104, B_105]: (k3_xboole_0(A_104, B_105)=B_105 | ~r1_tarski(B_105, k3_xboole_0(A_104, B_105)))), inference(resolution, [status(thm)], [c_549, c_2])).
% 5.10/2.04  tff(c_4107, plain, (![A_242, A_243]: (k3_xboole_0(A_242, A_243)=A_243 | ~r1_tarski(A_243, A_242))), inference(resolution, [status(thm)], [c_3840, c_573])).
% 5.10/2.04  tff(c_4308, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_4107])).
% 5.10/2.04  tff(c_4403, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4308, c_34])).
% 5.10/2.04  tff(c_4458, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4403])).
% 5.10/2.04  tff(c_4460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_4458])).
% 5.10/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/2.04  
% 5.10/2.04  Inference rules
% 5.10/2.04  ----------------------
% 5.10/2.04  #Ref     : 0
% 5.10/2.04  #Sup     : 1017
% 5.10/2.04  #Fact    : 0
% 5.10/2.04  #Define  : 0
% 5.10/2.04  #Split   : 1
% 5.10/2.04  #Chain   : 0
% 5.10/2.04  #Close   : 0
% 5.10/2.04  
% 5.10/2.04  Ordering : KBO
% 5.10/2.04  
% 5.10/2.04  Simplification rules
% 5.10/2.04  ----------------------
% 5.10/2.04  #Subsume      : 18
% 5.10/2.04  #Demod        : 531
% 5.10/2.04  #Tautology    : 390
% 5.10/2.04  #SimpNegUnit  : 1
% 5.10/2.04  #BackRed      : 1
% 5.10/2.04  
% 5.10/2.04  #Partial instantiations: 0
% 5.10/2.04  #Strategies tried      : 1
% 5.10/2.04  
% 5.10/2.04  Timing (in seconds)
% 5.10/2.04  ----------------------
% 5.10/2.04  Preprocessing        : 0.33
% 5.10/2.04  Parsing              : 0.18
% 5.10/2.04  CNF conversion       : 0.02
% 5.10/2.04  Main loop            : 0.95
% 5.10/2.04  Inferencing          : 0.27
% 5.10/2.04  Reduction            : 0.39
% 5.10/2.04  Demodulation         : 0.31
% 5.10/2.04  BG Simplification    : 0.04
% 5.10/2.04  Subsumption          : 0.18
% 5.10/2.04  Abstraction          : 0.05
% 5.10/2.04  MUC search           : 0.00
% 5.10/2.04  Cooper               : 0.00
% 5.10/2.04  Total                : 1.31
% 5.10/2.04  Index Insertion      : 0.00
% 5.10/2.04  Index Deletion       : 0.00
% 5.10/2.04  Index Matching       : 0.00
% 5.10/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
