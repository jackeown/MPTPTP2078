%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:39 EST 2020

% Result     : Theorem 4.65s
% Output     : CNFRefutation 4.65s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 264 expanded)
%              Number of leaves         :   28 (  96 expanded)
%              Depth                    :   13
%              Number of atoms          :  203 ( 794 expanded)
%              Number of equality atoms :   19 (  49 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_120,negated_conjecture,(
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

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_30,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_18,plain,(
    ! [A_22,B_23] :
      ( v1_funct_1(k7_relat_1(A_22,B_23))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_170,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_44,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_58,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_66,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_46,B_47)),k1_relat_1(A_46))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_264,plain,(
    ! [A_61,A_62,B_63] :
      ( r1_tarski(A_61,k1_relat_1(A_62))
      | ~ r1_tarski(A_61,k1_relat_1(k5_relat_1(A_62,B_63)))
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(A_62) ) ),
    inference(resolution,[status(thm)],[c_66,c_2])).

tff(c_277,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_264])).

tff(c_286,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_277])).

tff(c_288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_286])).

tff(c_290,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_16,plain,(
    ! [B_21,A_20] :
      ( k1_relat_1(k7_relat_1(B_21,A_20)) = A_20
      | ~ r1_tarski(A_20,k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_295,plain,
    ( k1_relat_1(k7_relat_1('#skF_1','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_290,c_16])).

tff(c_302,plain,(
    k1_relat_1(k7_relat_1('#skF_1','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_295])).

tff(c_129,plain,(
    ! [B_54,C_55,A_56] :
      ( k7_relat_1(k5_relat_1(B_54,C_55),A_56) = k5_relat_1(k7_relat_1(B_54,A_56),C_55)
      | ~ v1_relat_1(C_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k5_relat_1(A_4,B_5))
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_70,plain,(
    ! [B_48,A_49] :
      ( k1_relat_1(k7_relat_1(B_48,A_49)) = A_49
      | ~ r1_tarski(A_49,k1_relat_1(B_48))
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_82,plain,
    ( k1_relat_1(k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_4')) = '#skF_4'
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_70])).

tff(c_83,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_87,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_83])).

tff(c_91,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_87])).

tff(c_92,plain,(
    k1_relat_1(k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_135,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_92])).

tff(c_150,plain,(
    k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_135])).

tff(c_14,plain,(
    ! [A_17,B_19] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_17,B_19)),k1_relat_1(A_17))
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_161,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k7_relat_1('#skF_1','#skF_4')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_14])).

tff(c_168,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k7_relat_1('#skF_1','#skF_4')))
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_161])).

tff(c_379,plain,
    ( r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_168])).

tff(c_380,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_379])).

tff(c_383,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_380])).

tff(c_387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_383])).

tff(c_389,plain,(
    v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_379])).

tff(c_10,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_707,plain,(
    ! [B_90,A_91] :
      ( r1_tarski(k2_relat_1(B_90),k1_relat_1(A_91))
      | k1_relat_1(k5_relat_1(B_90,A_91)) != k1_relat_1(B_90)
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1825,plain,(
    ! [B_124,A_125,A_126] :
      ( r1_tarski(k9_relat_1(B_124,A_125),k1_relat_1(A_126))
      | k1_relat_1(k5_relat_1(k7_relat_1(B_124,A_125),A_126)) != k1_relat_1(k7_relat_1(B_124,A_125))
      | ~ v1_funct_1(k7_relat_1(B_124,A_125))
      | ~ v1_relat_1(k7_relat_1(B_124,A_125))
      | ~ v1_funct_1(A_126)
      | ~ v1_relat_1(A_126)
      | ~ v1_relat_1(B_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_707])).

tff(c_36,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_305,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_36])).

tff(c_306,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_305])).

tff(c_1845,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) != k1_relat_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1825,c_306])).

tff(c_1908,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_26,c_389,c_150,c_302,c_1845])).

tff(c_1922,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_1908])).

tff(c_1926,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1922])).

tff(c_1928,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_305])).

tff(c_34,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1955,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_34])).

tff(c_1956,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1955])).

tff(c_1970,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1928,c_1956])).

tff(c_1971,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1955])).

tff(c_12,plain,(
    ! [A_14,B_16] :
      ( k10_relat_1(A_14,k1_relat_1(B_16)) = k1_relat_1(k5_relat_1(A_14,B_16))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_289,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2031,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1928,c_289])).

tff(c_1927,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_305])).

tff(c_2133,plain,(
    ! [A_132,C_133,B_134] :
      ( r1_tarski(A_132,k10_relat_1(C_133,B_134))
      | ~ r1_tarski(k9_relat_1(C_133,A_132),B_134)
      | ~ r1_tarski(A_132,k1_relat_1(C_133))
      | ~ v1_funct_1(C_133)
      | ~ v1_relat_1(C_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2147,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1927,c_2133])).

tff(c_2159,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_2031,c_2147])).

tff(c_2179,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2159])).

tff(c_2185,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_2179])).

tff(c_2187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1971,c_2185])).

tff(c_2189,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_40,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2250,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2189,c_40])).

tff(c_2188,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2193,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_2194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2189,c_2193])).

tff(c_2195,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2527,plain,(
    ! [A_163,C_164,B_165] :
      ( r1_tarski(A_163,k10_relat_1(C_164,B_165))
      | ~ r1_tarski(k9_relat_1(C_164,A_163),B_165)
      | ~ r1_tarski(A_163,k1_relat_1(C_164))
      | ~ v1_funct_1(C_164)
      | ~ v1_relat_1(C_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2534,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2195,c_2527])).

tff(c_2538,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_2188,c_2534])).

tff(c_2545,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2538])).

tff(c_2550,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_2545])).

tff(c_2552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2250,c_2550])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:57:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.65/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.65/1.94  
% 4.65/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.65/1.94  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.65/1.94  
% 4.65/1.94  %Foreground sorts:
% 4.65/1.94  
% 4.65/1.94  
% 4.65/1.94  %Background operators:
% 4.65/1.94  
% 4.65/1.94  
% 4.65/1.94  %Foreground operators:
% 4.65/1.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.65/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.65/1.94  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.65/1.94  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.65/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.65/1.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.65/1.94  tff('#skF_2', type, '#skF_2': $i).
% 4.65/1.94  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.65/1.94  tff('#skF_3', type, '#skF_3': $i).
% 4.65/1.94  tff('#skF_1', type, '#skF_1': $i).
% 4.65/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.65/1.94  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.65/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.65/1.94  tff('#skF_4', type, '#skF_4': $i).
% 4.65/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.65/1.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.65/1.94  
% 4.65/1.96  tff(f_120, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 4.65/1.96  tff(f_80, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 4.65/1.96  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.65/1.96  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 4.65/1.96  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.65/1.96  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 4.65/1.96  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 4.65/1.96  tff(f_37, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 4.65/1.96  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.65/1.96  tff(f_103, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 4.65/1.96  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 4.65/1.96  tff(f_90, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 4.65/1.96  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.65/1.96  tff(c_30, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.65/1.96  tff(c_18, plain, (![A_22, B_23]: (v1_funct_1(k7_relat_1(A_22, B_23)) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.65/1.96  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.65/1.96  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.65/1.96  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.65/1.96  tff(c_38, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.65/1.96  tff(c_170, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_38])).
% 4.65/1.96  tff(c_44, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.65/1.96  tff(c_58, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_44])).
% 4.65/1.96  tff(c_66, plain, (![A_46, B_47]: (r1_tarski(k1_relat_1(k5_relat_1(A_46, B_47)), k1_relat_1(A_46)) | ~v1_relat_1(B_47) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.65/1.96  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.65/1.96  tff(c_264, plain, (![A_61, A_62, B_63]: (r1_tarski(A_61, k1_relat_1(A_62)) | ~r1_tarski(A_61, k1_relat_1(k5_relat_1(A_62, B_63))) | ~v1_relat_1(B_63) | ~v1_relat_1(A_62))), inference(resolution, [status(thm)], [c_66, c_2])).
% 4.65/1.96  tff(c_277, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_58, c_264])).
% 4.65/1.96  tff(c_286, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_277])).
% 4.65/1.96  tff(c_288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_286])).
% 4.65/1.96  tff(c_290, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_38])).
% 4.65/1.96  tff(c_16, plain, (![B_21, A_20]: (k1_relat_1(k7_relat_1(B_21, A_20))=A_20 | ~r1_tarski(A_20, k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.65/1.96  tff(c_295, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_290, c_16])).
% 4.65/1.96  tff(c_302, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_295])).
% 4.65/1.96  tff(c_129, plain, (![B_54, C_55, A_56]: (k7_relat_1(k5_relat_1(B_54, C_55), A_56)=k5_relat_1(k7_relat_1(B_54, A_56), C_55) | ~v1_relat_1(C_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.65/1.96  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k5_relat_1(A_4, B_5)) | ~v1_relat_1(B_5) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.65/1.96  tff(c_70, plain, (![B_48, A_49]: (k1_relat_1(k7_relat_1(B_48, A_49))=A_49 | ~r1_tarski(A_49, k1_relat_1(B_48)) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.65/1.96  tff(c_82, plain, (k1_relat_1(k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_4'))='#skF_4' | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_70])).
% 4.65/1.96  tff(c_83, plain, (~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_82])).
% 4.65/1.96  tff(c_87, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_83])).
% 4.65/1.96  tff(c_91, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_87])).
% 4.65/1.96  tff(c_92, plain, (k1_relat_1(k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_82])).
% 4.65/1.96  tff(c_135, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_129, c_92])).
% 4.65/1.96  tff(c_150, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_135])).
% 4.65/1.96  tff(c_14, plain, (![A_17, B_19]: (r1_tarski(k1_relat_1(k5_relat_1(A_17, B_19)), k1_relat_1(A_17)) | ~v1_relat_1(B_19) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.65/1.96  tff(c_161, plain, (r1_tarski('#skF_4', k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_150, c_14])).
% 4.65/1.96  tff(c_168, plain, (r1_tarski('#skF_4', k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))) | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_161])).
% 4.65/1.96  tff(c_379, plain, (r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_302, c_168])).
% 4.65/1.96  tff(c_380, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitLeft, [status(thm)], [c_379])).
% 4.65/1.96  tff(c_383, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_380])).
% 4.65/1.96  tff(c_387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_383])).
% 4.65/1.96  tff(c_389, plain, (v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitRight, [status(thm)], [c_379])).
% 4.65/1.96  tff(c_10, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.65/1.96  tff(c_707, plain, (![B_90, A_91]: (r1_tarski(k2_relat_1(B_90), k1_relat_1(A_91)) | k1_relat_1(k5_relat_1(B_90, A_91))!=k1_relat_1(B_90) | ~v1_funct_1(B_90) | ~v1_relat_1(B_90) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.65/1.96  tff(c_1825, plain, (![B_124, A_125, A_126]: (r1_tarski(k9_relat_1(B_124, A_125), k1_relat_1(A_126)) | k1_relat_1(k5_relat_1(k7_relat_1(B_124, A_125), A_126))!=k1_relat_1(k7_relat_1(B_124, A_125)) | ~v1_funct_1(k7_relat_1(B_124, A_125)) | ~v1_relat_1(k7_relat_1(B_124, A_125)) | ~v1_funct_1(A_126) | ~v1_relat_1(A_126) | ~v1_relat_1(B_124))), inference(superposition, [status(thm), theory('equality')], [c_10, c_707])).
% 4.65/1.96  tff(c_36, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.65/1.96  tff(c_305, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_290, c_36])).
% 4.65/1.96  tff(c_306, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_305])).
% 4.65/1.96  tff(c_1845, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))!=k1_relat_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_funct_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1825, c_306])).
% 4.65/1.96  tff(c_1908, plain, (~v1_funct_1(k7_relat_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_26, c_389, c_150, c_302, c_1845])).
% 4.65/1.96  tff(c_1922, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1908])).
% 4.65/1.96  tff(c_1926, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1922])).
% 4.65/1.96  tff(c_1928, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_305])).
% 4.65/1.96  tff(c_34, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.65/1.96  tff(c_1955, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_290, c_34])).
% 4.65/1.96  tff(c_1956, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1955])).
% 4.65/1.96  tff(c_1970, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1928, c_1956])).
% 4.65/1.96  tff(c_1971, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_1955])).
% 4.65/1.96  tff(c_12, plain, (![A_14, B_16]: (k10_relat_1(A_14, k1_relat_1(B_16))=k1_relat_1(k5_relat_1(A_14, B_16)) | ~v1_relat_1(B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.65/1.96  tff(c_289, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_38])).
% 4.65/1.96  tff(c_2031, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1928, c_289])).
% 4.65/1.96  tff(c_1927, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_305])).
% 4.65/1.96  tff(c_2133, plain, (![A_132, C_133, B_134]: (r1_tarski(A_132, k10_relat_1(C_133, B_134)) | ~r1_tarski(k9_relat_1(C_133, A_132), B_134) | ~r1_tarski(A_132, k1_relat_1(C_133)) | ~v1_funct_1(C_133) | ~v1_relat_1(C_133))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.65/1.96  tff(c_2147, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1927, c_2133])).
% 4.65/1.96  tff(c_2159, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_2031, c_2147])).
% 4.65/1.96  tff(c_2179, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12, c_2159])).
% 4.65/1.96  tff(c_2185, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_2179])).
% 4.65/1.96  tff(c_2187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1971, c_2185])).
% 4.65/1.96  tff(c_2189, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_44])).
% 4.65/1.96  tff(c_40, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.65/1.96  tff(c_2250, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_2189, c_40])).
% 4.65/1.96  tff(c_2188, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_44])).
% 4.65/1.96  tff(c_42, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.65/1.96  tff(c_2193, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_42])).
% 4.65/1.96  tff(c_2194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2189, c_2193])).
% 4.65/1.96  tff(c_2195, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_42])).
% 4.65/1.96  tff(c_2527, plain, (![A_163, C_164, B_165]: (r1_tarski(A_163, k10_relat_1(C_164, B_165)) | ~r1_tarski(k9_relat_1(C_164, A_163), B_165) | ~r1_tarski(A_163, k1_relat_1(C_164)) | ~v1_funct_1(C_164) | ~v1_relat_1(C_164))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.65/1.96  tff(c_2534, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2195, c_2527])).
% 4.65/1.96  tff(c_2538, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_2188, c_2534])).
% 4.65/1.96  tff(c_2545, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12, c_2538])).
% 4.65/1.96  tff(c_2550, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_2545])).
% 4.65/1.96  tff(c_2552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2250, c_2550])).
% 4.65/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.65/1.96  
% 4.65/1.96  Inference rules
% 4.65/1.96  ----------------------
% 4.65/1.96  #Ref     : 0
% 4.65/1.96  #Sup     : 578
% 4.65/1.96  #Fact    : 0
% 4.65/1.96  #Define  : 0
% 4.65/1.96  #Split   : 14
% 4.65/1.96  #Chain   : 0
% 4.65/1.96  #Close   : 0
% 4.65/1.96  
% 4.65/1.96  Ordering : KBO
% 4.65/1.96  
% 4.65/1.96  Simplification rules
% 4.65/1.96  ----------------------
% 4.65/1.96  #Subsume      : 50
% 4.65/1.96  #Demod        : 310
% 4.65/1.96  #Tautology    : 184
% 4.65/1.96  #SimpNegUnit  : 7
% 4.65/1.96  #BackRed      : 0
% 4.65/1.96  
% 4.65/1.96  #Partial instantiations: 0
% 4.65/1.96  #Strategies tried      : 1
% 4.65/1.96  
% 4.65/1.96  Timing (in seconds)
% 4.65/1.96  ----------------------
% 4.65/1.96  Preprocessing        : 0.31
% 4.65/1.96  Parsing              : 0.16
% 4.65/1.96  CNF conversion       : 0.02
% 4.65/1.96  Main loop            : 0.81
% 4.65/1.96  Inferencing          : 0.30
% 4.65/1.96  Reduction            : 0.24
% 4.65/1.96  Demodulation         : 0.17
% 4.65/1.96  BG Simplification    : 0.04
% 4.65/1.96  Subsumption          : 0.17
% 4.65/1.96  Abstraction          : 0.04
% 4.65/1.96  MUC search           : 0.00
% 4.65/1.96  Cooper               : 0.00
% 4.65/1.96  Total                : 1.16
% 4.65/1.96  Index Insertion      : 0.00
% 4.65/1.96  Index Deletion       : 0.00
% 4.65/1.96  Index Matching       : 0.00
% 4.65/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
