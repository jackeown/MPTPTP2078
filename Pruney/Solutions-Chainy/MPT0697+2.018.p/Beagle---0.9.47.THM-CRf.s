%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:00 EST 2020

% Result     : Theorem 28.06s
% Output     : CNFRefutation 28.24s
% Verified   : 
% Statistics : Number of formulae       :  136 (1549 expanded)
%              Number of leaves         :   27 ( 549 expanded)
%              Depth                    :   24
%              Number of atoms          :  276 (3192 expanded)
%              Number of equality atoms :  113 (1096 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( v2_funct_1(B)
         => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_16,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_64])).

tff(c_18,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [C_20,A_18,B_19] :
      ( k6_subset_1(k10_relat_1(C_20,A_18),k10_relat_1(C_20,B_19)) = k10_relat_1(C_20,k6_subset_1(A_18,B_19))
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_786,plain,(
    ! [C_81,A_82,B_83] :
      ( k4_xboole_0(k10_relat_1(C_81,A_82),k10_relat_1(C_81,B_83)) = k10_relat_1(C_81,k4_xboole_0(A_82,B_83))
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_24])).

tff(c_817,plain,(
    ! [C_81,B_83] :
      ( k10_relat_1(C_81,k4_xboole_0(B_83,B_83)) = k1_xboole_0
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_72])).

tff(c_838,plain,(
    ! [C_84] :
      ( k10_relat_1(C_84,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_84)
      | ~ v1_relat_1(C_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_817])).

tff(c_841,plain,
    ( k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_838])).

tff(c_844,plain,(
    k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_841])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_82,plain,(
    ! [B_35] : k4_xboole_0(B_35,B_35) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_64])).

tff(c_87,plain,(
    ! [B_35] : r1_tarski(k1_xboole_0,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_14])).

tff(c_226,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(A_45,C_46)
      | ~ r1_tarski(B_47,C_46)
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_258,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ r1_tarski(A_50,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_87,c_226])).

tff(c_267,plain,(
    ! [A_3,B_51] :
      ( r1_tarski(A_3,B_51)
      | k4_xboole_0(A_3,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_258])).

tff(c_285,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | k1_xboole_0 != A_52 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_267])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_369,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | k1_xboole_0 != A_59 ) ),
    inference(resolution,[status(thm)],[c_285,c_2])).

tff(c_396,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | k1_xboole_0 != A_8 ) ),
    inference(resolution,[status(thm)],[c_14,c_369])).

tff(c_4111,plain,(
    ! [C_180,A_181,B_182] :
      ( r1_tarski(k10_relat_1(C_180,k4_xboole_0(A_181,B_182)),k10_relat_1(C_180,A_181))
      | ~ v1_funct_1(C_180)
      | ~ v1_relat_1(C_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_14])).

tff(c_69384,plain,(
    ! [C_903,A_904,B_905] :
      ( k10_relat_1(C_903,k4_xboole_0(A_904,B_905)) = k10_relat_1(C_903,A_904)
      | ~ r1_tarski(k10_relat_1(C_903,A_904),k10_relat_1(C_903,k4_xboole_0(A_904,B_905)))
      | ~ v1_funct_1(C_903)
      | ~ v1_relat_1(C_903) ) ),
    inference(resolution,[status(thm)],[c_4111,c_2])).

tff(c_69591,plain,(
    ! [C_903,A_8,B_9] :
      ( k10_relat_1(C_903,k4_xboole_0(A_8,B_9)) = k10_relat_1(C_903,A_8)
      | ~ r1_tarski(k10_relat_1(C_903,A_8),k10_relat_1(C_903,A_8))
      | ~ v1_funct_1(C_903)
      | ~ v1_relat_1(C_903)
      | k1_xboole_0 != A_8 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_69384])).

tff(c_77099,plain,(
    ! [C_970,A_971,B_972] :
      ( k10_relat_1(C_970,k4_xboole_0(A_971,B_972)) = k10_relat_1(C_970,A_971)
      | ~ v1_funct_1(C_970)
      | ~ v1_relat_1(C_970)
      | k1_xboole_0 != A_971 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_69591])).

tff(c_78114,plain,(
    ! [C_979,B_980] :
      ( k10_relat_1(C_979,k1_xboole_0) = k10_relat_1(C_979,B_980)
      | ~ v1_funct_1(C_979)
      | ~ v1_relat_1(C_979)
      | k1_xboole_0 != B_980 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_77099])).

tff(c_78116,plain,(
    ! [B_980] :
      ( k10_relat_1('#skF_2',k1_xboole_0) = k10_relat_1('#skF_2',B_980)
      | ~ v1_funct_1('#skF_2')
      | k1_xboole_0 != B_980 ) ),
    inference(resolution,[status(thm)],[c_36,c_78114])).

tff(c_78122,plain,(
    ! [B_981] :
      ( k10_relat_1('#skF_2',B_981) = k1_xboole_0
      | k1_xboole_0 != B_981 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_844,c_78116])).

tff(c_37,plain,(
    ! [C_20,A_18,B_19] :
      ( k4_xboole_0(k10_relat_1(C_20,A_18),k10_relat_1(C_20,B_19)) = k10_relat_1(C_20,k4_xboole_0(A_18,B_19))
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_24])).

tff(c_78446,plain,(
    ! [A_18,B_981] :
      ( k4_xboole_0(k10_relat_1('#skF_2',A_18),k1_xboole_0) = k10_relat_1('#skF_2',k4_xboole_0(A_18,B_981))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != B_981 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78122,c_37])).

tff(c_81083,plain,(
    ! [A_996,B_997] :
      ( k10_relat_1('#skF_2',k4_xboole_0(A_996,B_997)) = k10_relat_1('#skF_2',A_996)
      | k1_xboole_0 != B_997 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_16,c_78446])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k10_relat_1(B_14,A_13),k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_81322,plain,(
    ! [A_996,B_997] :
      ( r1_tarski(k10_relat_1('#skF_2',A_996),k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != B_997 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81083,c_20])).

tff(c_81699,plain,(
    ! [A_996,B_997] :
      ( r1_tarski(k10_relat_1('#skF_2',A_996),k1_relat_1('#skF_2'))
      | k1_xboole_0 != B_997 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_81322])).

tff(c_81752,plain,(
    ! [B_997] : k1_xboole_0 != B_997 ),
    inference(splitLeft,[status(thm)],[c_81699])).

tff(c_452,plain,(
    ! [A_64,A_65,B_66] :
      ( r1_tarski(A_64,A_65)
      | ~ r1_tarski(A_64,k4_xboole_0(A_65,B_66)) ) ),
    inference(resolution,[status(thm)],[c_14,c_226])).

tff(c_494,plain,(
    ! [A_67,B_68,B_69] : r1_tarski(k4_xboole_0(k4_xboole_0(A_67,B_68),B_69),A_67) ),
    inference(resolution,[status(thm)],[c_14,c_452])).

tff(c_240,plain,(
    ! [A_45,A_8,B_9] :
      ( r1_tarski(A_45,A_8)
      | ~ r1_tarski(A_45,k4_xboole_0(A_8,B_9)) ) ),
    inference(resolution,[status(thm)],[c_14,c_226])).

tff(c_549,plain,(
    ! [A_8,B_9,B_68,B_69] : r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(A_8,B_9),B_68),B_69),A_8) ),
    inference(resolution,[status(thm)],[c_494,c_240])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2106,plain,(
    ! [A_134,A_135,B_136,B_137] :
      ( r1_tarski(A_134,A_135)
      | ~ r1_tarski(A_134,k4_xboole_0(k4_xboole_0(A_135,B_136),B_137)) ) ),
    inference(resolution,[status(thm)],[c_494,c_12])).

tff(c_22422,plain,(
    ! [A_424,B_425,B_421,B_422,B_423,B_426] : r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(A_424,B_422),B_426),B_425),B_421),B_423),A_424) ),
    inference(resolution,[status(thm)],[c_549,c_2106])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_23042,plain,(
    ! [A_424,B_425,B_421,B_422,B_423,B_426] : k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(A_424,B_422),B_426),B_425),B_421),B_423),A_424) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22422,c_10])).

tff(c_81814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81752,c_23042])).

tff(c_81816,plain,(
    ! [A_998] : r1_tarski(k10_relat_1('#skF_2',A_998),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_81699])).

tff(c_88754,plain,(
    ! [A_1030,A_1031] :
      ( r1_tarski(A_1030,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_1030,k10_relat_1('#skF_2',A_1031)) ) ),
    inference(resolution,[status(thm)],[c_81816,c_12])).

tff(c_89057,plain,(
    ! [A_1031,B_9] : r1_tarski(k4_xboole_0(k10_relat_1('#skF_2',A_1031),B_9),k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_88754])).

tff(c_69629,plain,(
    ! [C_903,A_8,B_9] :
      ( k10_relat_1(C_903,k4_xboole_0(A_8,B_9)) = k10_relat_1(C_903,A_8)
      | ~ v1_funct_1(C_903)
      | ~ v1_relat_1(C_903)
      | k1_xboole_0 != A_8 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_69591])).

tff(c_820,plain,(
    ! [C_81,A_82,B_83] :
      ( r1_tarski(k10_relat_1(C_81,k4_xboole_0(A_82,B_83)),k10_relat_1(C_81,A_82))
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_14])).

tff(c_78414,plain,(
    ! [B_981,B_83] :
      ( r1_tarski(k10_relat_1('#skF_2',k4_xboole_0(B_981,B_83)),k1_xboole_0)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != B_981 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78122,c_820])).

tff(c_80022,plain,(
    ! [B_988,B_989] :
      ( r1_tarski(k10_relat_1('#skF_2',k4_xboole_0(B_988,B_989)),k1_xboole_0)
      | k1_xboole_0 != B_988 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_78414])).

tff(c_80108,plain,(
    ! [A_8] :
      ( r1_tarski(k10_relat_1('#skF_2',A_8),k1_xboole_0)
      | k1_xboole_0 != A_8
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != A_8 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69629,c_80022])).

tff(c_80422,plain,(
    ! [A_990] :
      ( r1_tarski(k10_relat_1('#skF_2',A_990),k1_xboole_0)
      | k1_xboole_0 != A_990 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_80108])).

tff(c_680,plain,(
    ! [A_73,B_74,A_75] :
      ( r1_tarski(A_73,B_74)
      | ~ r1_tarski(A_73,A_75)
      | k1_xboole_0 != A_75 ) ),
    inference(resolution,[status(thm)],[c_285,c_12])).

tff(c_706,plain,(
    ! [A_76,B_77,B_78] :
      ( r1_tarski(k4_xboole_0(A_76,B_77),B_78)
      | k1_xboole_0 != A_76 ) ),
    inference(resolution,[status(thm)],[c_14,c_680])).

tff(c_306,plain,(
    ! [B_53,A_52] :
      ( B_53 = A_52
      | ~ r1_tarski(B_53,A_52)
      | k1_xboole_0 != A_52 ) ),
    inference(resolution,[status(thm)],[c_285,c_2])).

tff(c_1231,plain,(
    ! [B_77] : k4_xboole_0(k1_xboole_0,B_77) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_706,c_306])).

tff(c_71,plain,(
    ! [A_8,B_9] : k4_xboole_0(k4_xboole_0(A_8,B_9),A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_64])).

tff(c_1768,plain,(
    ! [A_117,B_118,A_119] :
      ( r1_tarski(A_117,B_118)
      | ~ r1_tarski(A_117,A_119)
      | k4_xboole_0(A_119,B_118) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_226])).

tff(c_1802,plain,(
    ! [A_120,B_121,B_122] :
      ( r1_tarski(k4_xboole_0(A_120,B_121),B_122)
      | k4_xboole_0(A_120,B_122) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_1768])).

tff(c_1880,plain,(
    ! [A_120,B_121,B_122] :
      ( k4_xboole_0(k4_xboole_0(A_120,B_121),B_122) = k1_xboole_0
      | k4_xboole_0(A_120,B_122) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1802,c_10])).

tff(c_16371,plain,(
    ! [A_364,B_365,B_366] :
      ( k4_xboole_0(k4_xboole_0(A_364,B_365),B_366) = A_364
      | ~ r1_tarski(A_364,k4_xboole_0(k4_xboole_0(A_364,B_365),B_366)) ) ),
    inference(resolution,[status(thm)],[c_494,c_2])).

tff(c_23558,plain,(
    ! [A_435,B_436,B_437] :
      ( k4_xboole_0(k4_xboole_0(A_435,B_436),B_437) = A_435
      | ~ r1_tarski(A_435,k1_xboole_0)
      | k4_xboole_0(A_435,B_437) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1880,c_16371])).

tff(c_25410,plain,(
    ! [A_450,B_451,B_452] :
      ( k4_xboole_0(A_450,k4_xboole_0(A_450,B_451)) = k1_xboole_0
      | ~ r1_tarski(A_450,k1_xboole_0)
      | k4_xboole_0(A_450,B_452) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23558,c_71])).

tff(c_25517,plain,(
    ! [B_453,B_454] :
      ( k4_xboole_0(B_453,k4_xboole_0(B_453,B_454)) = k1_xboole_0
      | ~ r1_tarski(B_453,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_25410])).

tff(c_1799,plain,(
    ! [A_3,B_118,B_4] :
      ( r1_tarski(A_3,B_118)
      | k4_xboole_0(B_4,B_118) != k1_xboole_0
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_1768])).

tff(c_26521,plain,(
    ! [A_457,B_458,B_459] :
      ( r1_tarski(A_457,k4_xboole_0(B_458,B_459))
      | k4_xboole_0(A_457,B_458) != k1_xboole_0
      | ~ r1_tarski(B_458,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25517,c_1799])).

tff(c_26865,plain,(
    ! [A_463,B_464] :
      ( r1_tarski(A_463,k1_xboole_0)
      | k4_xboole_0(A_463,B_464) != k1_xboole_0
      | ~ r1_tarski(B_464,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_26521])).

tff(c_26977,plain,(
    ! [A_465,B_466] :
      ( r1_tarski(k4_xboole_0(A_465,B_466),k1_xboole_0)
      | ~ r1_tarski(A_465,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_26865])).

tff(c_6999,plain,(
    ! [A_233,B_234,B_235] :
      ( k4_xboole_0(A_233,B_234) = B_235
      | ~ r1_tarski(B_235,k4_xboole_0(A_233,B_234))
      | k1_xboole_0 != A_233 ) ),
    inference(resolution,[status(thm)],[c_706,c_2])).

tff(c_7093,plain,(
    ! [A_8,B_9,B_235] :
      ( k4_xboole_0(A_8,B_9) = B_235
      | ~ r1_tarski(B_235,A_8)
      | k1_xboole_0 != A_8
      | k1_xboole_0 != A_8 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_6999])).

tff(c_26983,plain,(
    ! [B_9,A_465,B_466] :
      ( k4_xboole_0(k1_xboole_0,B_9) = k4_xboole_0(A_465,B_466)
      | ~ r1_tarski(A_465,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26977,c_7093])).

tff(c_27138,plain,(
    ! [A_465,B_466] :
      ( k4_xboole_0(A_465,B_466) = k1_xboole_0
      | ~ r1_tarski(A_465,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1231,c_26983])).

tff(c_82608,plain,(
    ! [A_1000,B_1001] :
      ( k4_xboole_0(k10_relat_1('#skF_2',A_1000),B_1001) = k1_xboole_0
      | k1_xboole_0 != A_1000 ) ),
    inference(resolution,[status(thm)],[c_80422,c_27138])).

tff(c_395,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | k1_xboole_0 != B_4
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_369])).

tff(c_84275,plain,(
    k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_82608,c_395])).

tff(c_182,plain,(
    ! [B_42,A_43] :
      ( B_42 = A_43
      | ~ r1_tarski(B_42,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1357,plain,(
    ! [B_101,A_102] :
      ( B_101 = A_102
      | ~ r1_tarski(B_101,A_102)
      | k4_xboole_0(A_102,B_101) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_182])).

tff(c_1391,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | k4_xboole_0(B_4,A_3) != k1_xboole_0
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_1357])).

tff(c_25925,plain,(
    ! [B_453,B_454] :
      ( k4_xboole_0(B_453,B_454) = B_453
      | k4_xboole_0(k4_xboole_0(B_453,B_454),B_453) != k1_xboole_0
      | ~ r1_tarski(B_453,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25517,c_1391])).

tff(c_26352,plain,(
    ! [B_453,B_454] :
      ( k4_xboole_0(B_453,B_454) = B_453
      | ~ r1_tarski(B_453,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_25925])).

tff(c_108120,plain,(
    ! [B_454] : k4_xboole_0(k10_relat_1('#skF_2',k1_xboole_0),B_454) = k10_relat_1('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_80422,c_26352])).

tff(c_32,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    ! [C_17,A_15,B_16] :
      ( k6_subset_1(k9_relat_1(C_17,A_15),k9_relat_1(C_17,B_16)) = k9_relat_1(C_17,k6_subset_1(A_15,B_16))
      | ~ v2_funct_1(C_17)
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_38,plain,(
    ! [C_17,A_15,B_16] :
      ( k4_xboole_0(k9_relat_1(C_17,A_15),k9_relat_1(C_17,B_16)) = k9_relat_1(C_17,k4_xboole_0(A_15,B_16))
      | ~ v2_funct_1(C_17)
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_22])).

tff(c_26,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k9_relat_1(B_22,k10_relat_1(B_22,A_21)),A_21)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_489,plain,(
    ! [B_22,A_65,B_66] :
      ( r1_tarski(k9_relat_1(B_22,k10_relat_1(B_22,k4_xboole_0(A_65,B_66))),A_65)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(resolution,[status(thm)],[c_26,c_452])).

tff(c_81248,plain,(
    ! [A_996,B_997] :
      ( r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_996)),A_996)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != B_997 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81083,c_489])).

tff(c_81649,plain,(
    ! [A_996,B_997] :
      ( r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_996)),A_996)
      | k1_xboole_0 != B_997 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_81248])).

tff(c_85424,plain,(
    ! [B_997] : k1_xboole_0 != B_997 ),
    inference(splitLeft,[status(thm)],[c_81649])).

tff(c_81908,plain,(
    ! [A_998] : k4_xboole_0(k10_relat_1('#skF_2',A_998),k1_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_81816,c_10])).

tff(c_85737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85424,c_81908])).

tff(c_85739,plain,(
    ! [A_1018] : r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_1018)),A_1018) ),
    inference(splitRight,[status(thm)],[c_81649])).

tff(c_86104,plain,(
    ! [A_1019] : k4_xboole_0(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_1019)),A_1019) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_85739,c_10])).

tff(c_86671,plain,(
    ! [B_16] :
      ( k9_relat_1('#skF_2',k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_16)),B_16)) = k1_xboole_0
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_86104])).

tff(c_86860,plain,(
    ! [B_16] : k9_relat_1('#skF_2',k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_16)),B_16)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_86671])).

tff(c_118465,plain,(
    ! [B_1132] : k9_relat_1('#skF_2',k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_1132)),B_1132)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_86671])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,k10_relat_1(B_24,k9_relat_1(B_24,A_23)))
      | ~ r1_tarski(A_23,k1_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1387,plain,(
    ! [B_24,A_23] :
      ( k10_relat_1(B_24,k9_relat_1(B_24,A_23)) = A_23
      | k4_xboole_0(k10_relat_1(B_24,k9_relat_1(B_24,A_23)),A_23) != k1_xboole_0
      | ~ r1_tarski(A_23,k1_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_28,c_1357])).

tff(c_118526,plain,(
    ! [B_1132] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_1132)),B_1132))) = k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_1132)),B_1132)
      | k4_xboole_0(k10_relat_1('#skF_2',k1_xboole_0),k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_1132)),B_1132)) != k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_1132)),B_1132),k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118465,c_1387])).

tff(c_118802,plain,(
    ! [B_1132] : k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_1132)),B_1132) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_89057,c_84275,c_108120,c_84275,c_86860,c_118526])).

tff(c_73,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | k4_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ~ r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_81,plain,(
    k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73,c_30])).

tff(c_118899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118802,c_81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:29:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 28.06/18.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.06/18.87  
% 28.06/18.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.06/18.87  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 28.06/18.87  
% 28.06/18.87  %Foreground sorts:
% 28.06/18.87  
% 28.06/18.87  
% 28.06/18.87  %Background operators:
% 28.06/18.87  
% 28.06/18.87  
% 28.06/18.87  %Foreground operators:
% 28.06/18.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 28.06/18.87  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 28.06/18.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 28.06/18.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 28.06/18.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 28.06/18.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 28.06/18.87  tff('#skF_2', type, '#skF_2': $i).
% 28.06/18.87  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 28.06/18.87  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 28.06/18.87  tff('#skF_1', type, '#skF_1': $i).
% 28.06/18.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 28.06/18.87  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 28.06/18.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 28.06/18.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 28.06/18.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 28.06/18.87  
% 28.24/18.90  tff(f_86, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 28.24/18.90  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 28.24/18.90  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 28.24/18.90  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 28.24/18.90  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 28.24/18.90  tff(f_47, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 28.24/18.90  tff(f_65, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 28.24/18.90  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 28.24/18.90  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 28.24/18.90  tff(f_59, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 28.24/18.90  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 28.24/18.90  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 28.24/18.90  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 28.24/18.90  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 28.24/18.90  tff(c_34, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 28.24/18.90  tff(c_16, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_45])).
% 28.24/18.90  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 28.24/18.90  tff(c_64, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 28.24/18.90  tff(c_72, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_64])).
% 28.24/18.90  tff(c_18, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 28.24/18.90  tff(c_24, plain, (![C_20, A_18, B_19]: (k6_subset_1(k10_relat_1(C_20, A_18), k10_relat_1(C_20, B_19))=k10_relat_1(C_20, k6_subset_1(A_18, B_19)) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 28.24/18.90  tff(c_786, plain, (![C_81, A_82, B_83]: (k4_xboole_0(k10_relat_1(C_81, A_82), k10_relat_1(C_81, B_83))=k10_relat_1(C_81, k4_xboole_0(A_82, B_83)) | ~v1_funct_1(C_81) | ~v1_relat_1(C_81))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_24])).
% 28.24/18.90  tff(c_817, plain, (![C_81, B_83]: (k10_relat_1(C_81, k4_xboole_0(B_83, B_83))=k1_xboole_0 | ~v1_funct_1(C_81) | ~v1_relat_1(C_81))), inference(superposition, [status(thm), theory('equality')], [c_786, c_72])).
% 28.24/18.90  tff(c_838, plain, (![C_84]: (k10_relat_1(C_84, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_84) | ~v1_relat_1(C_84))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_817])).
% 28.24/18.90  tff(c_841, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_838])).
% 28.24/18.90  tff(c_844, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_841])).
% 28.24/18.90  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 28.24/18.90  tff(c_82, plain, (![B_35]: (k4_xboole_0(B_35, B_35)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_64])).
% 28.24/18.90  tff(c_87, plain, (![B_35]: (r1_tarski(k1_xboole_0, B_35))), inference(superposition, [status(thm), theory('equality')], [c_82, c_14])).
% 28.24/18.90  tff(c_226, plain, (![A_45, C_46, B_47]: (r1_tarski(A_45, C_46) | ~r1_tarski(B_47, C_46) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_41])).
% 28.24/18.90  tff(c_258, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~r1_tarski(A_50, k1_xboole_0))), inference(resolution, [status(thm)], [c_87, c_226])).
% 28.24/18.90  tff(c_267, plain, (![A_3, B_51]: (r1_tarski(A_3, B_51) | k4_xboole_0(A_3, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_258])).
% 28.24/18.90  tff(c_285, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | k1_xboole_0!=A_52)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_267])).
% 28.24/18.90  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 28.24/18.90  tff(c_369, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | k1_xboole_0!=A_59)), inference(resolution, [status(thm)], [c_285, c_2])).
% 28.24/18.90  tff(c_396, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | k1_xboole_0!=A_8)), inference(resolution, [status(thm)], [c_14, c_369])).
% 28.24/18.90  tff(c_4111, plain, (![C_180, A_181, B_182]: (r1_tarski(k10_relat_1(C_180, k4_xboole_0(A_181, B_182)), k10_relat_1(C_180, A_181)) | ~v1_funct_1(C_180) | ~v1_relat_1(C_180))), inference(superposition, [status(thm), theory('equality')], [c_786, c_14])).
% 28.24/18.90  tff(c_69384, plain, (![C_903, A_904, B_905]: (k10_relat_1(C_903, k4_xboole_0(A_904, B_905))=k10_relat_1(C_903, A_904) | ~r1_tarski(k10_relat_1(C_903, A_904), k10_relat_1(C_903, k4_xboole_0(A_904, B_905))) | ~v1_funct_1(C_903) | ~v1_relat_1(C_903))), inference(resolution, [status(thm)], [c_4111, c_2])).
% 28.24/18.90  tff(c_69591, plain, (![C_903, A_8, B_9]: (k10_relat_1(C_903, k4_xboole_0(A_8, B_9))=k10_relat_1(C_903, A_8) | ~r1_tarski(k10_relat_1(C_903, A_8), k10_relat_1(C_903, A_8)) | ~v1_funct_1(C_903) | ~v1_relat_1(C_903) | k1_xboole_0!=A_8)), inference(superposition, [status(thm), theory('equality')], [c_396, c_69384])).
% 28.24/18.90  tff(c_77099, plain, (![C_970, A_971, B_972]: (k10_relat_1(C_970, k4_xboole_0(A_971, B_972))=k10_relat_1(C_970, A_971) | ~v1_funct_1(C_970) | ~v1_relat_1(C_970) | k1_xboole_0!=A_971)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_69591])).
% 28.24/18.90  tff(c_78114, plain, (![C_979, B_980]: (k10_relat_1(C_979, k1_xboole_0)=k10_relat_1(C_979, B_980) | ~v1_funct_1(C_979) | ~v1_relat_1(C_979) | k1_xboole_0!=B_980)), inference(superposition, [status(thm), theory('equality')], [c_72, c_77099])).
% 28.24/18.90  tff(c_78116, plain, (![B_980]: (k10_relat_1('#skF_2', k1_xboole_0)=k10_relat_1('#skF_2', B_980) | ~v1_funct_1('#skF_2') | k1_xboole_0!=B_980)), inference(resolution, [status(thm)], [c_36, c_78114])).
% 28.24/18.90  tff(c_78122, plain, (![B_981]: (k10_relat_1('#skF_2', B_981)=k1_xboole_0 | k1_xboole_0!=B_981)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_844, c_78116])).
% 28.24/18.90  tff(c_37, plain, (![C_20, A_18, B_19]: (k4_xboole_0(k10_relat_1(C_20, A_18), k10_relat_1(C_20, B_19))=k10_relat_1(C_20, k4_xboole_0(A_18, B_19)) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_24])).
% 28.24/18.90  tff(c_78446, plain, (![A_18, B_981]: (k4_xboole_0(k10_relat_1('#skF_2', A_18), k1_xboole_0)=k10_relat_1('#skF_2', k4_xboole_0(A_18, B_981)) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | k1_xboole_0!=B_981)), inference(superposition, [status(thm), theory('equality')], [c_78122, c_37])).
% 28.24/18.90  tff(c_81083, plain, (![A_996, B_997]: (k10_relat_1('#skF_2', k4_xboole_0(A_996, B_997))=k10_relat_1('#skF_2', A_996) | k1_xboole_0!=B_997)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_16, c_78446])).
% 28.24/18.90  tff(c_20, plain, (![B_14, A_13]: (r1_tarski(k10_relat_1(B_14, A_13), k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 28.24/18.90  tff(c_81322, plain, (![A_996, B_997]: (r1_tarski(k10_relat_1('#skF_2', A_996), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | k1_xboole_0!=B_997)), inference(superposition, [status(thm), theory('equality')], [c_81083, c_20])).
% 28.24/18.90  tff(c_81699, plain, (![A_996, B_997]: (r1_tarski(k10_relat_1('#skF_2', A_996), k1_relat_1('#skF_2')) | k1_xboole_0!=B_997)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_81322])).
% 28.24/18.90  tff(c_81752, plain, (![B_997]: (k1_xboole_0!=B_997)), inference(splitLeft, [status(thm)], [c_81699])).
% 28.24/18.90  tff(c_452, plain, (![A_64, A_65, B_66]: (r1_tarski(A_64, A_65) | ~r1_tarski(A_64, k4_xboole_0(A_65, B_66)))), inference(resolution, [status(thm)], [c_14, c_226])).
% 28.24/18.90  tff(c_494, plain, (![A_67, B_68, B_69]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_67, B_68), B_69), A_67))), inference(resolution, [status(thm)], [c_14, c_452])).
% 28.24/18.90  tff(c_240, plain, (![A_45, A_8, B_9]: (r1_tarski(A_45, A_8) | ~r1_tarski(A_45, k4_xboole_0(A_8, B_9)))), inference(resolution, [status(thm)], [c_14, c_226])).
% 28.24/18.90  tff(c_549, plain, (![A_8, B_9, B_68, B_69]: (r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(A_8, B_9), B_68), B_69), A_8))), inference(resolution, [status(thm)], [c_494, c_240])).
% 28.24/18.90  tff(c_12, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 28.24/18.90  tff(c_2106, plain, (![A_134, A_135, B_136, B_137]: (r1_tarski(A_134, A_135) | ~r1_tarski(A_134, k4_xboole_0(k4_xboole_0(A_135, B_136), B_137)))), inference(resolution, [status(thm)], [c_494, c_12])).
% 28.24/18.90  tff(c_22422, plain, (![A_424, B_425, B_421, B_422, B_423, B_426]: (r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(A_424, B_422), B_426), B_425), B_421), B_423), A_424))), inference(resolution, [status(thm)], [c_549, c_2106])).
% 28.24/18.90  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 28.24/18.90  tff(c_23042, plain, (![A_424, B_425, B_421, B_422, B_423, B_426]: (k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(A_424, B_422), B_426), B_425), B_421), B_423), A_424)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22422, c_10])).
% 28.24/18.90  tff(c_81814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81752, c_23042])).
% 28.24/18.90  tff(c_81816, plain, (![A_998]: (r1_tarski(k10_relat_1('#skF_2', A_998), k1_relat_1('#skF_2')))), inference(splitRight, [status(thm)], [c_81699])).
% 28.24/18.90  tff(c_88754, plain, (![A_1030, A_1031]: (r1_tarski(A_1030, k1_relat_1('#skF_2')) | ~r1_tarski(A_1030, k10_relat_1('#skF_2', A_1031)))), inference(resolution, [status(thm)], [c_81816, c_12])).
% 28.24/18.90  tff(c_89057, plain, (![A_1031, B_9]: (r1_tarski(k4_xboole_0(k10_relat_1('#skF_2', A_1031), B_9), k1_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_14, c_88754])).
% 28.24/18.90  tff(c_69629, plain, (![C_903, A_8, B_9]: (k10_relat_1(C_903, k4_xboole_0(A_8, B_9))=k10_relat_1(C_903, A_8) | ~v1_funct_1(C_903) | ~v1_relat_1(C_903) | k1_xboole_0!=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_69591])).
% 28.24/18.90  tff(c_820, plain, (![C_81, A_82, B_83]: (r1_tarski(k10_relat_1(C_81, k4_xboole_0(A_82, B_83)), k10_relat_1(C_81, A_82)) | ~v1_funct_1(C_81) | ~v1_relat_1(C_81))), inference(superposition, [status(thm), theory('equality')], [c_786, c_14])).
% 28.24/18.90  tff(c_78414, plain, (![B_981, B_83]: (r1_tarski(k10_relat_1('#skF_2', k4_xboole_0(B_981, B_83)), k1_xboole_0) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | k1_xboole_0!=B_981)), inference(superposition, [status(thm), theory('equality')], [c_78122, c_820])).
% 28.24/18.90  tff(c_80022, plain, (![B_988, B_989]: (r1_tarski(k10_relat_1('#skF_2', k4_xboole_0(B_988, B_989)), k1_xboole_0) | k1_xboole_0!=B_988)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_78414])).
% 28.24/18.90  tff(c_80108, plain, (![A_8]: (r1_tarski(k10_relat_1('#skF_2', A_8), k1_xboole_0) | k1_xboole_0!=A_8 | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | k1_xboole_0!=A_8)), inference(superposition, [status(thm), theory('equality')], [c_69629, c_80022])).
% 28.24/18.90  tff(c_80422, plain, (![A_990]: (r1_tarski(k10_relat_1('#skF_2', A_990), k1_xboole_0) | k1_xboole_0!=A_990)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_80108])).
% 28.24/18.90  tff(c_680, plain, (![A_73, B_74, A_75]: (r1_tarski(A_73, B_74) | ~r1_tarski(A_73, A_75) | k1_xboole_0!=A_75)), inference(resolution, [status(thm)], [c_285, c_12])).
% 28.24/18.90  tff(c_706, plain, (![A_76, B_77, B_78]: (r1_tarski(k4_xboole_0(A_76, B_77), B_78) | k1_xboole_0!=A_76)), inference(resolution, [status(thm)], [c_14, c_680])).
% 28.24/18.90  tff(c_306, plain, (![B_53, A_52]: (B_53=A_52 | ~r1_tarski(B_53, A_52) | k1_xboole_0!=A_52)), inference(resolution, [status(thm)], [c_285, c_2])).
% 28.24/18.90  tff(c_1231, plain, (![B_77]: (k4_xboole_0(k1_xboole_0, B_77)=k1_xboole_0)), inference(resolution, [status(thm)], [c_706, c_306])).
% 28.24/18.90  tff(c_71, plain, (![A_8, B_9]: (k4_xboole_0(k4_xboole_0(A_8, B_9), A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_64])).
% 28.24/18.90  tff(c_1768, plain, (![A_117, B_118, A_119]: (r1_tarski(A_117, B_118) | ~r1_tarski(A_117, A_119) | k4_xboole_0(A_119, B_118)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_226])).
% 28.24/18.90  tff(c_1802, plain, (![A_120, B_121, B_122]: (r1_tarski(k4_xboole_0(A_120, B_121), B_122) | k4_xboole_0(A_120, B_122)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_1768])).
% 28.24/18.90  tff(c_1880, plain, (![A_120, B_121, B_122]: (k4_xboole_0(k4_xboole_0(A_120, B_121), B_122)=k1_xboole_0 | k4_xboole_0(A_120, B_122)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1802, c_10])).
% 28.24/18.90  tff(c_16371, plain, (![A_364, B_365, B_366]: (k4_xboole_0(k4_xboole_0(A_364, B_365), B_366)=A_364 | ~r1_tarski(A_364, k4_xboole_0(k4_xboole_0(A_364, B_365), B_366)))), inference(resolution, [status(thm)], [c_494, c_2])).
% 28.24/18.90  tff(c_23558, plain, (![A_435, B_436, B_437]: (k4_xboole_0(k4_xboole_0(A_435, B_436), B_437)=A_435 | ~r1_tarski(A_435, k1_xboole_0) | k4_xboole_0(A_435, B_437)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1880, c_16371])).
% 28.24/18.90  tff(c_25410, plain, (![A_450, B_451, B_452]: (k4_xboole_0(A_450, k4_xboole_0(A_450, B_451))=k1_xboole_0 | ~r1_tarski(A_450, k1_xboole_0) | k4_xboole_0(A_450, B_452)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_23558, c_71])).
% 28.24/18.90  tff(c_25517, plain, (![B_453, B_454]: (k4_xboole_0(B_453, k4_xboole_0(B_453, B_454))=k1_xboole_0 | ~r1_tarski(B_453, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_72, c_25410])).
% 28.24/18.90  tff(c_1799, plain, (![A_3, B_118, B_4]: (r1_tarski(A_3, B_118) | k4_xboole_0(B_4, B_118)!=k1_xboole_0 | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1768])).
% 28.24/18.90  tff(c_26521, plain, (![A_457, B_458, B_459]: (r1_tarski(A_457, k4_xboole_0(B_458, B_459)) | k4_xboole_0(A_457, B_458)!=k1_xboole_0 | ~r1_tarski(B_458, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_25517, c_1799])).
% 28.24/18.90  tff(c_26865, plain, (![A_463, B_464]: (r1_tarski(A_463, k1_xboole_0) | k4_xboole_0(A_463, B_464)!=k1_xboole_0 | ~r1_tarski(B_464, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_72, c_26521])).
% 28.24/18.90  tff(c_26977, plain, (![A_465, B_466]: (r1_tarski(k4_xboole_0(A_465, B_466), k1_xboole_0) | ~r1_tarski(A_465, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_71, c_26865])).
% 28.24/18.90  tff(c_6999, plain, (![A_233, B_234, B_235]: (k4_xboole_0(A_233, B_234)=B_235 | ~r1_tarski(B_235, k4_xboole_0(A_233, B_234)) | k1_xboole_0!=A_233)), inference(resolution, [status(thm)], [c_706, c_2])).
% 28.24/18.90  tff(c_7093, plain, (![A_8, B_9, B_235]: (k4_xboole_0(A_8, B_9)=B_235 | ~r1_tarski(B_235, A_8) | k1_xboole_0!=A_8 | k1_xboole_0!=A_8)), inference(superposition, [status(thm), theory('equality')], [c_396, c_6999])).
% 28.24/18.90  tff(c_26983, plain, (![B_9, A_465, B_466]: (k4_xboole_0(k1_xboole_0, B_9)=k4_xboole_0(A_465, B_466) | ~r1_tarski(A_465, k1_xboole_0))), inference(resolution, [status(thm)], [c_26977, c_7093])).
% 28.24/18.90  tff(c_27138, plain, (![A_465, B_466]: (k4_xboole_0(A_465, B_466)=k1_xboole_0 | ~r1_tarski(A_465, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1231, c_26983])).
% 28.24/18.90  tff(c_82608, plain, (![A_1000, B_1001]: (k4_xboole_0(k10_relat_1('#skF_2', A_1000), B_1001)=k1_xboole_0 | k1_xboole_0!=A_1000)), inference(resolution, [status(thm)], [c_80422, c_27138])).
% 28.24/18.90  tff(c_395, plain, (![B_4, A_3]: (B_4=A_3 | k1_xboole_0!=B_4 | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_369])).
% 28.24/18.90  tff(c_84275, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_82608, c_395])).
% 28.24/18.90  tff(c_182, plain, (![B_42, A_43]: (B_42=A_43 | ~r1_tarski(B_42, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 28.24/18.90  tff(c_1357, plain, (![B_101, A_102]: (B_101=A_102 | ~r1_tarski(B_101, A_102) | k4_xboole_0(A_102, B_101)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_182])).
% 28.24/18.90  tff(c_1391, plain, (![B_4, A_3]: (B_4=A_3 | k4_xboole_0(B_4, A_3)!=k1_xboole_0 | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1357])).
% 28.24/18.90  tff(c_25925, plain, (![B_453, B_454]: (k4_xboole_0(B_453, B_454)=B_453 | k4_xboole_0(k4_xboole_0(B_453, B_454), B_453)!=k1_xboole_0 | ~r1_tarski(B_453, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_25517, c_1391])).
% 28.24/18.90  tff(c_26352, plain, (![B_453, B_454]: (k4_xboole_0(B_453, B_454)=B_453 | ~r1_tarski(B_453, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_25925])).
% 28.24/18.90  tff(c_108120, plain, (![B_454]: (k4_xboole_0(k10_relat_1('#skF_2', k1_xboole_0), B_454)=k10_relat_1('#skF_2', k1_xboole_0))), inference(resolution, [status(thm)], [c_80422, c_26352])).
% 28.24/18.90  tff(c_32, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 28.24/18.90  tff(c_22, plain, (![C_17, A_15, B_16]: (k6_subset_1(k9_relat_1(C_17, A_15), k9_relat_1(C_17, B_16))=k9_relat_1(C_17, k6_subset_1(A_15, B_16)) | ~v2_funct_1(C_17) | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 28.24/18.90  tff(c_38, plain, (![C_17, A_15, B_16]: (k4_xboole_0(k9_relat_1(C_17, A_15), k9_relat_1(C_17, B_16))=k9_relat_1(C_17, k4_xboole_0(A_15, B_16)) | ~v2_funct_1(C_17) | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_22])).
% 28.24/18.90  tff(c_26, plain, (![B_22, A_21]: (r1_tarski(k9_relat_1(B_22, k10_relat_1(B_22, A_21)), A_21) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 28.24/18.90  tff(c_489, plain, (![B_22, A_65, B_66]: (r1_tarski(k9_relat_1(B_22, k10_relat_1(B_22, k4_xboole_0(A_65, B_66))), A_65) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(resolution, [status(thm)], [c_26, c_452])).
% 28.24/18.90  tff(c_81248, plain, (![A_996, B_997]: (r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_996)), A_996) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | k1_xboole_0!=B_997)), inference(superposition, [status(thm), theory('equality')], [c_81083, c_489])).
% 28.24/18.90  tff(c_81649, plain, (![A_996, B_997]: (r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_996)), A_996) | k1_xboole_0!=B_997)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_81248])).
% 28.24/18.90  tff(c_85424, plain, (![B_997]: (k1_xboole_0!=B_997)), inference(splitLeft, [status(thm)], [c_81649])).
% 28.24/18.90  tff(c_81908, plain, (![A_998]: (k4_xboole_0(k10_relat_1('#skF_2', A_998), k1_relat_1('#skF_2'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_81816, c_10])).
% 28.24/18.90  tff(c_85737, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85424, c_81908])).
% 28.24/18.90  tff(c_85739, plain, (![A_1018]: (r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_1018)), A_1018))), inference(splitRight, [status(thm)], [c_81649])).
% 28.24/18.90  tff(c_86104, plain, (![A_1019]: (k4_xboole_0(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_1019)), A_1019)=k1_xboole_0)), inference(resolution, [status(thm)], [c_85739, c_10])).
% 28.24/18.90  tff(c_86671, plain, (![B_16]: (k9_relat_1('#skF_2', k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_16)), B_16))=k1_xboole_0 | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_86104])).
% 28.24/18.90  tff(c_86860, plain, (![B_16]: (k9_relat_1('#skF_2', k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_16)), B_16))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_86671])).
% 28.24/18.90  tff(c_118465, plain, (![B_1132]: (k9_relat_1('#skF_2', k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_1132)), B_1132))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_86671])).
% 28.24/18.90  tff(c_28, plain, (![A_23, B_24]: (r1_tarski(A_23, k10_relat_1(B_24, k9_relat_1(B_24, A_23))) | ~r1_tarski(A_23, k1_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_77])).
% 28.24/18.90  tff(c_1387, plain, (![B_24, A_23]: (k10_relat_1(B_24, k9_relat_1(B_24, A_23))=A_23 | k4_xboole_0(k10_relat_1(B_24, k9_relat_1(B_24, A_23)), A_23)!=k1_xboole_0 | ~r1_tarski(A_23, k1_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_28, c_1357])).
% 28.24/18.90  tff(c_118526, plain, (![B_1132]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_1132)), B_1132)))=k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_1132)), B_1132) | k4_xboole_0(k10_relat_1('#skF_2', k1_xboole_0), k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_1132)), B_1132))!=k1_xboole_0 | ~r1_tarski(k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_1132)), B_1132), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_118465, c_1387])).
% 28.24/18.90  tff(c_118802, plain, (![B_1132]: (k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_1132)), B_1132)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_89057, c_84275, c_108120, c_84275, c_86860, c_118526])).
% 28.24/18.90  tff(c_73, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | k4_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 28.24/18.90  tff(c_30, plain, (~r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 28.24/18.90  tff(c_81, plain, (k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_73, c_30])).
% 28.24/18.90  tff(c_118899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118802, c_81])).
% 28.24/18.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.24/18.90  
% 28.24/18.90  Inference rules
% 28.24/18.90  ----------------------
% 28.24/18.90  #Ref     : 17
% 28.24/18.90  #Sup     : 31489
% 28.24/18.90  #Fact    : 0
% 28.24/18.90  #Define  : 0
% 28.24/18.90  #Split   : 2
% 28.24/18.90  #Chain   : 0
% 28.24/18.90  #Close   : 0
% 28.24/18.90  
% 28.24/18.90  Ordering : KBO
% 28.24/18.90  
% 28.24/18.90  Simplification rules
% 28.24/18.90  ----------------------
% 28.24/18.90  #Subsume      : 15880
% 28.24/18.90  #Demod        : 18166
% 28.24/18.90  #Tautology    : 7331
% 28.24/18.90  #SimpNegUnit  : 202
% 28.24/18.90  #BackRed      : 82
% 28.24/18.90  
% 28.24/18.90  #Partial instantiations: 0
% 28.24/18.90  #Strategies tried      : 1
% 28.24/18.90  
% 28.24/18.90  Timing (in seconds)
% 28.24/18.90  ----------------------
% 28.24/18.90  Preprocessing        : 0.30
% 28.24/18.90  Parsing              : 0.16
% 28.24/18.90  CNF conversion       : 0.02
% 28.24/18.90  Main loop            : 17.84
% 28.24/18.90  Inferencing          : 2.19
% 28.24/18.90  Reduction            : 6.41
% 28.24/18.90  Demodulation         : 5.43
% 28.24/18.90  BG Simplification    : 0.24
% 28.24/18.90  Subsumption          : 8.38
% 28.24/18.90  Abstraction          : 0.49
% 28.24/18.90  MUC search           : 0.00
% 28.24/18.90  Cooper               : 0.00
% 28.24/18.90  Total                : 18.18
% 28.24/18.90  Index Insertion      : 0.00
% 28.24/18.90  Index Deletion       : 0.00
% 28.24/18.90  Index Matching       : 0.00
% 28.24/18.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
