%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:00 EST 2020

% Result     : Theorem 13.55s
% Output     : CNFRefutation 13.55s
% Verified   : 
% Statistics : Number of formulae       :  122 (1090 expanded)
%              Number of leaves         :   29 ( 402 expanded)
%              Depth                    :   24
%              Number of atoms          :  232 (2188 expanded)
%              Number of equality atoms :   74 ( 670 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( v2_funct_1(B)
         => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k10_relat_1(B,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_16,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_83,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_71])).

tff(c_18,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [C_21,A_19,B_20] :
      ( k6_subset_1(k10_relat_1(C_21,A_19),k10_relat_1(C_21,B_20)) = k10_relat_1(C_21,k6_subset_1(A_19,B_20))
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_780,plain,(
    ! [C_81,A_82,B_83] :
      ( k4_xboole_0(k10_relat_1(C_81,A_82),k10_relat_1(C_81,B_83)) = k10_relat_1(C_81,k4_xboole_0(A_82,B_83))
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_26])).

tff(c_808,plain,(
    ! [C_81,B_83] :
      ( k10_relat_1(C_81,k4_xboole_0(B_83,B_83)) = k1_xboole_0
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_83])).

tff(c_835,plain,(
    ! [C_84] :
      ( k10_relat_1(C_84,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_84)
      | ~ v1_relat_1(C_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_808])).

tff(c_838,plain,
    ( k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_835])).

tff(c_841,plain,(
    k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_838])).

tff(c_20,plain,(
    ! [A_13] :
      ( k10_relat_1(A_13,k2_relat_1(A_13)) = k1_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_15304,plain,(
    ! [A_354,B_355] :
      ( k4_xboole_0(k1_relat_1(A_354),k10_relat_1(A_354,B_355)) = k10_relat_1(A_354,k4_xboole_0(k2_relat_1(A_354),B_355))
      | ~ v1_funct_1(A_354)
      | ~ v1_relat_1(A_354)
      | ~ v1_relat_1(A_354) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_780])).

tff(c_15487,plain,
    ( k10_relat_1('#skF_2',k4_xboole_0(k2_relat_1('#skF_2'),k1_xboole_0)) = k4_xboole_0(k1_relat_1('#skF_2'),k1_xboole_0)
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_841,c_15304])).

tff(c_15507,plain,(
    k10_relat_1('#skF_2',k2_relat_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_36,c_16,c_16,c_15487])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_242,plain,(
    ! [B_48,A_49] :
      ( r1_tarski(k10_relat_1(B_48,A_49),k10_relat_1(B_48,k2_relat_1(B_48)))
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4954,plain,(
    ! [A_188,B_189,A_190] :
      ( r1_tarski(A_188,k10_relat_1(B_189,k2_relat_1(B_189)))
      | ~ r1_tarski(A_188,k10_relat_1(B_189,A_190))
      | ~ v1_relat_1(B_189) ) ),
    inference(resolution,[status(thm)],[c_242,c_12])).

tff(c_5012,plain,(
    ! [B_189,A_190,B_9] :
      ( r1_tarski(k4_xboole_0(k10_relat_1(B_189,A_190),B_9),k10_relat_1(B_189,k2_relat_1(B_189)))
      | ~ v1_relat_1(B_189) ) ),
    inference(resolution,[status(thm)],[c_14,c_4954])).

tff(c_15546,plain,(
    ! [A_190,B_9] :
      ( r1_tarski(k4_xboole_0(k10_relat_1('#skF_2',A_190),B_9),k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15507,c_5012])).

tff(c_15650,plain,(
    ! [A_190,B_9] : r1_tarski(k4_xboole_0(k10_relat_1('#skF_2',A_190),B_9),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_15546])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [B_36] : k4_xboole_0(B_36,B_36) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_71])).

tff(c_89,plain,(
    ! [B_36] : r1_tarski(k1_xboole_0,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_14])).

tff(c_229,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(A_45,C_46)
      | ~ r1_tarski(B_47,C_46)
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_259,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ r1_tarski(A_50,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_89,c_229])).

tff(c_265,plain,(
    ! [A_3,B_51] :
      ( r1_tarski(A_3,B_51)
      | k4_xboole_0(A_3,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_259])).

tff(c_280,plain,(
    ! [B_51] : r1_tarski(k1_xboole_0,B_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_265])).

tff(c_282,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | k1_xboole_0 != A_52 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_265])).

tff(c_700,plain,(
    ! [A_75,B_76,A_77] :
      ( r1_tarski(A_75,B_76)
      | ~ r1_tarski(A_75,A_77)
      | k1_xboole_0 != A_77 ) ),
    inference(resolution,[status(thm)],[c_282,c_12])).

tff(c_726,plain,(
    ! [A_78,B_79,B_80] :
      ( r1_tarski(k4_xboole_0(A_78,B_79),B_80)
      | k1_xboole_0 != A_78 ) ),
    inference(resolution,[status(thm)],[c_14,c_700])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_303,plain,(
    ! [B_53,A_52] :
      ( B_53 = A_52
      | ~ r1_tarski(B_53,A_52)
      | k1_xboole_0 != A_52 ) ),
    inference(resolution,[status(thm)],[c_282,c_2])).

tff(c_1257,plain,(
    ! [B_79] : k4_xboole_0(k1_xboole_0,B_79) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_726,c_303])).

tff(c_472,plain,(
    ! [A_66,A_67,B_68] :
      ( r1_tarski(A_66,A_67)
      | ~ r1_tarski(A_66,k4_xboole_0(A_67,B_68)) ) ),
    inference(resolution,[status(thm)],[c_14,c_229])).

tff(c_514,plain,(
    ! [A_69,B_70,B_71] : r1_tarski(k4_xboole_0(k4_xboole_0(A_69,B_70),B_71),A_69) ),
    inference(resolution,[status(thm)],[c_14,c_472])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_577,plain,(
    ! [A_69,B_70,B_71] : k4_xboole_0(k4_xboole_0(k4_xboole_0(A_69,B_70),B_71),A_69) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_514,c_10])).

tff(c_1829,plain,(
    ! [A_121,B_122,A_123] :
      ( r1_tarski(A_121,B_122)
      | ~ r1_tarski(A_121,A_123)
      | k4_xboole_0(A_123,B_122) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_229])).

tff(c_1866,plain,(
    ! [A_124,B_125,B_126] :
      ( r1_tarski(k4_xboole_0(A_124,B_125),B_126)
      | k4_xboole_0(A_124,B_126) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_1829])).

tff(c_240,plain,(
    ! [A_45,A_8,B_9] :
      ( r1_tarski(A_45,A_8)
      | ~ r1_tarski(A_45,k4_xboole_0(A_8,B_9)) ) ),
    inference(resolution,[status(thm)],[c_14,c_229])).

tff(c_5464,plain,(
    ! [A_206,B_207,A_208,B_209] :
      ( r1_tarski(k4_xboole_0(A_206,B_207),A_208)
      | k4_xboole_0(A_206,k4_xboole_0(A_208,B_209)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1866,c_240])).

tff(c_5780,plain,(
    ! [B_215,A_214,B_216,B_217,B_218] : r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(A_214,B_217),B_216),B_218),B_215),A_214) ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_5464])).

tff(c_6054,plain,(
    ! [B_215,A_214,B_216,B_217,B_218] :
      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(A_214,B_217),B_216),B_218),B_215) = A_214
      | k1_xboole_0 != A_214 ) ),
    inference(resolution,[status(thm)],[c_5780,c_303])).

tff(c_16394,plain,(
    ! [A_360,A_361] :
      ( k4_xboole_0(k10_relat_1(A_360,A_361),k1_relat_1(A_360)) = k10_relat_1(A_360,k4_xboole_0(A_361,k2_relat_1(A_360)))
      | ~ v1_funct_1(A_360)
      | ~ v1_relat_1(A_360)
      | ~ v1_relat_1(A_360) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_780])).

tff(c_258,plain,(
    ! [B_48,A_49] :
      ( k4_xboole_0(k10_relat_1(B_48,A_49),k10_relat_1(B_48,k2_relat_1(B_48))) = k1_xboole_0
      | ~ v1_relat_1(B_48) ) ),
    inference(resolution,[status(thm)],[c_242,c_10])).

tff(c_15598,plain,(
    ! [A_49] :
      ( k4_xboole_0(k10_relat_1('#skF_2',A_49),k1_relat_1('#skF_2')) = k1_xboole_0
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15507,c_258])).

tff(c_15686,plain,(
    ! [A_49] : k4_xboole_0(k10_relat_1('#skF_2',A_49),k1_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_15598])).

tff(c_16405,plain,(
    ! [A_361] :
      ( k10_relat_1('#skF_2',k4_xboole_0(A_361,k2_relat_1('#skF_2'))) = k1_xboole_0
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16394,c_15686])).

tff(c_16632,plain,(
    ! [A_362] : k10_relat_1('#skF_2',k4_xboole_0(A_362,k2_relat_1('#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_36,c_16405])).

tff(c_16902,plain,(
    ! [A_363] :
      ( k10_relat_1('#skF_2',A_363) = k1_xboole_0
      | k1_xboole_0 != A_363 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6054,c_16632])).

tff(c_811,plain,(
    ! [C_81,A_82,B_83] :
      ( r1_tarski(k10_relat_1(C_81,k4_xboole_0(A_82,B_83)),k10_relat_1(C_81,A_82))
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_14])).

tff(c_17006,plain,(
    ! [A_363,B_83] :
      ( r1_tarski(k10_relat_1('#skF_2',k4_xboole_0(A_363,B_83)),k1_xboole_0)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != A_363 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16902,c_811])).

tff(c_19786,plain,(
    ! [A_383,B_384] :
      ( r1_tarski(k10_relat_1('#skF_2',k4_xboole_0(A_383,B_384)),k1_xboole_0)
      | k1_xboole_0 != A_383 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_17006])).

tff(c_19999,plain,(
    ! [A_385] :
      ( r1_tarski(k10_relat_1('#skF_2',A_385),k1_xboole_0)
      | k1_xboole_0 != A_385 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_19786])).

tff(c_239,plain,(
    ! [A_45,B_4,A_3] :
      ( r1_tarski(A_45,B_4)
      | ~ r1_tarski(A_45,A_3)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_229])).

tff(c_20009,plain,(
    ! [A_385,B_4] :
      ( r1_tarski(k10_relat_1('#skF_2',A_385),B_4)
      | k4_xboole_0(k1_xboole_0,B_4) != k1_xboole_0
      | k1_xboole_0 != A_385 ) ),
    inference(resolution,[status(thm)],[c_19999,c_239])).

tff(c_20094,plain,(
    ! [A_386,B_387] :
      ( r1_tarski(k10_relat_1('#skF_2',A_386),B_387)
      | k1_xboole_0 != A_386 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1257,c_20009])).

tff(c_20727,plain,(
    k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20094,c_303])).

tff(c_34,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_39,plain,(
    ! [C_21,A_19,B_20] :
      ( k4_xboole_0(k10_relat_1(C_21,A_19),k10_relat_1(C_21,B_20)) = k10_relat_1(C_21,k4_xboole_0(A_19,B_20))
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_26])).

tff(c_17058,plain,(
    ! [A_19,A_363] :
      ( k4_xboole_0(k10_relat_1('#skF_2',A_19),k1_xboole_0) = k10_relat_1('#skF_2',k4_xboole_0(A_19,A_363))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != A_363 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16902,c_39])).

tff(c_24442,plain,(
    ! [A_423,A_424] :
      ( k10_relat_1('#skF_2',k4_xboole_0(A_423,A_424)) = k10_relat_1('#skF_2',A_423)
      | k1_xboole_0 != A_424 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_16,c_17058])).

tff(c_28,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k9_relat_1(B_23,k10_relat_1(B_23,A_22)),A_22)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_508,plain,(
    ! [B_23,A_67,B_68] :
      ( r1_tarski(k9_relat_1(B_23,k10_relat_1(B_23,k4_xboole_0(A_67,B_68))),A_67)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(resolution,[status(thm)],[c_28,c_472])).

tff(c_24448,plain,(
    ! [A_423,A_424] :
      ( r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_423)),A_423)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != A_424 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24442,c_508])).

tff(c_24751,plain,(
    ! [A_423,A_424] :
      ( r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_423)),A_423)
      | k1_xboole_0 != A_424 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_24448])).

tff(c_24859,plain,(
    ! [A_424] : k1_xboole_0 != A_424 ),
    inference(splitLeft,[status(thm)],[c_24751])).

tff(c_354,plain,(
    ! [B_56,A_57] :
      ( r1_tarski(k9_relat_1(B_56,k10_relat_1(B_56,A_57)),A_57)
      | ~ v1_funct_1(B_56)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_373,plain,(
    ! [A_5,A_57,B_56] :
      ( r1_tarski(A_5,A_57)
      | ~ r1_tarski(A_5,k9_relat_1(B_56,k10_relat_1(B_56,A_57)))
      | ~ v1_funct_1(B_56)
      | ~ v1_relat_1(B_56) ) ),
    inference(resolution,[status(thm)],[c_354,c_12])).

tff(c_15555,plain,(
    ! [A_5] :
      ( r1_tarski(A_5,k2_relat_1('#skF_2'))
      | ~ r1_tarski(A_5,k9_relat_1('#skF_2',k1_relat_1('#skF_2')))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15507,c_373])).

tff(c_18124,plain,(
    ! [A_372] :
      ( r1_tarski(A_372,k2_relat_1('#skF_2'))
      | ~ r1_tarski(A_372,k9_relat_1('#skF_2',k1_relat_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_15555])).

tff(c_18914,plain,(
    ! [B_378] : r1_tarski(k4_xboole_0(k9_relat_1('#skF_2',k1_relat_1('#skF_2')),B_378),k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_18124])).

tff(c_18990,plain,(
    ! [B_378] : k4_xboole_0(k4_xboole_0(k9_relat_1('#skF_2',k1_relat_1('#skF_2')),B_378),k2_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18914,c_10])).

tff(c_25063,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24859,c_18990])).

tff(c_25065,plain,(
    ! [A_427] : r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_427)),A_427) ),
    inference(splitRight,[status(thm)],[c_24751])).

tff(c_25415,plain,(
    ! [A_429] : k4_xboole_0(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_429)),A_429) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_25065,c_10])).

tff(c_24,plain,(
    ! [C_18,A_16,B_17] :
      ( k6_subset_1(k9_relat_1(C_18,A_16),k9_relat_1(C_18,B_17)) = k9_relat_1(C_18,k6_subset_1(A_16,B_17))
      | ~ v2_funct_1(C_18)
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_40,plain,(
    ! [C_18,A_16,B_17] :
      ( k4_xboole_0(k9_relat_1(C_18,A_16),k9_relat_1(C_18,B_17)) = k9_relat_1(C_18,k4_xboole_0(A_16,B_17))
      | ~ v2_funct_1(C_18)
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_24])).

tff(c_25600,plain,(
    ! [B_17] :
      ( k9_relat_1('#skF_2',k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_17)),B_17)) = k1_xboole_0
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25415,c_40])).

tff(c_25786,plain,(
    ! [B_17] : k9_relat_1('#skF_2',k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_17)),B_17)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_25600])).

tff(c_39669,plain,(
    ! [B_520] : k9_relat_1('#skF_2',k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_520)),B_520)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_25600])).

tff(c_457,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,k10_relat_1(B_65,k9_relat_1(B_65,A_64)))
      | ~ r1_tarski(A_64,k1_relat_1(B_65))
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_470,plain,(
    ! [B_65,A_64] :
      ( k10_relat_1(B_65,k9_relat_1(B_65,A_64)) = A_64
      | ~ r1_tarski(k10_relat_1(B_65,k9_relat_1(B_65,A_64)),A_64)
      | ~ r1_tarski(A_64,k1_relat_1(B_65))
      | ~ v1_relat_1(B_65) ) ),
    inference(resolution,[status(thm)],[c_457,c_2])).

tff(c_39713,plain,(
    ! [B_520] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_520)),B_520))) = k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_520)),B_520)
      | ~ r1_tarski(k10_relat_1('#skF_2',k1_xboole_0),k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_520)),B_520))
      | ~ r1_tarski(k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_520)),B_520),k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39669,c_470])).

tff(c_39886,plain,(
    ! [B_520] : k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_520)),B_520) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_15650,c_280,c_20727,c_20727,c_25786,c_39713])).

tff(c_66,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | k4_xboole_0(A_32,B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ~ r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_70,plain,(
    k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_32])).

tff(c_39942,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39886,c_70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:57:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.55/5.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.55/5.58  
% 13.55/5.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.55/5.58  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 13.55/5.58  
% 13.55/5.58  %Foreground sorts:
% 13.55/5.58  
% 13.55/5.58  
% 13.55/5.58  %Background operators:
% 13.55/5.58  
% 13.55/5.58  
% 13.55/5.58  %Foreground operators:
% 13.55/5.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.55/5.58  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.55/5.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.55/5.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.55/5.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.55/5.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.55/5.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.55/5.58  tff('#skF_2', type, '#skF_2': $i).
% 13.55/5.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.55/5.58  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 13.55/5.58  tff('#skF_1', type, '#skF_1': $i).
% 13.55/5.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.55/5.58  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 13.55/5.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.55/5.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.55/5.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.55/5.58  
% 13.55/5.60  tff(f_90, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 13.55/5.60  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 13.55/5.60  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.55/5.60  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 13.55/5.60  tff(f_47, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 13.55/5.60  tff(f_69, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 13.55/5.60  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 13.55/5.60  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 13.55/5.60  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k10_relat_1(B, k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t170_relat_1)).
% 13.55/5.60  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 13.55/5.60  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 13.55/5.60  tff(f_63, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_funct_1)).
% 13.55/5.60  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 13.55/5.60  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 13.55/5.60  tff(c_36, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 13.55/5.60  tff(c_16, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.55/5.60  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.55/5.60  tff(c_71, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.55/5.60  tff(c_83, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_71])).
% 13.55/5.60  tff(c_18, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.55/5.60  tff(c_26, plain, (![C_21, A_19, B_20]: (k6_subset_1(k10_relat_1(C_21, A_19), k10_relat_1(C_21, B_20))=k10_relat_1(C_21, k6_subset_1(A_19, B_20)) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.55/5.60  tff(c_780, plain, (![C_81, A_82, B_83]: (k4_xboole_0(k10_relat_1(C_81, A_82), k10_relat_1(C_81, B_83))=k10_relat_1(C_81, k4_xboole_0(A_82, B_83)) | ~v1_funct_1(C_81) | ~v1_relat_1(C_81))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_26])).
% 13.55/5.60  tff(c_808, plain, (![C_81, B_83]: (k10_relat_1(C_81, k4_xboole_0(B_83, B_83))=k1_xboole_0 | ~v1_funct_1(C_81) | ~v1_relat_1(C_81))), inference(superposition, [status(thm), theory('equality')], [c_780, c_83])).
% 13.55/5.60  tff(c_835, plain, (![C_84]: (k10_relat_1(C_84, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_84) | ~v1_relat_1(C_84))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_808])).
% 13.55/5.60  tff(c_838, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_835])).
% 13.55/5.60  tff(c_841, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_838])).
% 13.55/5.60  tff(c_20, plain, (![A_13]: (k10_relat_1(A_13, k2_relat_1(A_13))=k1_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.55/5.60  tff(c_15304, plain, (![A_354, B_355]: (k4_xboole_0(k1_relat_1(A_354), k10_relat_1(A_354, B_355))=k10_relat_1(A_354, k4_xboole_0(k2_relat_1(A_354), B_355)) | ~v1_funct_1(A_354) | ~v1_relat_1(A_354) | ~v1_relat_1(A_354))), inference(superposition, [status(thm), theory('equality')], [c_20, c_780])).
% 13.55/5.60  tff(c_15487, plain, (k10_relat_1('#skF_2', k4_xboole_0(k2_relat_1('#skF_2'), k1_xboole_0))=k4_xboole_0(k1_relat_1('#skF_2'), k1_xboole_0) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_841, c_15304])).
% 13.55/5.60  tff(c_15507, plain, (k10_relat_1('#skF_2', k2_relat_1('#skF_2'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_36, c_16, c_16, c_15487])).
% 13.55/5.60  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.55/5.60  tff(c_242, plain, (![B_48, A_49]: (r1_tarski(k10_relat_1(B_48, A_49), k10_relat_1(B_48, k2_relat_1(B_48))) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.55/5.60  tff(c_12, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.55/5.60  tff(c_4954, plain, (![A_188, B_189, A_190]: (r1_tarski(A_188, k10_relat_1(B_189, k2_relat_1(B_189))) | ~r1_tarski(A_188, k10_relat_1(B_189, A_190)) | ~v1_relat_1(B_189))), inference(resolution, [status(thm)], [c_242, c_12])).
% 13.55/5.60  tff(c_5012, plain, (![B_189, A_190, B_9]: (r1_tarski(k4_xboole_0(k10_relat_1(B_189, A_190), B_9), k10_relat_1(B_189, k2_relat_1(B_189))) | ~v1_relat_1(B_189))), inference(resolution, [status(thm)], [c_14, c_4954])).
% 13.55/5.60  tff(c_15546, plain, (![A_190, B_9]: (r1_tarski(k4_xboole_0(k10_relat_1('#skF_2', A_190), B_9), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_15507, c_5012])).
% 13.55/5.60  tff(c_15650, plain, (![A_190, B_9]: (r1_tarski(k4_xboole_0(k10_relat_1('#skF_2', A_190), B_9), k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_15546])).
% 13.55/5.60  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.55/5.60  tff(c_84, plain, (![B_36]: (k4_xboole_0(B_36, B_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_71])).
% 13.55/5.60  tff(c_89, plain, (![B_36]: (r1_tarski(k1_xboole_0, B_36))), inference(superposition, [status(thm), theory('equality')], [c_84, c_14])).
% 13.55/5.60  tff(c_229, plain, (![A_45, C_46, B_47]: (r1_tarski(A_45, C_46) | ~r1_tarski(B_47, C_46) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.55/5.60  tff(c_259, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~r1_tarski(A_50, k1_xboole_0))), inference(resolution, [status(thm)], [c_89, c_229])).
% 13.55/5.60  tff(c_265, plain, (![A_3, B_51]: (r1_tarski(A_3, B_51) | k4_xboole_0(A_3, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_259])).
% 13.55/5.60  tff(c_280, plain, (![B_51]: (r1_tarski(k1_xboole_0, B_51))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_265])).
% 13.55/5.60  tff(c_282, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | k1_xboole_0!=A_52)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_265])).
% 13.55/5.60  tff(c_700, plain, (![A_75, B_76, A_77]: (r1_tarski(A_75, B_76) | ~r1_tarski(A_75, A_77) | k1_xboole_0!=A_77)), inference(resolution, [status(thm)], [c_282, c_12])).
% 13.55/5.60  tff(c_726, plain, (![A_78, B_79, B_80]: (r1_tarski(k4_xboole_0(A_78, B_79), B_80) | k1_xboole_0!=A_78)), inference(resolution, [status(thm)], [c_14, c_700])).
% 13.55/5.60  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.55/5.60  tff(c_303, plain, (![B_53, A_52]: (B_53=A_52 | ~r1_tarski(B_53, A_52) | k1_xboole_0!=A_52)), inference(resolution, [status(thm)], [c_282, c_2])).
% 13.55/5.60  tff(c_1257, plain, (![B_79]: (k4_xboole_0(k1_xboole_0, B_79)=k1_xboole_0)), inference(resolution, [status(thm)], [c_726, c_303])).
% 13.55/5.60  tff(c_472, plain, (![A_66, A_67, B_68]: (r1_tarski(A_66, A_67) | ~r1_tarski(A_66, k4_xboole_0(A_67, B_68)))), inference(resolution, [status(thm)], [c_14, c_229])).
% 13.55/5.60  tff(c_514, plain, (![A_69, B_70, B_71]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_69, B_70), B_71), A_69))), inference(resolution, [status(thm)], [c_14, c_472])).
% 13.55/5.60  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.55/5.60  tff(c_577, plain, (![A_69, B_70, B_71]: (k4_xboole_0(k4_xboole_0(k4_xboole_0(A_69, B_70), B_71), A_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_514, c_10])).
% 13.55/5.60  tff(c_1829, plain, (![A_121, B_122, A_123]: (r1_tarski(A_121, B_122) | ~r1_tarski(A_121, A_123) | k4_xboole_0(A_123, B_122)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_229])).
% 13.55/5.60  tff(c_1866, plain, (![A_124, B_125, B_126]: (r1_tarski(k4_xboole_0(A_124, B_125), B_126) | k4_xboole_0(A_124, B_126)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_1829])).
% 13.55/5.60  tff(c_240, plain, (![A_45, A_8, B_9]: (r1_tarski(A_45, A_8) | ~r1_tarski(A_45, k4_xboole_0(A_8, B_9)))), inference(resolution, [status(thm)], [c_14, c_229])).
% 13.55/5.60  tff(c_5464, plain, (![A_206, B_207, A_208, B_209]: (r1_tarski(k4_xboole_0(A_206, B_207), A_208) | k4_xboole_0(A_206, k4_xboole_0(A_208, B_209))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1866, c_240])).
% 13.55/5.60  tff(c_5780, plain, (![B_215, A_214, B_216, B_217, B_218]: (r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(A_214, B_217), B_216), B_218), B_215), A_214))), inference(superposition, [status(thm), theory('equality')], [c_577, c_5464])).
% 13.55/5.60  tff(c_6054, plain, (![B_215, A_214, B_216, B_217, B_218]: (k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(A_214, B_217), B_216), B_218), B_215)=A_214 | k1_xboole_0!=A_214)), inference(resolution, [status(thm)], [c_5780, c_303])).
% 13.55/5.60  tff(c_16394, plain, (![A_360, A_361]: (k4_xboole_0(k10_relat_1(A_360, A_361), k1_relat_1(A_360))=k10_relat_1(A_360, k4_xboole_0(A_361, k2_relat_1(A_360))) | ~v1_funct_1(A_360) | ~v1_relat_1(A_360) | ~v1_relat_1(A_360))), inference(superposition, [status(thm), theory('equality')], [c_20, c_780])).
% 13.55/5.60  tff(c_258, plain, (![B_48, A_49]: (k4_xboole_0(k10_relat_1(B_48, A_49), k10_relat_1(B_48, k2_relat_1(B_48)))=k1_xboole_0 | ~v1_relat_1(B_48))), inference(resolution, [status(thm)], [c_242, c_10])).
% 13.55/5.60  tff(c_15598, plain, (![A_49]: (k4_xboole_0(k10_relat_1('#skF_2', A_49), k1_relat_1('#skF_2'))=k1_xboole_0 | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_15507, c_258])).
% 13.55/5.60  tff(c_15686, plain, (![A_49]: (k4_xboole_0(k10_relat_1('#skF_2', A_49), k1_relat_1('#skF_2'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_15598])).
% 13.55/5.60  tff(c_16405, plain, (![A_361]: (k10_relat_1('#skF_2', k4_xboole_0(A_361, k2_relat_1('#skF_2')))=k1_xboole_0 | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_16394, c_15686])).
% 13.55/5.60  tff(c_16632, plain, (![A_362]: (k10_relat_1('#skF_2', k4_xboole_0(A_362, k2_relat_1('#skF_2')))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_36, c_16405])).
% 13.55/5.60  tff(c_16902, plain, (![A_363]: (k10_relat_1('#skF_2', A_363)=k1_xboole_0 | k1_xboole_0!=A_363)), inference(superposition, [status(thm), theory('equality')], [c_6054, c_16632])).
% 13.55/5.60  tff(c_811, plain, (![C_81, A_82, B_83]: (r1_tarski(k10_relat_1(C_81, k4_xboole_0(A_82, B_83)), k10_relat_1(C_81, A_82)) | ~v1_funct_1(C_81) | ~v1_relat_1(C_81))), inference(superposition, [status(thm), theory('equality')], [c_780, c_14])).
% 13.55/5.60  tff(c_17006, plain, (![A_363, B_83]: (r1_tarski(k10_relat_1('#skF_2', k4_xboole_0(A_363, B_83)), k1_xboole_0) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | k1_xboole_0!=A_363)), inference(superposition, [status(thm), theory('equality')], [c_16902, c_811])).
% 13.55/5.60  tff(c_19786, plain, (![A_383, B_384]: (r1_tarski(k10_relat_1('#skF_2', k4_xboole_0(A_383, B_384)), k1_xboole_0) | k1_xboole_0!=A_383)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_17006])).
% 13.55/5.60  tff(c_19999, plain, (![A_385]: (r1_tarski(k10_relat_1('#skF_2', A_385), k1_xboole_0) | k1_xboole_0!=A_385)), inference(superposition, [status(thm), theory('equality')], [c_16, c_19786])).
% 13.55/5.60  tff(c_239, plain, (![A_45, B_4, A_3]: (r1_tarski(A_45, B_4) | ~r1_tarski(A_45, A_3) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_229])).
% 13.55/5.60  tff(c_20009, plain, (![A_385, B_4]: (r1_tarski(k10_relat_1('#skF_2', A_385), B_4) | k4_xboole_0(k1_xboole_0, B_4)!=k1_xboole_0 | k1_xboole_0!=A_385)), inference(resolution, [status(thm)], [c_19999, c_239])).
% 13.55/5.60  tff(c_20094, plain, (![A_386, B_387]: (r1_tarski(k10_relat_1('#skF_2', A_386), B_387) | k1_xboole_0!=A_386)), inference(demodulation, [status(thm), theory('equality')], [c_1257, c_20009])).
% 13.55/5.60  tff(c_20727, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_20094, c_303])).
% 13.55/5.60  tff(c_34, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 13.55/5.60  tff(c_39, plain, (![C_21, A_19, B_20]: (k4_xboole_0(k10_relat_1(C_21, A_19), k10_relat_1(C_21, B_20))=k10_relat_1(C_21, k4_xboole_0(A_19, B_20)) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_26])).
% 13.55/5.60  tff(c_17058, plain, (![A_19, A_363]: (k4_xboole_0(k10_relat_1('#skF_2', A_19), k1_xboole_0)=k10_relat_1('#skF_2', k4_xboole_0(A_19, A_363)) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | k1_xboole_0!=A_363)), inference(superposition, [status(thm), theory('equality')], [c_16902, c_39])).
% 13.55/5.60  tff(c_24442, plain, (![A_423, A_424]: (k10_relat_1('#skF_2', k4_xboole_0(A_423, A_424))=k10_relat_1('#skF_2', A_423) | k1_xboole_0!=A_424)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_16, c_17058])).
% 13.55/5.60  tff(c_28, plain, (![B_23, A_22]: (r1_tarski(k9_relat_1(B_23, k10_relat_1(B_23, A_22)), A_22) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.55/5.60  tff(c_508, plain, (![B_23, A_67, B_68]: (r1_tarski(k9_relat_1(B_23, k10_relat_1(B_23, k4_xboole_0(A_67, B_68))), A_67) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(resolution, [status(thm)], [c_28, c_472])).
% 13.55/5.60  tff(c_24448, plain, (![A_423, A_424]: (r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_423)), A_423) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | k1_xboole_0!=A_424)), inference(superposition, [status(thm), theory('equality')], [c_24442, c_508])).
% 13.55/5.60  tff(c_24751, plain, (![A_423, A_424]: (r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_423)), A_423) | k1_xboole_0!=A_424)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_24448])).
% 13.55/5.60  tff(c_24859, plain, (![A_424]: (k1_xboole_0!=A_424)), inference(splitLeft, [status(thm)], [c_24751])).
% 13.55/5.60  tff(c_354, plain, (![B_56, A_57]: (r1_tarski(k9_relat_1(B_56, k10_relat_1(B_56, A_57)), A_57) | ~v1_funct_1(B_56) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.55/5.60  tff(c_373, plain, (![A_5, A_57, B_56]: (r1_tarski(A_5, A_57) | ~r1_tarski(A_5, k9_relat_1(B_56, k10_relat_1(B_56, A_57))) | ~v1_funct_1(B_56) | ~v1_relat_1(B_56))), inference(resolution, [status(thm)], [c_354, c_12])).
% 13.55/5.60  tff(c_15555, plain, (![A_5]: (r1_tarski(A_5, k2_relat_1('#skF_2')) | ~r1_tarski(A_5, k9_relat_1('#skF_2', k1_relat_1('#skF_2'))) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_15507, c_373])).
% 13.55/5.60  tff(c_18124, plain, (![A_372]: (r1_tarski(A_372, k2_relat_1('#skF_2')) | ~r1_tarski(A_372, k9_relat_1('#skF_2', k1_relat_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_15555])).
% 13.55/5.60  tff(c_18914, plain, (![B_378]: (r1_tarski(k4_xboole_0(k9_relat_1('#skF_2', k1_relat_1('#skF_2')), B_378), k2_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_14, c_18124])).
% 13.55/5.60  tff(c_18990, plain, (![B_378]: (k4_xboole_0(k4_xboole_0(k9_relat_1('#skF_2', k1_relat_1('#skF_2')), B_378), k2_relat_1('#skF_2'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_18914, c_10])).
% 13.55/5.60  tff(c_25063, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24859, c_18990])).
% 13.55/5.60  tff(c_25065, plain, (![A_427]: (r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_427)), A_427))), inference(splitRight, [status(thm)], [c_24751])).
% 13.55/5.60  tff(c_25415, plain, (![A_429]: (k4_xboole_0(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_429)), A_429)=k1_xboole_0)), inference(resolution, [status(thm)], [c_25065, c_10])).
% 13.55/5.60  tff(c_24, plain, (![C_18, A_16, B_17]: (k6_subset_1(k9_relat_1(C_18, A_16), k9_relat_1(C_18, B_17))=k9_relat_1(C_18, k6_subset_1(A_16, B_17)) | ~v2_funct_1(C_18) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.55/5.60  tff(c_40, plain, (![C_18, A_16, B_17]: (k4_xboole_0(k9_relat_1(C_18, A_16), k9_relat_1(C_18, B_17))=k9_relat_1(C_18, k4_xboole_0(A_16, B_17)) | ~v2_funct_1(C_18) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_24])).
% 13.55/5.60  tff(c_25600, plain, (![B_17]: (k9_relat_1('#skF_2', k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_17)), B_17))=k1_xboole_0 | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_25415, c_40])).
% 13.55/5.60  tff(c_25786, plain, (![B_17]: (k9_relat_1('#skF_2', k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_17)), B_17))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_25600])).
% 13.55/5.60  tff(c_39669, plain, (![B_520]: (k9_relat_1('#skF_2', k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_520)), B_520))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_25600])).
% 13.55/5.60  tff(c_457, plain, (![A_64, B_65]: (r1_tarski(A_64, k10_relat_1(B_65, k9_relat_1(B_65, A_64))) | ~r1_tarski(A_64, k1_relat_1(B_65)) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.55/5.60  tff(c_470, plain, (![B_65, A_64]: (k10_relat_1(B_65, k9_relat_1(B_65, A_64))=A_64 | ~r1_tarski(k10_relat_1(B_65, k9_relat_1(B_65, A_64)), A_64) | ~r1_tarski(A_64, k1_relat_1(B_65)) | ~v1_relat_1(B_65))), inference(resolution, [status(thm)], [c_457, c_2])).
% 13.55/5.60  tff(c_39713, plain, (![B_520]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_520)), B_520)))=k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_520)), B_520) | ~r1_tarski(k10_relat_1('#skF_2', k1_xboole_0), k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_520)), B_520)) | ~r1_tarski(k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_520)), B_520), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_39669, c_470])).
% 13.55/5.60  tff(c_39886, plain, (![B_520]: (k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_520)), B_520)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_15650, c_280, c_20727, c_20727, c_25786, c_39713])).
% 13.55/5.60  tff(c_66, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | k4_xboole_0(A_32, B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.55/5.60  tff(c_32, plain, (~r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 13.55/5.60  tff(c_70, plain, (k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_32])).
% 13.55/5.60  tff(c_39942, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39886, c_70])).
% 13.55/5.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.55/5.60  
% 13.55/5.60  Inference rules
% 13.55/5.60  ----------------------
% 13.55/5.60  #Ref     : 9
% 13.55/5.60  #Sup     : 10109
% 13.55/5.60  #Fact    : 0
% 13.55/5.60  #Define  : 0
% 13.55/5.60  #Split   : 6
% 13.55/5.60  #Chain   : 0
% 13.55/5.60  #Close   : 0
% 13.55/5.60  
% 13.55/5.60  Ordering : KBO
% 13.55/5.60  
% 13.55/5.60  Simplification rules
% 13.55/5.60  ----------------------
% 13.55/5.60  #Subsume      : 4569
% 13.55/5.60  #Demod        : 7535
% 13.55/5.60  #Tautology    : 3505
% 13.55/5.60  #SimpNegUnit  : 199
% 13.55/5.60  #BackRed      : 65
% 13.55/5.60  
% 13.55/5.60  #Partial instantiations: 0
% 13.55/5.60  #Strategies tried      : 1
% 13.55/5.60  
% 13.55/5.60  Timing (in seconds)
% 13.55/5.60  ----------------------
% 13.55/5.61  Preprocessing        : 0.31
% 13.55/5.61  Parsing              : 0.17
% 13.55/5.61  CNF conversion       : 0.02
% 13.55/5.61  Main loop            : 4.52
% 13.55/5.61  Inferencing          : 0.89
% 13.55/5.61  Reduction            : 1.99
% 13.55/5.61  Demodulation         : 1.63
% 13.55/5.61  BG Simplification    : 0.09
% 13.55/5.61  Subsumption          : 1.33
% 13.55/5.61  Abstraction          : 0.17
% 13.55/5.61  MUC search           : 0.00
% 13.55/5.61  Cooper               : 0.00
% 13.55/5.61  Total                : 4.88
% 13.55/5.61  Index Insertion      : 0.00
% 13.55/5.61  Index Deletion       : 0.00
% 13.55/5.61  Index Matching       : 0.00
% 13.55/5.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
