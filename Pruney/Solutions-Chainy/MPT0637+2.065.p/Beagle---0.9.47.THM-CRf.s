%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:32 EST 2020

% Result     : Theorem 15.33s
% Output     : CNFRefutation 15.41s
% Verified   : 
% Statistics : Number of formulae       :  141 (1464 expanded)
%              Number of leaves         :   36 ( 525 expanded)
%              Depth                    :   21
%              Number of atoms          :  246 (2428 expanded)
%              Number of equality atoms :   84 ( 923 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_49,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_86,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_20,plain,(
    ! [A_34] : v1_relat_1(k6_relat_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    ! [A_59,B_60] :
      ( k5_relat_1(k6_relat_1(A_59),B_60) = k7_relat_1(B_60,A_59)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_34,plain,(
    ! [A_53] : k4_relat_1(k6_relat_1(A_53)) = k6_relat_1(A_53) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_731,plain,(
    ! [B_123,A_124] :
      ( k5_relat_1(k4_relat_1(B_123),k4_relat_1(A_124)) = k4_relat_1(k5_relat_1(A_124,B_123))
      | ~ v1_relat_1(B_123)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_746,plain,(
    ! [A_53,A_124] :
      ( k5_relat_1(k6_relat_1(A_53),k4_relat_1(A_124)) = k4_relat_1(k5_relat_1(A_124,k6_relat_1(A_53)))
      | ~ v1_relat_1(k6_relat_1(A_53))
      | ~ v1_relat_1(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_731])).

tff(c_802,plain,(
    ! [A_127,A_128] :
      ( k5_relat_1(k6_relat_1(A_127),k4_relat_1(A_128)) = k4_relat_1(k5_relat_1(A_128,k6_relat_1(A_127)))
      | ~ v1_relat_1(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_746])).

tff(c_832,plain,(
    ! [A_53,A_127] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_53),k6_relat_1(A_127))) = k5_relat_1(k6_relat_1(A_127),k6_relat_1(A_53))
      | ~ v1_relat_1(k6_relat_1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_802])).

tff(c_943,plain,(
    ! [A_136,A_137] : k4_relat_1(k5_relat_1(k6_relat_1(A_136),k6_relat_1(A_137))) = k5_relat_1(k6_relat_1(A_137),k6_relat_1(A_136)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_832])).

tff(c_18,plain,(
    ! [A_32,B_33] :
      ( v1_relat_1(k5_relat_1(A_32,B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_818,plain,(
    ! [A_128,A_127] :
      ( v1_relat_1(k4_relat_1(k5_relat_1(A_128,k6_relat_1(A_127))))
      | ~ v1_relat_1(k4_relat_1(A_128))
      | ~ v1_relat_1(k6_relat_1(A_127))
      | ~ v1_relat_1(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_802,c_18])).

tff(c_837,plain,(
    ! [A_128,A_127] :
      ( v1_relat_1(k4_relat_1(k5_relat_1(A_128,k6_relat_1(A_127))))
      | ~ v1_relat_1(k4_relat_1(A_128))
      | ~ v1_relat_1(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_818])).

tff(c_949,plain,(
    ! [A_137,A_136] :
      ( v1_relat_1(k5_relat_1(k6_relat_1(A_137),k6_relat_1(A_136)))
      | ~ v1_relat_1(k4_relat_1(k6_relat_1(A_136)))
      | ~ v1_relat_1(k6_relat_1(A_136)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_943,c_837])).

tff(c_992,plain,(
    ! [A_138,A_139] : v1_relat_1(k5_relat_1(k6_relat_1(A_138),k6_relat_1(A_139))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_34,c_949])).

tff(c_1002,plain,(
    ! [A_139,A_59] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_139),A_59))
      | ~ v1_relat_1(k6_relat_1(A_139)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_992])).

tff(c_1013,plain,(
    ! [A_139,A_59] : v1_relat_1(k7_relat_1(k6_relat_1(A_139),A_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1002])).

tff(c_972,plain,(
    ! [A_137,A_59] :
      ( k5_relat_1(k6_relat_1(A_137),k6_relat_1(A_59)) = k4_relat_1(k7_relat_1(k6_relat_1(A_137),A_59))
      | ~ v1_relat_1(k6_relat_1(A_137)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_943])).

tff(c_1444,plain,(
    ! [A_163,A_164] : k5_relat_1(k6_relat_1(A_163),k6_relat_1(A_164)) = k4_relat_1(k7_relat_1(k6_relat_1(A_163),A_164)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_972])).

tff(c_1491,plain,(
    ! [A_59,A_164] :
      ( k4_relat_1(k7_relat_1(k6_relat_1(A_59),A_164)) = k7_relat_1(k6_relat_1(A_164),A_59)
      | ~ v1_relat_1(k6_relat_1(A_164)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1444])).

tff(c_1523,plain,(
    ! [A_59,A_164] : k4_relat_1(k7_relat_1(k6_relat_1(A_59),A_164)) = k7_relat_1(k6_relat_1(A_164),A_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1491])).

tff(c_30,plain,(
    ! [A_52] : k1_relat_1(k6_relat_1(A_52)) = A_52 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_195,plain,(
    ! [B_83,A_84] :
      ( k3_xboole_0(k1_relat_1(B_83),A_84) = k1_relat_1(k7_relat_1(B_83,A_84))
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_207,plain,(
    ! [A_52,A_84] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_52),A_84)) = k3_xboole_0(A_52,A_84)
      | ~ v1_relat_1(k6_relat_1(A_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_195])).

tff(c_211,plain,(
    ! [A_52,A_84] : k1_relat_1(k7_relat_1(k6_relat_1(A_52),A_84)) = k3_xboole_0(A_52,A_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_207])).

tff(c_32,plain,(
    ! [A_52] : k2_relat_1(k6_relat_1(A_52)) = A_52 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_38,plain,(
    ! [A_56] :
      ( k5_relat_1(A_56,k6_relat_1(k2_relat_1(A_56))) = A_56
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_126,plain,(
    ! [A_75,B_76] :
      ( k5_relat_1(k6_relat_1(A_75),B_76) = k7_relat_1(B_76,A_75)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_153,plain,(
    ! [A_75] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_75))),A_75) = k6_relat_1(A_75)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_75))))
      | ~ v1_relat_1(k6_relat_1(A_75)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_126])).

tff(c_167,plain,(
    ! [A_75] : k7_relat_1(k6_relat_1(A_75),A_75) = k6_relat_1(A_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_32,c_153])).

tff(c_212,plain,(
    ! [A_85,A_86] : k1_relat_1(k7_relat_1(k6_relat_1(A_85),A_86)) = k3_xboole_0(A_85,A_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_207])).

tff(c_224,plain,(
    ! [A_75] : k3_xboole_0(A_75,A_75) = k1_relat_1(k6_relat_1(A_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_212])).

tff(c_228,plain,(
    ! [A_87] : k3_xboole_0(A_87,A_87) = A_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_224])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_238,plain,(
    ! [A_87] : r1_tarski(A_87,A_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_2])).

tff(c_323,plain,(
    ! [A_96,B_97] :
      ( k5_relat_1(k6_relat_1(A_96),B_97) = B_97
      | ~ r1_tarski(k1_relat_1(B_97),A_96)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_341,plain,(
    ! [B_97] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_97)),B_97) = B_97
      | ~ v1_relat_1(B_97) ) ),
    inference(resolution,[status(thm)],[c_238,c_323])).

tff(c_24,plain,(
    ! [A_39,B_41] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_39,B_41)),k2_relat_1(B_41))
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6312,plain,(
    ! [A_331,B_332] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(A_331,B_332))),k2_relat_1(k4_relat_1(A_331)))
      | ~ v1_relat_1(k4_relat_1(A_331))
      | ~ v1_relat_1(k4_relat_1(B_332))
      | ~ v1_relat_1(B_332)
      | ~ v1_relat_1(A_331) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_731,c_24])).

tff(c_6369,plain,(
    ! [B_97] :
      ( r1_tarski(k2_relat_1(k4_relat_1(B_97)),k2_relat_1(k4_relat_1(k6_relat_1(k1_relat_1(B_97)))))
      | ~ v1_relat_1(k4_relat_1(k6_relat_1(k1_relat_1(B_97))))
      | ~ v1_relat_1(k4_relat_1(B_97))
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(B_97)))
      | ~ v1_relat_1(B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_6312])).

tff(c_6418,plain,(
    ! [B_333] :
      ( r1_tarski(k2_relat_1(k4_relat_1(B_333)),k1_relat_1(B_333))
      | ~ v1_relat_1(k4_relat_1(B_333))
      | ~ v1_relat_1(B_333) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_34,c_32,c_34,c_6369])).

tff(c_6436,plain,(
    ! [A_164,A_59] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_164),A_59)),k1_relat_1(k7_relat_1(k6_relat_1(A_59),A_164)))
      | ~ v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_59),A_164)))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_59),A_164)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1523,c_6418])).

tff(c_6463,plain,(
    ! [A_334,A_335] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_334),A_335)),k3_xboole_0(A_335,A_334)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1013,c_1013,c_1523,c_211,c_6436])).

tff(c_339,plain,(
    ! [A_96,A_52] :
      ( k5_relat_1(k6_relat_1(A_96),k6_relat_1(A_52)) = k6_relat_1(A_52)
      | ~ r1_tarski(A_52,A_96)
      | ~ v1_relat_1(k6_relat_1(A_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_323])).

tff(c_343,plain,(
    ! [A_96,A_52] :
      ( k5_relat_1(k6_relat_1(A_96),k6_relat_1(A_52)) = k6_relat_1(A_52)
      | ~ r1_tarski(A_52,A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_339])).

tff(c_964,plain,(
    ! [A_52,A_96] :
      ( k5_relat_1(k6_relat_1(A_52),k6_relat_1(A_96)) = k4_relat_1(k6_relat_1(A_52))
      | ~ r1_tarski(A_52,A_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_943])).

tff(c_1030,plain,(
    ! [A_142,A_143] :
      ( k5_relat_1(k6_relat_1(A_142),k6_relat_1(A_143)) = k6_relat_1(A_142)
      | ~ r1_tarski(A_142,A_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_964])).

tff(c_1060,plain,(
    ! [A_143,A_142] :
      ( k7_relat_1(k6_relat_1(A_143),A_142) = k6_relat_1(A_142)
      | ~ v1_relat_1(k6_relat_1(A_143))
      | ~ r1_tarski(A_142,A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_42])).

tff(c_1110,plain,(
    ! [A_143,A_142] :
      ( k7_relat_1(k6_relat_1(A_143),A_142) = k6_relat_1(A_142)
      | ~ r1_tarski(A_142,A_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1060])).

tff(c_867,plain,(
    ! [B_131,C_132,A_133] :
      ( k7_relat_1(k5_relat_1(B_131,C_132),A_133) = k5_relat_1(k7_relat_1(B_131,A_133),C_132)
      | ~ v1_relat_1(C_132)
      | ~ v1_relat_1(B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_909,plain,(
    ! [A_59,A_133,B_60] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_59),A_133),B_60) = k7_relat_1(k7_relat_1(B_60,A_59),A_133)
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(k6_relat_1(A_59))
      | ~ v1_relat_1(B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_867])).

tff(c_2395,plain,(
    ! [A_206,A_207,B_208] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_206),A_207),B_208) = k7_relat_1(k7_relat_1(B_208,A_206),A_207)
      | ~ v1_relat_1(B_208) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_909])).

tff(c_376,plain,(
    ! [A_99,B_100] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_99,B_100)),k2_relat_1(B_100))
      | ~ v1_relat_1(B_100)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_391,plain,(
    ! [A_99,A_52] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_99,k6_relat_1(A_52))),A_52)
      | ~ v1_relat_1(k6_relat_1(A_52))
      | ~ v1_relat_1(A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_376])).

tff(c_401,plain,(
    ! [A_99,A_52] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_99,k6_relat_1(A_52))),A_52)
      | ~ v1_relat_1(A_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_391])).

tff(c_2424,plain,(
    ! [A_52,A_206,A_207] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_52),A_206),A_207)),A_52)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_206),A_207))
      | ~ v1_relat_1(k6_relat_1(A_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2395,c_401])).

tff(c_2541,plain,(
    ! [A_215,A_216,A_217] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_215),A_216),A_217)),A_215) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1013,c_2424])).

tff(c_2709,plain,(
    ! [A_222,A_223,A_224] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_222),A_223)),A_224)
      | ~ r1_tarski(A_222,A_224) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1110,c_2541])).

tff(c_2736,plain,(
    ! [A_142,A_224,A_143] :
      ( r1_tarski(k2_relat_1(k6_relat_1(A_142)),A_224)
      | ~ r1_tarski(A_143,A_224)
      | ~ r1_tarski(A_142,A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1110,c_2709])).

tff(c_2762,plain,(
    ! [A_225,A_226,A_227] :
      ( r1_tarski(A_225,A_226)
      | ~ r1_tarski(A_227,A_226)
      | ~ r1_tarski(A_225,A_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2736])).

tff(c_2795,plain,(
    ! [A_225,A_1,B_2] :
      ( r1_tarski(A_225,A_1)
      | ~ r1_tarski(A_225,k3_xboole_0(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_2,c_2762])).

tff(c_6566,plain,(
    ! [A_336,A_337] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_336),A_337)),A_337) ),
    inference(resolution,[status(thm)],[c_6463,c_2795])).

tff(c_496,plain,(
    ! [A_113,A_114] :
      ( k5_relat_1(k6_relat_1(A_113),k6_relat_1(A_114)) = k6_relat_1(A_114)
      | ~ r1_tarski(A_114,A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_339])).

tff(c_512,plain,(
    ! [A_114,A_113] :
      ( k7_relat_1(k6_relat_1(A_114),A_113) = k6_relat_1(A_114)
      | ~ v1_relat_1(k6_relat_1(A_114))
      | ~ r1_tarski(A_114,A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_42])).

tff(c_573,plain,(
    ! [A_115,A_116] :
      ( k7_relat_1(k6_relat_1(A_115),A_116) = k6_relat_1(A_115)
      | ~ r1_tarski(A_115,A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_512])).

tff(c_596,plain,(
    ! [A_115,A_116] :
      ( k3_xboole_0(A_115,A_116) = k1_relat_1(k6_relat_1(A_115))
      | ~ r1_tarski(A_115,A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_211])).

tff(c_628,plain,(
    ! [A_115,A_116] :
      ( k3_xboole_0(A_115,A_116) = A_115
      | ~ r1_tarski(A_115,A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_596])).

tff(c_6635,plain,(
    ! [A_336,A_337] : k3_xboole_0(k2_relat_1(k7_relat_1(k6_relat_1(A_336),A_337)),A_337) = k2_relat_1(k7_relat_1(k6_relat_1(A_336),A_337)) ),
    inference(resolution,[status(thm)],[c_6566,c_628])).

tff(c_227,plain,(
    ! [A_75] : k3_xboole_0(A_75,A_75) = A_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_224])).

tff(c_988,plain,(
    ! [A_137,A_59] : k5_relat_1(k6_relat_1(A_137),k6_relat_1(A_59)) = k4_relat_1(k7_relat_1(k6_relat_1(A_137),A_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_972])).

tff(c_1585,plain,(
    ! [A_137,A_59] : k5_relat_1(k6_relat_1(A_137),k6_relat_1(A_59)) = k7_relat_1(k6_relat_1(A_59),A_137) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1523,c_988])).

tff(c_1352,plain,(
    ! [A_160,B_161,C_162] :
      ( k5_relat_1(k5_relat_1(A_160,B_161),C_162) = k5_relat_1(A_160,k5_relat_1(B_161,C_162))
      | ~ v1_relat_1(C_162)
      | ~ v1_relat_1(B_161)
      | ~ v1_relat_1(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1409,plain,(
    ! [A_56,C_162] :
      ( k5_relat_1(A_56,k5_relat_1(k6_relat_1(k2_relat_1(A_56)),C_162)) = k5_relat_1(A_56,C_162)
      | ~ v1_relat_1(C_162)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_56)))
      | ~ v1_relat_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1352])).

tff(c_2940,plain,(
    ! [A_234,C_235] :
      ( k5_relat_1(A_234,k5_relat_1(k6_relat_1(k2_relat_1(A_234)),C_235)) = k5_relat_1(A_234,C_235)
      | ~ v1_relat_1(C_235)
      | ~ v1_relat_1(A_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1409])).

tff(c_3023,plain,(
    ! [A_52,C_235] :
      ( k5_relat_1(k6_relat_1(A_52),k5_relat_1(k6_relat_1(A_52),C_235)) = k5_relat_1(k6_relat_1(A_52),C_235)
      | ~ v1_relat_1(C_235)
      | ~ v1_relat_1(k6_relat_1(A_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2940])).

tff(c_19480,plain,(
    ! [A_553,C_554] :
      ( k5_relat_1(k6_relat_1(A_553),k5_relat_1(k6_relat_1(A_553),C_554)) = k5_relat_1(k6_relat_1(A_553),C_554)
      | ~ v1_relat_1(C_554) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_3023])).

tff(c_19606,plain,(
    ! [A_137,A_59] :
      ( k5_relat_1(k6_relat_1(A_137),k7_relat_1(k6_relat_1(A_59),A_137)) = k5_relat_1(k6_relat_1(A_137),k6_relat_1(A_59))
      | ~ v1_relat_1(k6_relat_1(A_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1585,c_19480])).

tff(c_19873,plain,(
    ! [A_559,A_560] : k5_relat_1(k6_relat_1(A_559),k7_relat_1(k6_relat_1(A_560),A_559)) = k7_relat_1(k6_relat_1(A_560),A_559) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1585,c_19606])).

tff(c_19943,plain,(
    ! [A_560,A_559] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_560),A_559),A_559) = k7_relat_1(k6_relat_1(A_560),A_559)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_560),A_559)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19873,c_42])).

tff(c_20140,plain,(
    ! [A_563,A_564] : k7_relat_1(k7_relat_1(k6_relat_1(A_563),A_564),A_564) = k7_relat_1(k6_relat_1(A_563),A_564) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1013,c_19943])).

tff(c_40,plain,(
    ! [B_58,A_57] :
      ( k3_xboole_0(k1_relat_1(B_58),A_57) = k1_relat_1(k7_relat_1(B_58,A_57))
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_641,plain,(
    ! [A_117,A_118] :
      ( k3_xboole_0(A_117,A_118) = A_117
      | ~ r1_tarski(A_117,A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_596])).

tff(c_672,plain,(
    ! [A_119,B_120] : k3_xboole_0(k3_xboole_0(A_119,B_120),A_119) = k3_xboole_0(A_119,B_120) ),
    inference(resolution,[status(thm)],[c_2,c_641])).

tff(c_693,plain,(
    ! [B_58,A_57] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_58,A_57)),k1_relat_1(B_58)) = k3_xboole_0(k1_relat_1(B_58),A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_672])).

tff(c_20232,plain,(
    ! [A_563,A_564] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_563),A_564)),k1_relat_1(k7_relat_1(k6_relat_1(A_563),A_564))) = k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_563),A_564)),A_564)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_563),A_564)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20140,c_693])).

tff(c_20334,plain,(
    ! [A_563,A_564] : k3_xboole_0(k3_xboole_0(A_563,A_564),A_564) = k3_xboole_0(A_563,A_564) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1013,c_227,c_211,c_211,c_211,c_20232])).

tff(c_382,plain,(
    ! [B_60,A_59] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_60,A_59)),k2_relat_1(B_60))
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(k6_relat_1(A_59))
      | ~ v1_relat_1(B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_376])).

tff(c_402,plain,(
    ! [B_101,A_102] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_101,A_102)),k2_relat_1(B_101))
      | ~ v1_relat_1(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_382])).

tff(c_408,plain,(
    ! [A_52,A_102] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_52),A_102)),A_52)
      | ~ v1_relat_1(k6_relat_1(A_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_402])).

tff(c_412,plain,(
    ! [A_52,A_102] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_52),A_102)),A_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_408])).

tff(c_899,plain,(
    ! [A_96,A_133,A_52] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_96),A_133),k6_relat_1(A_52)) = k7_relat_1(k6_relat_1(A_52),A_133)
      | ~ v1_relat_1(k6_relat_1(A_52))
      | ~ v1_relat_1(k6_relat_1(A_96))
      | ~ r1_tarski(A_52,A_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_867])).

tff(c_35814,plain,(
    ! [A_720,A_721,A_722] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_720),A_721),k6_relat_1(A_722)) = k7_relat_1(k6_relat_1(A_722),A_721)
      | ~ r1_tarski(A_722,A_720) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_899])).

tff(c_35905,plain,(
    ! [A_720,A_721] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_720),A_721))),A_721) = k7_relat_1(k6_relat_1(A_720),A_721)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_720),A_721))
      | ~ r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_720),A_721)),A_720) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35814,c_38])).

tff(c_36058,plain,(
    ! [A_723,A_724] : k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_723),A_724))),A_724) = k7_relat_1(k6_relat_1(A_723),A_724) ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_1013,c_35905])).

tff(c_20412,plain,(
    ! [A_568,A_569] : k3_xboole_0(k3_xboole_0(A_568,A_569),A_569) = k3_xboole_0(A_568,A_569) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1013,c_227,c_211,c_211,c_211,c_20232])).

tff(c_20697,plain,(
    ! [B_58,A_57] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_58,A_57)),A_57) = k3_xboole_0(k1_relat_1(B_58),A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_20412])).

tff(c_36161,plain,(
    ! [A_723,A_724] :
      ( k3_xboole_0(k1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_723),A_724)))),A_724) = k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_723),A_724)),A_724)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_723),A_724)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36058,c_20697])).

tff(c_36489,plain,(
    ! [A_723,A_724] : k2_relat_1(k7_relat_1(k6_relat_1(A_723),A_724)) = k3_xboole_0(A_723,A_724) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6635,c_20334,c_211,c_30,c_36161])).

tff(c_6549,plain,(
    ! [A_334,A_335] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_334),A_335)),A_335) ),
    inference(resolution,[status(thm)],[c_6463,c_2795])).

tff(c_554,plain,(
    ! [A_114,A_113] :
      ( k7_relat_1(k6_relat_1(A_114),A_113) = k6_relat_1(A_114)
      | ~ r1_tarski(A_114,A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_512])).

tff(c_36447,plain,(
    ! [A_723,A_113] :
      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_723),A_113))) = k7_relat_1(k6_relat_1(A_723),A_113)
      | ~ r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_723),A_113)),A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_36058])).

tff(c_36590,plain,(
    ! [A_723,A_113] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_723),A_113))) = k7_relat_1(k6_relat_1(A_723),A_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6549,c_36447])).

tff(c_54095,plain,(
    ! [A_723,A_113] : k7_relat_1(k6_relat_1(A_723),A_113) = k6_relat_1(k3_xboole_0(A_723,A_113)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36489,c_36590])).

tff(c_44,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_135,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_44])).

tff(c_158,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_135])).

tff(c_54159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54095,c_158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.33/7.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.41/7.82  
% 15.41/7.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.41/7.82  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 15.41/7.82  
% 15.41/7.82  %Foreground sorts:
% 15.41/7.82  
% 15.41/7.82  
% 15.41/7.82  %Background operators:
% 15.41/7.82  
% 15.41/7.82  
% 15.41/7.82  %Foreground operators:
% 15.41/7.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.41/7.82  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 15.41/7.82  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 15.41/7.82  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 15.41/7.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.41/7.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 15.41/7.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.41/7.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.41/7.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.41/7.82  tff('#skF_2', type, '#skF_2': $i).
% 15.41/7.82  tff('#skF_1', type, '#skF_1': $i).
% 15.41/7.82  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.41/7.82  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 15.41/7.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.41/7.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.41/7.82  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 15.41/7.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.41/7.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.41/7.82  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 15.41/7.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.41/7.82  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 15.41/7.82  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 15.41/7.82  
% 15.41/7.85  tff(f_49, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 15.41/7.85  tff(f_104, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 15.41/7.85  tff(f_86, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 15.41/7.85  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 15.41/7.85  tff(f_47, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 15.41/7.85  tff(f_84, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 15.41/7.85  tff(f_100, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 15.41/7.85  tff(f_96, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 15.41/7.85  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 15.41/7.85  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 15.41/7.85  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 15.41/7.85  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 15.41/7.85  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 15.41/7.85  tff(f_107, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 15.41/7.85  tff(c_20, plain, (![A_34]: (v1_relat_1(k6_relat_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.41/7.85  tff(c_42, plain, (![A_59, B_60]: (k5_relat_1(k6_relat_1(A_59), B_60)=k7_relat_1(B_60, A_59) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_104])).
% 15.41/7.85  tff(c_34, plain, (![A_53]: (k4_relat_1(k6_relat_1(A_53))=k6_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.41/7.85  tff(c_731, plain, (![B_123, A_124]: (k5_relat_1(k4_relat_1(B_123), k4_relat_1(A_124))=k4_relat_1(k5_relat_1(A_124, B_123)) | ~v1_relat_1(B_123) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.41/7.85  tff(c_746, plain, (![A_53, A_124]: (k5_relat_1(k6_relat_1(A_53), k4_relat_1(A_124))=k4_relat_1(k5_relat_1(A_124, k6_relat_1(A_53))) | ~v1_relat_1(k6_relat_1(A_53)) | ~v1_relat_1(A_124))), inference(superposition, [status(thm), theory('equality')], [c_34, c_731])).
% 15.41/7.85  tff(c_802, plain, (![A_127, A_128]: (k5_relat_1(k6_relat_1(A_127), k4_relat_1(A_128))=k4_relat_1(k5_relat_1(A_128, k6_relat_1(A_127))) | ~v1_relat_1(A_128))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_746])).
% 15.41/7.85  tff(c_832, plain, (![A_53, A_127]: (k4_relat_1(k5_relat_1(k6_relat_1(A_53), k6_relat_1(A_127)))=k5_relat_1(k6_relat_1(A_127), k6_relat_1(A_53)) | ~v1_relat_1(k6_relat_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_802])).
% 15.41/7.85  tff(c_943, plain, (![A_136, A_137]: (k4_relat_1(k5_relat_1(k6_relat_1(A_136), k6_relat_1(A_137)))=k5_relat_1(k6_relat_1(A_137), k6_relat_1(A_136)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_832])).
% 15.41/7.85  tff(c_18, plain, (![A_32, B_33]: (v1_relat_1(k5_relat_1(A_32, B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.41/7.85  tff(c_818, plain, (![A_128, A_127]: (v1_relat_1(k4_relat_1(k5_relat_1(A_128, k6_relat_1(A_127)))) | ~v1_relat_1(k4_relat_1(A_128)) | ~v1_relat_1(k6_relat_1(A_127)) | ~v1_relat_1(A_128))), inference(superposition, [status(thm), theory('equality')], [c_802, c_18])).
% 15.41/7.85  tff(c_837, plain, (![A_128, A_127]: (v1_relat_1(k4_relat_1(k5_relat_1(A_128, k6_relat_1(A_127)))) | ~v1_relat_1(k4_relat_1(A_128)) | ~v1_relat_1(A_128))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_818])).
% 15.41/7.85  tff(c_949, plain, (![A_137, A_136]: (v1_relat_1(k5_relat_1(k6_relat_1(A_137), k6_relat_1(A_136))) | ~v1_relat_1(k4_relat_1(k6_relat_1(A_136))) | ~v1_relat_1(k6_relat_1(A_136)))), inference(superposition, [status(thm), theory('equality')], [c_943, c_837])).
% 15.41/7.85  tff(c_992, plain, (![A_138, A_139]: (v1_relat_1(k5_relat_1(k6_relat_1(A_138), k6_relat_1(A_139))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_34, c_949])).
% 15.41/7.85  tff(c_1002, plain, (![A_139, A_59]: (v1_relat_1(k7_relat_1(k6_relat_1(A_139), A_59)) | ~v1_relat_1(k6_relat_1(A_139)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_992])).
% 15.41/7.85  tff(c_1013, plain, (![A_139, A_59]: (v1_relat_1(k7_relat_1(k6_relat_1(A_139), A_59)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1002])).
% 15.41/7.85  tff(c_972, plain, (![A_137, A_59]: (k5_relat_1(k6_relat_1(A_137), k6_relat_1(A_59))=k4_relat_1(k7_relat_1(k6_relat_1(A_137), A_59)) | ~v1_relat_1(k6_relat_1(A_137)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_943])).
% 15.41/7.85  tff(c_1444, plain, (![A_163, A_164]: (k5_relat_1(k6_relat_1(A_163), k6_relat_1(A_164))=k4_relat_1(k7_relat_1(k6_relat_1(A_163), A_164)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_972])).
% 15.41/7.85  tff(c_1491, plain, (![A_59, A_164]: (k4_relat_1(k7_relat_1(k6_relat_1(A_59), A_164))=k7_relat_1(k6_relat_1(A_164), A_59) | ~v1_relat_1(k6_relat_1(A_164)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1444])).
% 15.41/7.85  tff(c_1523, plain, (![A_59, A_164]: (k4_relat_1(k7_relat_1(k6_relat_1(A_59), A_164))=k7_relat_1(k6_relat_1(A_164), A_59))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1491])).
% 15.41/7.85  tff(c_30, plain, (![A_52]: (k1_relat_1(k6_relat_1(A_52))=A_52)), inference(cnfTransformation, [status(thm)], [f_84])).
% 15.41/7.85  tff(c_195, plain, (![B_83, A_84]: (k3_xboole_0(k1_relat_1(B_83), A_84)=k1_relat_1(k7_relat_1(B_83, A_84)) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.41/7.85  tff(c_207, plain, (![A_52, A_84]: (k1_relat_1(k7_relat_1(k6_relat_1(A_52), A_84))=k3_xboole_0(A_52, A_84) | ~v1_relat_1(k6_relat_1(A_52)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_195])).
% 15.41/7.85  tff(c_211, plain, (![A_52, A_84]: (k1_relat_1(k7_relat_1(k6_relat_1(A_52), A_84))=k3_xboole_0(A_52, A_84))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_207])).
% 15.41/7.85  tff(c_32, plain, (![A_52]: (k2_relat_1(k6_relat_1(A_52))=A_52)), inference(cnfTransformation, [status(thm)], [f_84])).
% 15.41/7.85  tff(c_38, plain, (![A_56]: (k5_relat_1(A_56, k6_relat_1(k2_relat_1(A_56)))=A_56 | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.41/7.85  tff(c_126, plain, (![A_75, B_76]: (k5_relat_1(k6_relat_1(A_75), B_76)=k7_relat_1(B_76, A_75) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_104])).
% 15.41/7.85  tff(c_153, plain, (![A_75]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_75))), A_75)=k6_relat_1(A_75) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_75)))) | ~v1_relat_1(k6_relat_1(A_75)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_126])).
% 15.41/7.85  tff(c_167, plain, (![A_75]: (k7_relat_1(k6_relat_1(A_75), A_75)=k6_relat_1(A_75))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_32, c_153])).
% 15.41/7.85  tff(c_212, plain, (![A_85, A_86]: (k1_relat_1(k7_relat_1(k6_relat_1(A_85), A_86))=k3_xboole_0(A_85, A_86))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_207])).
% 15.41/7.85  tff(c_224, plain, (![A_75]: (k3_xboole_0(A_75, A_75)=k1_relat_1(k6_relat_1(A_75)))), inference(superposition, [status(thm), theory('equality')], [c_167, c_212])).
% 15.41/7.85  tff(c_228, plain, (![A_87]: (k3_xboole_0(A_87, A_87)=A_87)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_224])).
% 15.41/7.85  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.41/7.85  tff(c_238, plain, (![A_87]: (r1_tarski(A_87, A_87))), inference(superposition, [status(thm), theory('equality')], [c_228, c_2])).
% 15.41/7.85  tff(c_323, plain, (![A_96, B_97]: (k5_relat_1(k6_relat_1(A_96), B_97)=B_97 | ~r1_tarski(k1_relat_1(B_97), A_96) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.41/7.85  tff(c_341, plain, (![B_97]: (k5_relat_1(k6_relat_1(k1_relat_1(B_97)), B_97)=B_97 | ~v1_relat_1(B_97))), inference(resolution, [status(thm)], [c_238, c_323])).
% 15.41/7.85  tff(c_24, plain, (![A_39, B_41]: (r1_tarski(k2_relat_1(k5_relat_1(A_39, B_41)), k2_relat_1(B_41)) | ~v1_relat_1(B_41) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.41/7.85  tff(c_6312, plain, (![A_331, B_332]: (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(A_331, B_332))), k2_relat_1(k4_relat_1(A_331))) | ~v1_relat_1(k4_relat_1(A_331)) | ~v1_relat_1(k4_relat_1(B_332)) | ~v1_relat_1(B_332) | ~v1_relat_1(A_331))), inference(superposition, [status(thm), theory('equality')], [c_731, c_24])).
% 15.41/7.85  tff(c_6369, plain, (![B_97]: (r1_tarski(k2_relat_1(k4_relat_1(B_97)), k2_relat_1(k4_relat_1(k6_relat_1(k1_relat_1(B_97))))) | ~v1_relat_1(k4_relat_1(k6_relat_1(k1_relat_1(B_97)))) | ~v1_relat_1(k4_relat_1(B_97)) | ~v1_relat_1(B_97) | ~v1_relat_1(k6_relat_1(k1_relat_1(B_97))) | ~v1_relat_1(B_97))), inference(superposition, [status(thm), theory('equality')], [c_341, c_6312])).
% 15.41/7.85  tff(c_6418, plain, (![B_333]: (r1_tarski(k2_relat_1(k4_relat_1(B_333)), k1_relat_1(B_333)) | ~v1_relat_1(k4_relat_1(B_333)) | ~v1_relat_1(B_333))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_34, c_32, c_34, c_6369])).
% 15.41/7.85  tff(c_6436, plain, (![A_164, A_59]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_164), A_59)), k1_relat_1(k7_relat_1(k6_relat_1(A_59), A_164))) | ~v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_59), A_164))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_59), A_164)))), inference(superposition, [status(thm), theory('equality')], [c_1523, c_6418])).
% 15.41/7.85  tff(c_6463, plain, (![A_334, A_335]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_334), A_335)), k3_xboole_0(A_335, A_334)))), inference(demodulation, [status(thm), theory('equality')], [c_1013, c_1013, c_1523, c_211, c_6436])).
% 15.41/7.85  tff(c_339, plain, (![A_96, A_52]: (k5_relat_1(k6_relat_1(A_96), k6_relat_1(A_52))=k6_relat_1(A_52) | ~r1_tarski(A_52, A_96) | ~v1_relat_1(k6_relat_1(A_52)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_323])).
% 15.41/7.85  tff(c_343, plain, (![A_96, A_52]: (k5_relat_1(k6_relat_1(A_96), k6_relat_1(A_52))=k6_relat_1(A_52) | ~r1_tarski(A_52, A_96))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_339])).
% 15.41/7.85  tff(c_964, plain, (![A_52, A_96]: (k5_relat_1(k6_relat_1(A_52), k6_relat_1(A_96))=k4_relat_1(k6_relat_1(A_52)) | ~r1_tarski(A_52, A_96))), inference(superposition, [status(thm), theory('equality')], [c_343, c_943])).
% 15.41/7.85  tff(c_1030, plain, (![A_142, A_143]: (k5_relat_1(k6_relat_1(A_142), k6_relat_1(A_143))=k6_relat_1(A_142) | ~r1_tarski(A_142, A_143))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_964])).
% 15.41/7.85  tff(c_1060, plain, (![A_143, A_142]: (k7_relat_1(k6_relat_1(A_143), A_142)=k6_relat_1(A_142) | ~v1_relat_1(k6_relat_1(A_143)) | ~r1_tarski(A_142, A_143))), inference(superposition, [status(thm), theory('equality')], [c_1030, c_42])).
% 15.41/7.85  tff(c_1110, plain, (![A_143, A_142]: (k7_relat_1(k6_relat_1(A_143), A_142)=k6_relat_1(A_142) | ~r1_tarski(A_142, A_143))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1060])).
% 15.41/7.85  tff(c_867, plain, (![B_131, C_132, A_133]: (k7_relat_1(k5_relat_1(B_131, C_132), A_133)=k5_relat_1(k7_relat_1(B_131, A_133), C_132) | ~v1_relat_1(C_132) | ~v1_relat_1(B_131))), inference(cnfTransformation, [status(thm)], [f_56])).
% 15.41/7.85  tff(c_909, plain, (![A_59, A_133, B_60]: (k5_relat_1(k7_relat_1(k6_relat_1(A_59), A_133), B_60)=k7_relat_1(k7_relat_1(B_60, A_59), A_133) | ~v1_relat_1(B_60) | ~v1_relat_1(k6_relat_1(A_59)) | ~v1_relat_1(B_60))), inference(superposition, [status(thm), theory('equality')], [c_42, c_867])).
% 15.41/7.85  tff(c_2395, plain, (![A_206, A_207, B_208]: (k5_relat_1(k7_relat_1(k6_relat_1(A_206), A_207), B_208)=k7_relat_1(k7_relat_1(B_208, A_206), A_207) | ~v1_relat_1(B_208))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_909])).
% 15.41/7.85  tff(c_376, plain, (![A_99, B_100]: (r1_tarski(k2_relat_1(k5_relat_1(A_99, B_100)), k2_relat_1(B_100)) | ~v1_relat_1(B_100) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.41/7.85  tff(c_391, plain, (![A_99, A_52]: (r1_tarski(k2_relat_1(k5_relat_1(A_99, k6_relat_1(A_52))), A_52) | ~v1_relat_1(k6_relat_1(A_52)) | ~v1_relat_1(A_99))), inference(superposition, [status(thm), theory('equality')], [c_32, c_376])).
% 15.41/7.85  tff(c_401, plain, (![A_99, A_52]: (r1_tarski(k2_relat_1(k5_relat_1(A_99, k6_relat_1(A_52))), A_52) | ~v1_relat_1(A_99))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_391])).
% 15.41/7.85  tff(c_2424, plain, (![A_52, A_206, A_207]: (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_52), A_206), A_207)), A_52) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_206), A_207)) | ~v1_relat_1(k6_relat_1(A_52)))), inference(superposition, [status(thm), theory('equality')], [c_2395, c_401])).
% 15.41/7.85  tff(c_2541, plain, (![A_215, A_216, A_217]: (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_215), A_216), A_217)), A_215))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1013, c_2424])).
% 15.41/7.85  tff(c_2709, plain, (![A_222, A_223, A_224]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_222), A_223)), A_224) | ~r1_tarski(A_222, A_224))), inference(superposition, [status(thm), theory('equality')], [c_1110, c_2541])).
% 15.41/7.85  tff(c_2736, plain, (![A_142, A_224, A_143]: (r1_tarski(k2_relat_1(k6_relat_1(A_142)), A_224) | ~r1_tarski(A_143, A_224) | ~r1_tarski(A_142, A_143))), inference(superposition, [status(thm), theory('equality')], [c_1110, c_2709])).
% 15.41/7.85  tff(c_2762, plain, (![A_225, A_226, A_227]: (r1_tarski(A_225, A_226) | ~r1_tarski(A_227, A_226) | ~r1_tarski(A_225, A_227))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2736])).
% 15.41/7.85  tff(c_2795, plain, (![A_225, A_1, B_2]: (r1_tarski(A_225, A_1) | ~r1_tarski(A_225, k3_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_2, c_2762])).
% 15.41/7.85  tff(c_6566, plain, (![A_336, A_337]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_336), A_337)), A_337))), inference(resolution, [status(thm)], [c_6463, c_2795])).
% 15.41/7.85  tff(c_496, plain, (![A_113, A_114]: (k5_relat_1(k6_relat_1(A_113), k6_relat_1(A_114))=k6_relat_1(A_114) | ~r1_tarski(A_114, A_113))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_339])).
% 15.41/7.85  tff(c_512, plain, (![A_114, A_113]: (k7_relat_1(k6_relat_1(A_114), A_113)=k6_relat_1(A_114) | ~v1_relat_1(k6_relat_1(A_114)) | ~r1_tarski(A_114, A_113))), inference(superposition, [status(thm), theory('equality')], [c_496, c_42])).
% 15.41/7.85  tff(c_573, plain, (![A_115, A_116]: (k7_relat_1(k6_relat_1(A_115), A_116)=k6_relat_1(A_115) | ~r1_tarski(A_115, A_116))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_512])).
% 15.41/7.85  tff(c_596, plain, (![A_115, A_116]: (k3_xboole_0(A_115, A_116)=k1_relat_1(k6_relat_1(A_115)) | ~r1_tarski(A_115, A_116))), inference(superposition, [status(thm), theory('equality')], [c_573, c_211])).
% 15.41/7.85  tff(c_628, plain, (![A_115, A_116]: (k3_xboole_0(A_115, A_116)=A_115 | ~r1_tarski(A_115, A_116))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_596])).
% 15.41/7.85  tff(c_6635, plain, (![A_336, A_337]: (k3_xboole_0(k2_relat_1(k7_relat_1(k6_relat_1(A_336), A_337)), A_337)=k2_relat_1(k7_relat_1(k6_relat_1(A_336), A_337)))), inference(resolution, [status(thm)], [c_6566, c_628])).
% 15.41/7.85  tff(c_227, plain, (![A_75]: (k3_xboole_0(A_75, A_75)=A_75)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_224])).
% 15.41/7.85  tff(c_988, plain, (![A_137, A_59]: (k5_relat_1(k6_relat_1(A_137), k6_relat_1(A_59))=k4_relat_1(k7_relat_1(k6_relat_1(A_137), A_59)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_972])).
% 15.41/7.85  tff(c_1585, plain, (![A_137, A_59]: (k5_relat_1(k6_relat_1(A_137), k6_relat_1(A_59))=k7_relat_1(k6_relat_1(A_59), A_137))), inference(demodulation, [status(thm), theory('equality')], [c_1523, c_988])).
% 15.41/7.85  tff(c_1352, plain, (![A_160, B_161, C_162]: (k5_relat_1(k5_relat_1(A_160, B_161), C_162)=k5_relat_1(A_160, k5_relat_1(B_161, C_162)) | ~v1_relat_1(C_162) | ~v1_relat_1(B_161) | ~v1_relat_1(A_160))), inference(cnfTransformation, [status(thm)], [f_80])).
% 15.41/7.85  tff(c_1409, plain, (![A_56, C_162]: (k5_relat_1(A_56, k5_relat_1(k6_relat_1(k2_relat_1(A_56)), C_162))=k5_relat_1(A_56, C_162) | ~v1_relat_1(C_162) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_56))) | ~v1_relat_1(A_56) | ~v1_relat_1(A_56))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1352])).
% 15.41/7.85  tff(c_2940, plain, (![A_234, C_235]: (k5_relat_1(A_234, k5_relat_1(k6_relat_1(k2_relat_1(A_234)), C_235))=k5_relat_1(A_234, C_235) | ~v1_relat_1(C_235) | ~v1_relat_1(A_234))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1409])).
% 15.41/7.85  tff(c_3023, plain, (![A_52, C_235]: (k5_relat_1(k6_relat_1(A_52), k5_relat_1(k6_relat_1(A_52), C_235))=k5_relat_1(k6_relat_1(A_52), C_235) | ~v1_relat_1(C_235) | ~v1_relat_1(k6_relat_1(A_52)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2940])).
% 15.41/7.85  tff(c_19480, plain, (![A_553, C_554]: (k5_relat_1(k6_relat_1(A_553), k5_relat_1(k6_relat_1(A_553), C_554))=k5_relat_1(k6_relat_1(A_553), C_554) | ~v1_relat_1(C_554))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_3023])).
% 15.41/7.85  tff(c_19606, plain, (![A_137, A_59]: (k5_relat_1(k6_relat_1(A_137), k7_relat_1(k6_relat_1(A_59), A_137))=k5_relat_1(k6_relat_1(A_137), k6_relat_1(A_59)) | ~v1_relat_1(k6_relat_1(A_59)))), inference(superposition, [status(thm), theory('equality')], [c_1585, c_19480])).
% 15.41/7.85  tff(c_19873, plain, (![A_559, A_560]: (k5_relat_1(k6_relat_1(A_559), k7_relat_1(k6_relat_1(A_560), A_559))=k7_relat_1(k6_relat_1(A_560), A_559))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1585, c_19606])).
% 15.41/7.85  tff(c_19943, plain, (![A_560, A_559]: (k7_relat_1(k7_relat_1(k6_relat_1(A_560), A_559), A_559)=k7_relat_1(k6_relat_1(A_560), A_559) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_560), A_559)))), inference(superposition, [status(thm), theory('equality')], [c_19873, c_42])).
% 15.41/7.85  tff(c_20140, plain, (![A_563, A_564]: (k7_relat_1(k7_relat_1(k6_relat_1(A_563), A_564), A_564)=k7_relat_1(k6_relat_1(A_563), A_564))), inference(demodulation, [status(thm), theory('equality')], [c_1013, c_19943])).
% 15.41/7.85  tff(c_40, plain, (![B_58, A_57]: (k3_xboole_0(k1_relat_1(B_58), A_57)=k1_relat_1(k7_relat_1(B_58, A_57)) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.41/7.85  tff(c_641, plain, (![A_117, A_118]: (k3_xboole_0(A_117, A_118)=A_117 | ~r1_tarski(A_117, A_118))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_596])).
% 15.41/7.85  tff(c_672, plain, (![A_119, B_120]: (k3_xboole_0(k3_xboole_0(A_119, B_120), A_119)=k3_xboole_0(A_119, B_120))), inference(resolution, [status(thm)], [c_2, c_641])).
% 15.41/7.85  tff(c_693, plain, (![B_58, A_57]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_58, A_57)), k1_relat_1(B_58))=k3_xboole_0(k1_relat_1(B_58), A_57) | ~v1_relat_1(B_58))), inference(superposition, [status(thm), theory('equality')], [c_40, c_672])).
% 15.41/7.85  tff(c_20232, plain, (![A_563, A_564]: (k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_563), A_564)), k1_relat_1(k7_relat_1(k6_relat_1(A_563), A_564)))=k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_563), A_564)), A_564) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_563), A_564)))), inference(superposition, [status(thm), theory('equality')], [c_20140, c_693])).
% 15.41/7.85  tff(c_20334, plain, (![A_563, A_564]: (k3_xboole_0(k3_xboole_0(A_563, A_564), A_564)=k3_xboole_0(A_563, A_564))), inference(demodulation, [status(thm), theory('equality')], [c_1013, c_227, c_211, c_211, c_211, c_20232])).
% 15.41/7.85  tff(c_382, plain, (![B_60, A_59]: (r1_tarski(k2_relat_1(k7_relat_1(B_60, A_59)), k2_relat_1(B_60)) | ~v1_relat_1(B_60) | ~v1_relat_1(k6_relat_1(A_59)) | ~v1_relat_1(B_60))), inference(superposition, [status(thm), theory('equality')], [c_42, c_376])).
% 15.41/7.85  tff(c_402, plain, (![B_101, A_102]: (r1_tarski(k2_relat_1(k7_relat_1(B_101, A_102)), k2_relat_1(B_101)) | ~v1_relat_1(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_382])).
% 15.41/7.85  tff(c_408, plain, (![A_52, A_102]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_52), A_102)), A_52) | ~v1_relat_1(k6_relat_1(A_52)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_402])).
% 15.41/7.85  tff(c_412, plain, (![A_52, A_102]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_52), A_102)), A_52))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_408])).
% 15.41/7.85  tff(c_899, plain, (![A_96, A_133, A_52]: (k5_relat_1(k7_relat_1(k6_relat_1(A_96), A_133), k6_relat_1(A_52))=k7_relat_1(k6_relat_1(A_52), A_133) | ~v1_relat_1(k6_relat_1(A_52)) | ~v1_relat_1(k6_relat_1(A_96)) | ~r1_tarski(A_52, A_96))), inference(superposition, [status(thm), theory('equality')], [c_343, c_867])).
% 15.41/7.85  tff(c_35814, plain, (![A_720, A_721, A_722]: (k5_relat_1(k7_relat_1(k6_relat_1(A_720), A_721), k6_relat_1(A_722))=k7_relat_1(k6_relat_1(A_722), A_721) | ~r1_tarski(A_722, A_720))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_899])).
% 15.41/7.85  tff(c_35905, plain, (![A_720, A_721]: (k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_720), A_721))), A_721)=k7_relat_1(k6_relat_1(A_720), A_721) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_720), A_721)) | ~r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_720), A_721)), A_720))), inference(superposition, [status(thm), theory('equality')], [c_35814, c_38])).
% 15.41/7.85  tff(c_36058, plain, (![A_723, A_724]: (k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_723), A_724))), A_724)=k7_relat_1(k6_relat_1(A_723), A_724))), inference(demodulation, [status(thm), theory('equality')], [c_412, c_1013, c_35905])).
% 15.41/7.85  tff(c_20412, plain, (![A_568, A_569]: (k3_xboole_0(k3_xboole_0(A_568, A_569), A_569)=k3_xboole_0(A_568, A_569))), inference(demodulation, [status(thm), theory('equality')], [c_1013, c_227, c_211, c_211, c_211, c_20232])).
% 15.41/7.85  tff(c_20697, plain, (![B_58, A_57]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_58, A_57)), A_57)=k3_xboole_0(k1_relat_1(B_58), A_57) | ~v1_relat_1(B_58))), inference(superposition, [status(thm), theory('equality')], [c_40, c_20412])).
% 15.41/7.85  tff(c_36161, plain, (![A_723, A_724]: (k3_xboole_0(k1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_723), A_724)))), A_724)=k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_723), A_724)), A_724) | ~v1_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_723), A_724)))))), inference(superposition, [status(thm), theory('equality')], [c_36058, c_20697])).
% 15.41/7.85  tff(c_36489, plain, (![A_723, A_724]: (k2_relat_1(k7_relat_1(k6_relat_1(A_723), A_724))=k3_xboole_0(A_723, A_724))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_6635, c_20334, c_211, c_30, c_36161])).
% 15.41/7.85  tff(c_6549, plain, (![A_334, A_335]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_334), A_335)), A_335))), inference(resolution, [status(thm)], [c_6463, c_2795])).
% 15.41/7.85  tff(c_554, plain, (![A_114, A_113]: (k7_relat_1(k6_relat_1(A_114), A_113)=k6_relat_1(A_114) | ~r1_tarski(A_114, A_113))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_512])).
% 15.41/7.85  tff(c_36447, plain, (![A_723, A_113]: (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_723), A_113)))=k7_relat_1(k6_relat_1(A_723), A_113) | ~r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_723), A_113)), A_113))), inference(superposition, [status(thm), theory('equality')], [c_554, c_36058])).
% 15.41/7.85  tff(c_36590, plain, (![A_723, A_113]: (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(A_723), A_113)))=k7_relat_1(k6_relat_1(A_723), A_113))), inference(demodulation, [status(thm), theory('equality')], [c_6549, c_36447])).
% 15.41/7.85  tff(c_54095, plain, (![A_723, A_113]: (k7_relat_1(k6_relat_1(A_723), A_113)=k6_relat_1(k3_xboole_0(A_723, A_113)))), inference(demodulation, [status(thm), theory('equality')], [c_36489, c_36590])).
% 15.41/7.85  tff(c_44, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 15.41/7.85  tff(c_135, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_44])).
% 15.41/7.85  tff(c_158, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_135])).
% 15.41/7.85  tff(c_54159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54095, c_158])).
% 15.41/7.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.41/7.85  
% 15.41/7.85  Inference rules
% 15.41/7.85  ----------------------
% 15.41/7.85  #Ref     : 0
% 15.41/7.85  #Sup     : 13240
% 15.41/7.85  #Fact    : 0
% 15.41/7.85  #Define  : 0
% 15.41/7.85  #Split   : 2
% 15.41/7.85  #Chain   : 0
% 15.41/7.85  #Close   : 0
% 15.41/7.85  
% 15.41/7.85  Ordering : KBO
% 15.41/7.85  
% 15.41/7.85  Simplification rules
% 15.41/7.85  ----------------------
% 15.41/7.85  #Subsume      : 2369
% 15.41/7.85  #Demod        : 10039
% 15.41/7.85  #Tautology    : 4286
% 15.41/7.85  #SimpNegUnit  : 0
% 15.41/7.85  #BackRed      : 107
% 15.41/7.85  
% 15.41/7.85  #Partial instantiations: 0
% 15.41/7.85  #Strategies tried      : 1
% 15.41/7.85  
% 15.41/7.85  Timing (in seconds)
% 15.41/7.85  ----------------------
% 15.41/7.85  Preprocessing        : 0.34
% 15.41/7.85  Parsing              : 0.18
% 15.41/7.85  CNF conversion       : 0.02
% 15.41/7.85  Main loop            : 6.73
% 15.41/7.85  Inferencing          : 1.29
% 15.41/7.85  Reduction            : 2.75
% 15.41/7.85  Demodulation         : 2.34
% 15.41/7.85  BG Simplification    : 0.17
% 15.41/7.85  Subsumption          : 2.12
% 15.41/7.85  Abstraction          : 0.27
% 15.41/7.85  MUC search           : 0.00
% 15.41/7.85  Cooper               : 0.00
% 15.41/7.85  Total                : 7.12
% 15.41/7.85  Index Insertion      : 0.00
% 15.41/7.85  Index Deletion       : 0.00
% 15.41/7.85  Index Matching       : 0.00
% 15.41/7.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
