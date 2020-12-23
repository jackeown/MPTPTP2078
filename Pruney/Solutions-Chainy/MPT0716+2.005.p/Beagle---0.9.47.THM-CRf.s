%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:37 EST 2020

% Result     : Theorem 16.27s
% Output     : CNFRefutation 16.36s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 331 expanded)
%              Number of leaves         :   24 ( 121 expanded)
%              Depth                    :   23
%              Number of atoms          :  233 ( 900 expanded)
%              Number of equality atoms :   22 (  85 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_94,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

tff(c_34,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_366,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_437,plain,(
    ! [A_70,B_71] :
      ( k10_relat_1(A_70,k1_relat_1(B_71)) = k1_relat_1(k5_relat_1(A_70,B_71))
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k10_relat_1(B_14,A_13),k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_907,plain,(
    ! [A_102,B_103] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_102,B_103)),k1_relat_1(A_102))
      | ~ v1_relat_1(A_102)
      | ~ v1_relat_1(B_103)
      | ~ v1_relat_1(A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_14])).

tff(c_40,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_71,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_89,plain,(
    k2_xboole_0('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) = k1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_71,c_10])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_271,plain,(
    ! [C_5] :
      ( r1_tarski('#skF_4',C_5)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),C_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_8])).

tff(c_913,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_907,c_271])).

tff(c_922,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_913])).

tff(c_924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_366,c_922])).

tff(c_926,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,B_29) = B_29
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_47,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_43])).

tff(c_26,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_933,plain,(
    k2_xboole_0('#skF_4',k1_relat_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_926,c_10])).

tff(c_1033,plain,(
    ! [A_108,B_109] :
      ( k10_relat_1(A_108,k1_relat_1(B_109)) = k1_relat_1(k5_relat_1(A_108,B_109))
      | ~ v1_relat_1(B_109)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1989,plain,(
    ! [A_170,B_171] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_170,B_171)),k1_relat_1(A_170))
      | ~ v1_relat_1(A_170)
      | ~ v1_relat_1(B_171)
      | ~ v1_relat_1(A_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1033,c_14])).

tff(c_2006,plain,(
    ! [A_170,B_171] :
      ( k2_xboole_0(k1_relat_1(k5_relat_1(A_170,B_171)),k1_relat_1(A_170)) = k1_relat_1(A_170)
      | ~ v1_relat_1(B_171)
      | ~ v1_relat_1(A_170) ) ),
    inference(resolution,[status(thm)],[c_1989,c_10])).

tff(c_62,plain,(
    ! [A_33,C_34,B_35] :
      ( r1_tarski(A_33,C_34)
      | ~ r1_tarski(k2_xboole_0(A_33,B_35),C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,(
    ! [A_36,B_37] : r1_tarski(A_36,k2_xboole_0(A_36,B_37)) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_90,plain,(
    ! [A_38,B_39,B_40] : r1_tarski(A_38,k2_xboole_0(k2_xboole_0(A_38,B_39),B_40)) ),
    inference(resolution,[status(thm)],[c_72,c_8])).

tff(c_1349,plain,(
    ! [A_134,B_135,B_136] : k2_xboole_0(A_134,k2_xboole_0(k2_xboole_0(A_134,B_135),B_136)) = k2_xboole_0(k2_xboole_0(A_134,B_135),B_136) ),
    inference(resolution,[status(thm)],[c_90,c_10])).

tff(c_1490,plain,(
    ! [B_136] : k2_xboole_0(k2_xboole_0('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))),B_136) = k2_xboole_0('#skF_4',k2_xboole_0(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),B_136)) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_1349])).

tff(c_2794,plain,(
    ! [B_218] : k2_xboole_0('#skF_4',k2_xboole_0(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),B_218)) = k2_xboole_0(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),B_218) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_1490])).

tff(c_2843,plain,
    ( k2_xboole_0(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),k1_relat_1('#skF_1')) = k2_xboole_0('#skF_4',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2006,c_2794])).

tff(c_2867,plain,(
    k2_xboole_0(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),k1_relat_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_933,c_2843])).

tff(c_70,plain,(
    ! [A_33,B_35] : r1_tarski(A_33,k2_xboole_0(A_33,B_35)) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_2936,plain,(
    r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2867,c_70])).

tff(c_16,plain,(
    ! [A_15,B_17] :
      ( k10_relat_1(A_15,k1_relat_1(B_17)) = k1_relat_1(k5_relat_1(A_15,B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k9_relat_1(B_19,k10_relat_1(B_19,A_18)),A_18)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2725,plain,(
    ! [A_210,B_211] :
      ( r1_tarski(k9_relat_1(A_210,k1_relat_1(k5_relat_1(A_210,B_211))),k1_relat_1(B_211))
      | ~ v1_funct_1(A_210)
      | ~ v1_relat_1(A_210)
      | ~ v1_relat_1(B_211)
      | ~ v1_relat_1(A_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1033,c_18])).

tff(c_20,plain,(
    ! [A_20,C_22,B_21] :
      ( r1_tarski(A_20,k10_relat_1(C_22,B_21))
      | ~ r1_tarski(k9_relat_1(C_22,A_20),B_21)
      | ~ r1_tarski(A_20,k1_relat_1(C_22))
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8728,plain,(
    ! [A_397,B_398] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_397,B_398)),k10_relat_1(A_397,k1_relat_1(B_398)))
      | ~ r1_tarski(k1_relat_1(k5_relat_1(A_397,B_398)),k1_relat_1(A_397))
      | ~ v1_funct_1(A_397)
      | ~ v1_relat_1(B_398)
      | ~ v1_relat_1(A_397) ) ),
    inference(resolution,[status(thm)],[c_2725,c_20])).

tff(c_8744,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8728,c_271])).

tff(c_8761,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_26,c_2936,c_8744])).

tff(c_8789,plain,(
    k2_xboole_0('#skF_4',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) = k10_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8761,c_10])).

tff(c_8871,plain,
    ( k2_xboole_0('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) = k10_relat_1('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_8789])).

tff(c_8881,plain,(
    k10_relat_1('#skF_1',k1_relat_1('#skF_2')) = k1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_89,c_8871])).

tff(c_165,plain,(
    ! [B_45,A_46] :
      ( r1_tarski(k9_relat_1(B_45,k10_relat_1(B_45,A_46)),A_46)
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1277,plain,(
    ! [B_129,A_130] :
      ( k2_xboole_0(k9_relat_1(B_129,k10_relat_1(B_129,A_130)),A_130) = A_130
      | ~ v1_funct_1(B_129)
      | ~ v1_relat_1(B_129) ) ),
    inference(resolution,[status(thm)],[c_165,c_10])).

tff(c_83,plain,(
    ! [A_3,B_4,B_37] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_37)) ),
    inference(resolution,[status(thm)],[c_72,c_8])).

tff(c_1295,plain,(
    ! [B_129,A_130,B_37] :
      ( r1_tarski(k9_relat_1(B_129,k10_relat_1(B_129,A_130)),k2_xboole_0(A_130,B_37))
      | ~ v1_funct_1(B_129)
      | ~ v1_relat_1(B_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1277,c_83])).

tff(c_9115,plain,(
    ! [B_37] :
      ( r1_tarski(k9_relat_1('#skF_1',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))),k2_xboole_0(k1_relat_1('#skF_2'),B_37))
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8881,c_1295])).

tff(c_9337,plain,(
    ! [B_407] : r1_tarski(k9_relat_1('#skF_1',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))),k2_xboole_0(k1_relat_1('#skF_2'),B_407)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_9115])).

tff(c_9348,plain,(
    ! [B_407] :
      ( r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),k10_relat_1('#skF_1',k2_xboole_0(k1_relat_1('#skF_2'),B_407)))
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),k1_relat_1('#skF_1'))
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_9337,c_20])).

tff(c_9385,plain,(
    ! [B_408] : r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),k10_relat_1('#skF_1',k2_xboole_0(k1_relat_1('#skF_2'),B_408))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_2936,c_9348])).

tff(c_9431,plain,(
    ! [B_408] : r1_tarski('#skF_4',k10_relat_1('#skF_1',k2_xboole_0(k1_relat_1('#skF_2'),B_408))) ),
    inference(resolution,[status(thm)],[c_9385,c_271])).

tff(c_1258,plain,(
    ! [C_124,A_125,D_126,B_127] :
      ( r1_tarski(k9_relat_1(C_124,A_125),k9_relat_1(D_126,B_127))
      | ~ r1_tarski(A_125,B_127)
      | ~ r1_tarski(C_124,D_126)
      | ~ v1_relat_1(D_126)
      | ~ v1_relat_1(C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3080,plain,(
    ! [C_223,A_224,D_225,B_226] :
      ( k2_xboole_0(k9_relat_1(C_223,A_224),k9_relat_1(D_225,B_226)) = k9_relat_1(D_225,B_226)
      | ~ r1_tarski(A_224,B_226)
      | ~ r1_tarski(C_223,D_225)
      | ~ v1_relat_1(D_225)
      | ~ v1_relat_1(C_223) ) ),
    inference(resolution,[status(thm)],[c_1258,c_10])).

tff(c_7479,plain,(
    ! [C_357,C_361,B_358,D_359,A_360] :
      ( r1_tarski(k9_relat_1(C_357,A_360),C_361)
      | ~ r1_tarski(k9_relat_1(D_359,B_358),C_361)
      | ~ r1_tarski(A_360,B_358)
      | ~ r1_tarski(C_357,D_359)
      | ~ v1_relat_1(D_359)
      | ~ v1_relat_1(C_357) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3080,c_8])).

tff(c_26033,plain,(
    ! [C_709,A_710,A_711,B_712] :
      ( r1_tarski(k9_relat_1(C_709,A_710),A_711)
      | ~ r1_tarski(A_710,k10_relat_1(B_712,A_711))
      | ~ r1_tarski(C_709,B_712)
      | ~ v1_relat_1(C_709)
      | ~ v1_funct_1(B_712)
      | ~ v1_relat_1(B_712) ) ),
    inference(resolution,[status(thm)],[c_18,c_7479])).

tff(c_26089,plain,(
    ! [C_709,B_408] :
      ( r1_tarski(k9_relat_1(C_709,'#skF_4'),k2_xboole_0(k1_relat_1('#skF_2'),B_408))
      | ~ r1_tarski(C_709,'#skF_1')
      | ~ v1_relat_1(C_709)
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_9431,c_26033])).

tff(c_36650,plain,(
    ! [C_867,B_868] :
      ( r1_tarski(k9_relat_1(C_867,'#skF_4'),k2_xboole_0(k1_relat_1('#skF_2'),B_868))
      | ~ r1_tarski(C_867,'#skF_1')
      | ~ v1_relat_1(C_867) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_26089])).

tff(c_36705,plain,(
    ! [C_869] :
      ( r1_tarski(k9_relat_1(C_869,'#skF_4'),k1_relat_1('#skF_2'))
      | ~ r1_tarski(C_869,'#skF_1')
      | ~ v1_relat_1(C_869) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_36650])).

tff(c_925,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_959,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_925])).

tff(c_36731,plain,
    ( ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_36705,c_959])).

tff(c_36758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6,c_36731])).

tff(c_36760,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_925])).

tff(c_30,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36819,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_926,c_36760,c_30])).

tff(c_36759,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_925])).

tff(c_32,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36908,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_926,c_36760,c_32])).

tff(c_37107,plain,(
    ! [A_889,C_890,B_891] :
      ( r1_tarski(A_889,k10_relat_1(C_890,B_891))
      | ~ r1_tarski(k9_relat_1(C_890,A_889),B_891)
      | ~ r1_tarski(A_889,k1_relat_1(C_890))
      | ~ v1_funct_1(C_890)
      | ~ v1_relat_1(C_890) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_37125,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_36908,c_37107])).

tff(c_37163,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_36759,c_37125])).

tff(c_37180,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_37163])).

tff(c_37184,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_37180])).

tff(c_37186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36819,c_37184])).

tff(c_37188,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_36,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_37207,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_37187,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_37292,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_37188,c_38])).

tff(c_38511,plain,(
    ! [A_978,C_979,B_980] :
      ( r1_tarski(A_978,k10_relat_1(C_979,B_980))
      | ~ r1_tarski(k9_relat_1(C_979,A_978),B_980)
      | ~ r1_tarski(A_978,k1_relat_1(C_979))
      | ~ v1_funct_1(C_979)
      | ~ v1_relat_1(C_979) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38540,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_37292,c_38511])).

tff(c_38572,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_37187,c_38540])).

tff(c_38583,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_38572])).

tff(c_38587,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_38583])).

tff(c_38589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37207,c_38587])).

tff(c_38590,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37188,c_38590])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:43:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.27/7.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.27/7.86  
% 16.27/7.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.27/7.86  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 16.27/7.86  
% 16.27/7.86  %Foreground sorts:
% 16.27/7.86  
% 16.27/7.86  
% 16.27/7.86  %Background operators:
% 16.27/7.86  
% 16.27/7.86  
% 16.27/7.86  %Foreground operators:
% 16.27/7.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.27/7.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.27/7.86  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 16.27/7.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.27/7.86  tff('#skF_2', type, '#skF_2': $i).
% 16.27/7.86  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 16.27/7.86  tff('#skF_3', type, '#skF_3': $i).
% 16.27/7.86  tff('#skF_1', type, '#skF_1': $i).
% 16.27/7.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.27/7.86  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 16.27/7.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.27/7.86  tff('#skF_4', type, '#skF_4': $i).
% 16.27/7.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.27/7.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.27/7.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.27/7.86  
% 16.36/7.88  tff(f_94, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 16.36/7.88  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 16.36/7.88  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 16.36/7.88  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 16.36/7.88  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 16.36/7.88  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.36/7.88  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 16.36/7.88  tff(f_77, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 16.36/7.88  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 16.36/7.88  tff(c_34, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.36/7.88  tff(c_366, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_34])).
% 16.36/7.88  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.36/7.88  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.36/7.88  tff(c_437, plain, (![A_70, B_71]: (k10_relat_1(A_70, k1_relat_1(B_71))=k1_relat_1(k5_relat_1(A_70, B_71)) | ~v1_relat_1(B_71) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.36/7.88  tff(c_14, plain, (![B_14, A_13]: (r1_tarski(k10_relat_1(B_14, A_13), k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.36/7.88  tff(c_907, plain, (![A_102, B_103]: (r1_tarski(k1_relat_1(k5_relat_1(A_102, B_103)), k1_relat_1(A_102)) | ~v1_relat_1(A_102) | ~v1_relat_1(B_103) | ~v1_relat_1(A_102))), inference(superposition, [status(thm), theory('equality')], [c_437, c_14])).
% 16.36/7.88  tff(c_40, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.36/7.88  tff(c_71, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_40])).
% 16.36/7.88  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.36/7.88  tff(c_89, plain, (k2_xboole_0('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))=k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_71, c_10])).
% 16.36/7.88  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.36/7.88  tff(c_271, plain, (![C_5]: (r1_tarski('#skF_4', C_5) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), C_5))), inference(superposition, [status(thm), theory('equality')], [c_89, c_8])).
% 16.36/7.88  tff(c_913, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_907, c_271])).
% 16.36/7.88  tff(c_922, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_913])).
% 16.36/7.88  tff(c_924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_366, c_922])).
% 16.36/7.88  tff(c_926, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_34])).
% 16.36/7.88  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.36/7.88  tff(c_43, plain, (![A_28, B_29]: (k2_xboole_0(A_28, B_29)=B_29 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.36/7.88  tff(c_47, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_43])).
% 16.36/7.88  tff(c_26, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.36/7.88  tff(c_933, plain, (k2_xboole_0('#skF_4', k1_relat_1('#skF_1'))=k1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_926, c_10])).
% 16.36/7.88  tff(c_1033, plain, (![A_108, B_109]: (k10_relat_1(A_108, k1_relat_1(B_109))=k1_relat_1(k5_relat_1(A_108, B_109)) | ~v1_relat_1(B_109) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.36/7.88  tff(c_1989, plain, (![A_170, B_171]: (r1_tarski(k1_relat_1(k5_relat_1(A_170, B_171)), k1_relat_1(A_170)) | ~v1_relat_1(A_170) | ~v1_relat_1(B_171) | ~v1_relat_1(A_170))), inference(superposition, [status(thm), theory('equality')], [c_1033, c_14])).
% 16.36/7.88  tff(c_2006, plain, (![A_170, B_171]: (k2_xboole_0(k1_relat_1(k5_relat_1(A_170, B_171)), k1_relat_1(A_170))=k1_relat_1(A_170) | ~v1_relat_1(B_171) | ~v1_relat_1(A_170))), inference(resolution, [status(thm)], [c_1989, c_10])).
% 16.36/7.88  tff(c_62, plain, (![A_33, C_34, B_35]: (r1_tarski(A_33, C_34) | ~r1_tarski(k2_xboole_0(A_33, B_35), C_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.36/7.88  tff(c_72, plain, (![A_36, B_37]: (r1_tarski(A_36, k2_xboole_0(A_36, B_37)))), inference(resolution, [status(thm)], [c_6, c_62])).
% 16.36/7.88  tff(c_90, plain, (![A_38, B_39, B_40]: (r1_tarski(A_38, k2_xboole_0(k2_xboole_0(A_38, B_39), B_40)))), inference(resolution, [status(thm)], [c_72, c_8])).
% 16.36/7.88  tff(c_1349, plain, (![A_134, B_135, B_136]: (k2_xboole_0(A_134, k2_xboole_0(k2_xboole_0(A_134, B_135), B_136))=k2_xboole_0(k2_xboole_0(A_134, B_135), B_136))), inference(resolution, [status(thm)], [c_90, c_10])).
% 16.36/7.88  tff(c_1490, plain, (![B_136]: (k2_xboole_0(k2_xboole_0('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), B_136)=k2_xboole_0('#skF_4', k2_xboole_0(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), B_136)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_1349])).
% 16.36/7.88  tff(c_2794, plain, (![B_218]: (k2_xboole_0('#skF_4', k2_xboole_0(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), B_218))=k2_xboole_0(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), B_218))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_1490])).
% 16.36/7.88  tff(c_2843, plain, (k2_xboole_0(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))=k2_xboole_0('#skF_4', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2006, c_2794])).
% 16.36/7.88  tff(c_2867, plain, (k2_xboole_0(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_933, c_2843])).
% 16.36/7.88  tff(c_70, plain, (![A_33, B_35]: (r1_tarski(A_33, k2_xboole_0(A_33, B_35)))), inference(resolution, [status(thm)], [c_6, c_62])).
% 16.36/7.88  tff(c_2936, plain, (r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2867, c_70])).
% 16.36/7.88  tff(c_16, plain, (![A_15, B_17]: (k10_relat_1(A_15, k1_relat_1(B_17))=k1_relat_1(k5_relat_1(A_15, B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.36/7.88  tff(c_18, plain, (![B_19, A_18]: (r1_tarski(k9_relat_1(B_19, k10_relat_1(B_19, A_18)), A_18) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.36/7.88  tff(c_2725, plain, (![A_210, B_211]: (r1_tarski(k9_relat_1(A_210, k1_relat_1(k5_relat_1(A_210, B_211))), k1_relat_1(B_211)) | ~v1_funct_1(A_210) | ~v1_relat_1(A_210) | ~v1_relat_1(B_211) | ~v1_relat_1(A_210))), inference(superposition, [status(thm), theory('equality')], [c_1033, c_18])).
% 16.36/7.88  tff(c_20, plain, (![A_20, C_22, B_21]: (r1_tarski(A_20, k10_relat_1(C_22, B_21)) | ~r1_tarski(k9_relat_1(C_22, A_20), B_21) | ~r1_tarski(A_20, k1_relat_1(C_22)) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 16.36/7.88  tff(c_8728, plain, (![A_397, B_398]: (r1_tarski(k1_relat_1(k5_relat_1(A_397, B_398)), k10_relat_1(A_397, k1_relat_1(B_398))) | ~r1_tarski(k1_relat_1(k5_relat_1(A_397, B_398)), k1_relat_1(A_397)) | ~v1_funct_1(A_397) | ~v1_relat_1(B_398) | ~v1_relat_1(A_397))), inference(resolution, [status(thm)], [c_2725, c_20])).
% 16.36/7.88  tff(c_8744, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8728, c_271])).
% 16.36/7.88  tff(c_8761, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_26, c_2936, c_8744])).
% 16.36/7.88  tff(c_8789, plain, (k2_xboole_0('#skF_4', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))=k10_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_8761, c_10])).
% 16.36/7.88  tff(c_8871, plain, (k2_xboole_0('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))=k10_relat_1('#skF_1', k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_8789])).
% 16.36/7.88  tff(c_8881, plain, (k10_relat_1('#skF_1', k1_relat_1('#skF_2'))=k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_89, c_8871])).
% 16.36/7.88  tff(c_165, plain, (![B_45, A_46]: (r1_tarski(k9_relat_1(B_45, k10_relat_1(B_45, A_46)), A_46) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.36/7.88  tff(c_1277, plain, (![B_129, A_130]: (k2_xboole_0(k9_relat_1(B_129, k10_relat_1(B_129, A_130)), A_130)=A_130 | ~v1_funct_1(B_129) | ~v1_relat_1(B_129))), inference(resolution, [status(thm)], [c_165, c_10])).
% 16.36/7.88  tff(c_83, plain, (![A_3, B_4, B_37]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_37)))), inference(resolution, [status(thm)], [c_72, c_8])).
% 16.36/7.88  tff(c_1295, plain, (![B_129, A_130, B_37]: (r1_tarski(k9_relat_1(B_129, k10_relat_1(B_129, A_130)), k2_xboole_0(A_130, B_37)) | ~v1_funct_1(B_129) | ~v1_relat_1(B_129))), inference(superposition, [status(thm), theory('equality')], [c_1277, c_83])).
% 16.36/7.88  tff(c_9115, plain, (![B_37]: (r1_tarski(k9_relat_1('#skF_1', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), k2_xboole_0(k1_relat_1('#skF_2'), B_37)) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_8881, c_1295])).
% 16.36/7.88  tff(c_9337, plain, (![B_407]: (r1_tarski(k9_relat_1('#skF_1', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), k2_xboole_0(k1_relat_1('#skF_2'), B_407)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_9115])).
% 16.36/7.88  tff(c_9348, plain, (![B_407]: (r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), k10_relat_1('#skF_1', k2_xboole_0(k1_relat_1('#skF_2'), B_407))) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_9337, c_20])).
% 16.36/7.88  tff(c_9385, plain, (![B_408]: (r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), k10_relat_1('#skF_1', k2_xboole_0(k1_relat_1('#skF_2'), B_408))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_2936, c_9348])).
% 16.36/7.88  tff(c_9431, plain, (![B_408]: (r1_tarski('#skF_4', k10_relat_1('#skF_1', k2_xboole_0(k1_relat_1('#skF_2'), B_408))))), inference(resolution, [status(thm)], [c_9385, c_271])).
% 16.36/7.88  tff(c_1258, plain, (![C_124, A_125, D_126, B_127]: (r1_tarski(k9_relat_1(C_124, A_125), k9_relat_1(D_126, B_127)) | ~r1_tarski(A_125, B_127) | ~r1_tarski(C_124, D_126) | ~v1_relat_1(D_126) | ~v1_relat_1(C_124))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.36/7.88  tff(c_3080, plain, (![C_223, A_224, D_225, B_226]: (k2_xboole_0(k9_relat_1(C_223, A_224), k9_relat_1(D_225, B_226))=k9_relat_1(D_225, B_226) | ~r1_tarski(A_224, B_226) | ~r1_tarski(C_223, D_225) | ~v1_relat_1(D_225) | ~v1_relat_1(C_223))), inference(resolution, [status(thm)], [c_1258, c_10])).
% 16.36/7.88  tff(c_7479, plain, (![C_357, C_361, B_358, D_359, A_360]: (r1_tarski(k9_relat_1(C_357, A_360), C_361) | ~r1_tarski(k9_relat_1(D_359, B_358), C_361) | ~r1_tarski(A_360, B_358) | ~r1_tarski(C_357, D_359) | ~v1_relat_1(D_359) | ~v1_relat_1(C_357))), inference(superposition, [status(thm), theory('equality')], [c_3080, c_8])).
% 16.36/7.88  tff(c_26033, plain, (![C_709, A_710, A_711, B_712]: (r1_tarski(k9_relat_1(C_709, A_710), A_711) | ~r1_tarski(A_710, k10_relat_1(B_712, A_711)) | ~r1_tarski(C_709, B_712) | ~v1_relat_1(C_709) | ~v1_funct_1(B_712) | ~v1_relat_1(B_712))), inference(resolution, [status(thm)], [c_18, c_7479])).
% 16.36/7.88  tff(c_26089, plain, (![C_709, B_408]: (r1_tarski(k9_relat_1(C_709, '#skF_4'), k2_xboole_0(k1_relat_1('#skF_2'), B_408)) | ~r1_tarski(C_709, '#skF_1') | ~v1_relat_1(C_709) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_9431, c_26033])).
% 16.36/7.88  tff(c_36650, plain, (![C_867, B_868]: (r1_tarski(k9_relat_1(C_867, '#skF_4'), k2_xboole_0(k1_relat_1('#skF_2'), B_868)) | ~r1_tarski(C_867, '#skF_1') | ~v1_relat_1(C_867))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_26089])).
% 16.36/7.88  tff(c_36705, plain, (![C_869]: (r1_tarski(k9_relat_1(C_869, '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski(C_869, '#skF_1') | ~v1_relat_1(C_869))), inference(superposition, [status(thm), theory('equality')], [c_47, c_36650])).
% 16.36/7.88  tff(c_925, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_34])).
% 16.36/7.88  tff(c_959, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_925])).
% 16.36/7.88  tff(c_36731, plain, (~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_36705, c_959])).
% 16.36/7.88  tff(c_36758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_6, c_36731])).
% 16.36/7.88  tff(c_36760, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_925])).
% 16.36/7.88  tff(c_30, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.36/7.88  tff(c_36819, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_926, c_36760, c_30])).
% 16.36/7.88  tff(c_36759, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_925])).
% 16.36/7.88  tff(c_32, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.36/7.88  tff(c_36908, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_926, c_36760, c_32])).
% 16.36/7.88  tff(c_37107, plain, (![A_889, C_890, B_891]: (r1_tarski(A_889, k10_relat_1(C_890, B_891)) | ~r1_tarski(k9_relat_1(C_890, A_889), B_891) | ~r1_tarski(A_889, k1_relat_1(C_890)) | ~v1_funct_1(C_890) | ~v1_relat_1(C_890))), inference(cnfTransformation, [status(thm)], [f_77])).
% 16.36/7.88  tff(c_37125, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_36908, c_37107])).
% 16.36/7.88  tff(c_37163, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_36759, c_37125])).
% 16.36/7.88  tff(c_37180, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_37163])).
% 16.36/7.88  tff(c_37184, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_37180])).
% 16.36/7.88  tff(c_37186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36819, c_37184])).
% 16.36/7.88  tff(c_37188, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_40])).
% 16.36/7.88  tff(c_36, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.36/7.88  tff(c_37207, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_36])).
% 16.36/7.88  tff(c_37187, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_40])).
% 16.36/7.88  tff(c_38, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.36/7.88  tff(c_37292, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_37188, c_38])).
% 16.36/7.88  tff(c_38511, plain, (![A_978, C_979, B_980]: (r1_tarski(A_978, k10_relat_1(C_979, B_980)) | ~r1_tarski(k9_relat_1(C_979, A_978), B_980) | ~r1_tarski(A_978, k1_relat_1(C_979)) | ~v1_funct_1(C_979) | ~v1_relat_1(C_979))), inference(cnfTransformation, [status(thm)], [f_77])).
% 16.36/7.88  tff(c_38540, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_37292, c_38511])).
% 16.36/7.88  tff(c_38572, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_37187, c_38540])).
% 16.36/7.88  tff(c_38583, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_38572])).
% 16.36/7.88  tff(c_38587, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_38583])).
% 16.36/7.88  tff(c_38589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37207, c_38587])).
% 16.36/7.88  tff(c_38590, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_36])).
% 16.36/7.88  tff(c_38601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37188, c_38590])).
% 16.36/7.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.36/7.88  
% 16.36/7.88  Inference rules
% 16.36/7.88  ----------------------
% 16.36/7.88  #Ref     : 0
% 16.36/7.88  #Sup     : 9399
% 16.36/7.88  #Fact    : 0
% 16.36/7.88  #Define  : 0
% 16.36/7.88  #Split   : 24
% 16.36/7.88  #Chain   : 0
% 16.36/7.88  #Close   : 0
% 16.36/7.88  
% 16.36/7.88  Ordering : KBO
% 16.36/7.88  
% 16.36/7.88  Simplification rules
% 16.36/7.88  ----------------------
% 16.36/7.88  #Subsume      : 2251
% 16.36/7.88  #Demod        : 4849
% 16.36/7.88  #Tautology    : 2186
% 16.36/7.88  #SimpNegUnit  : 22
% 16.36/7.88  #BackRed      : 8
% 16.36/7.88  
% 16.36/7.88  #Partial instantiations: 0
% 16.36/7.88  #Strategies tried      : 1
% 16.36/7.88  
% 16.36/7.88  Timing (in seconds)
% 16.36/7.88  ----------------------
% 16.36/7.88  Preprocessing        : 0.31
% 16.36/7.88  Parsing              : 0.17
% 16.36/7.88  CNF conversion       : 0.02
% 16.36/7.88  Main loop            : 6.79
% 16.36/7.88  Inferencing          : 1.25
% 16.36/7.88  Reduction            : 2.77
% 16.36/7.88  Demodulation         : 2.28
% 16.36/7.88  BG Simplification    : 0.15
% 16.36/7.88  Subsumption          : 2.17
% 16.36/7.88  Abstraction          : 0.22
% 16.36/7.88  MUC search           : 0.00
% 16.36/7.88  Cooper               : 0.00
% 16.36/7.88  Total                : 7.14
% 16.36/7.88  Index Insertion      : 0.00
% 16.36/7.88  Index Deletion       : 0.00
% 16.36/7.88  Index Matching       : 0.00
% 16.36/7.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
