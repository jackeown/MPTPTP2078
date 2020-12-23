%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:28 EST 2020

% Result     : Theorem 43.94s
% Output     : CNFRefutation 43.94s
% Verified   : 
% Statistics : Number of formulae       :  136 (10184 expanded)
%              Number of leaves         :   23 (3541 expanded)
%              Depth                    :   36
%              Number of atoms          :  612 (39940 expanded)
%              Number of equality atoms :   62 (3959 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_20,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10,plain,(
    ! [A_7] :
      ( v1_relat_1(k2_funct_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_41,plain,(
    ! [A_19,C_20,B_21] :
      ( r1_tarski(A_19,C_20)
      | ~ r1_tarski(B_21,C_20)
      | ~ r1_tarski(A_19,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ! [A_19] :
      ( r1_tarski(A_19,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_19,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_41])).

tff(c_6,plain,(
    ! [A_6] :
      ( k10_relat_1(A_6,k2_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_91,plain,(
    ! [B_30,A_31] :
      ( k9_relat_1(k2_funct_1(B_30),A_31) = k10_relat_1(B_30,A_31)
      | ~ v2_funct_1(B_30)
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k9_relat_1(B_5,A_4),k2_relat_1(B_5))
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_165,plain,(
    ! [B_41,A_42] :
      ( r1_tarski(k10_relat_1(B_41,A_42),k2_relat_1(k2_funct_1(B_41)))
      | ~ v1_relat_1(k2_funct_1(B_41))
      | ~ v2_funct_1(B_41)
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_4])).

tff(c_177,plain,(
    ! [A_6] :
      ( r1_tarski(k1_relat_1(A_6),k2_relat_1(k2_funct_1(A_6)))
      | ~ v1_relat_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_165])).

tff(c_181,plain,(
    ! [A_43] :
      ( r1_tarski(k1_relat_1(A_43),k2_relat_1(k2_funct_1(A_43)))
      | ~ v1_relat_1(k2_funct_1(A_43))
      | ~ v2_funct_1(A_43)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_165])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_194,plain,(
    ! [A_44,A_45] :
      ( r1_tarski(A_44,k2_relat_1(k2_funct_1(A_45)))
      | ~ r1_tarski(A_44,k1_relat_1(A_45))
      | ~ v1_relat_1(k2_funct_1(A_45))
      | ~ v2_funct_1(A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_181,c_2])).

tff(c_414,plain,(
    ! [A_70,A_71,A_72] :
      ( r1_tarski(A_70,k2_relat_1(k2_funct_1(A_71)))
      | ~ r1_tarski(A_70,A_72)
      | ~ r1_tarski(A_72,k1_relat_1(A_71))
      | ~ v1_relat_1(k2_funct_1(A_71))
      | ~ v2_funct_1(A_71)
      | ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(resolution,[status(thm)],[c_194,c_2])).

tff(c_2868,plain,(
    ! [A_153,A_154] :
      ( r1_tarski(k1_relat_1(A_153),k2_relat_1(k2_funct_1(A_154)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_153)),k1_relat_1(A_154))
      | ~ v1_relat_1(k2_funct_1(A_154))
      | ~ v2_funct_1(A_154)
      | ~ v1_funct_1(A_154)
      | ~ v1_relat_1(A_154)
      | ~ v1_relat_1(k2_funct_1(A_153))
      | ~ v2_funct_1(A_153)
      | ~ v1_funct_1(A_153)
      | ~ v1_relat_1(A_153) ) ),
    inference(resolution,[status(thm)],[c_177,c_414])).

tff(c_2881,plain,(
    ! [A_153] :
      ( r1_tarski(k1_relat_1(A_153),k2_relat_1(k2_funct_1('#skF_2')))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(k2_funct_1(A_153))
      | ~ v2_funct_1(A_153)
      | ~ v1_funct_1(A_153)
      | ~ v1_relat_1(A_153)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_153)),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_47,c_2868])).

tff(c_2884,plain,(
    ! [A_153] :
      ( r1_tarski(k1_relat_1(A_153),k2_relat_1(k2_funct_1('#skF_2')))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1(A_153))
      | ~ v2_funct_1(A_153)
      | ~ v1_funct_1(A_153)
      | ~ v1_relat_1(A_153)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_153)),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_2881])).

tff(c_2885,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2884])).

tff(c_2888,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_2885])).

tff(c_2892,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_2888])).

tff(c_2894,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2884])).

tff(c_8,plain,(
    ! [A_7] :
      ( v1_funct_1(k2_funct_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2917,plain,(
    ! [A_157] :
      ( r1_tarski(k1_relat_1(A_157),k2_relat_1(k2_funct_1('#skF_2')))
      | ~ v1_relat_1(k2_funct_1(A_157))
      | ~ v2_funct_1(A_157)
      | ~ v1_funct_1(A_157)
      | ~ v1_relat_1(A_157)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_157)),'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_2884])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k9_relat_1(B_9,k10_relat_1(B_9,A_8)) = A_8
      | ~ r1_tarski(A_8,k2_relat_1(B_9))
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2921,plain,(
    ! [A_157] :
      ( k9_relat_1(k2_funct_1('#skF_2'),k10_relat_1(k2_funct_1('#skF_2'),k1_relat_1(A_157))) = k1_relat_1(A_157)
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1(A_157))
      | ~ v2_funct_1(A_157)
      | ~ v1_funct_1(A_157)
      | ~ v1_relat_1(A_157)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_157)),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2917,c_12])).

tff(c_2935,plain,(
    ! [A_157] :
      ( k9_relat_1(k2_funct_1('#skF_2'),k10_relat_1(k2_funct_1('#skF_2'),k1_relat_1(A_157))) = k1_relat_1(A_157)
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1(A_157))
      | ~ v2_funct_1(A_157)
      | ~ v1_funct_1(A_157)
      | ~ v1_relat_1(A_157)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_157)),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2894,c_2921])).

tff(c_2973,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2935])).

tff(c_2976,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_2973])).

tff(c_2980,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_2976])).

tff(c_2982,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2935])).

tff(c_16,plain,(
    ! [A_12] :
      ( v2_funct_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3144,plain,(
    ! [A_162] :
      ( k9_relat_1(k2_funct_1('#skF_2'),k10_relat_1(k2_funct_1('#skF_2'),k1_relat_1(A_162))) = k1_relat_1(A_162)
      | ~ v1_relat_1(k2_funct_1(A_162))
      | ~ v2_funct_1(A_162)
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_162)),'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_2935])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( k9_relat_1(k2_funct_1(B_11),A_10) = k10_relat_1(B_11,A_10)
      | ~ v2_funct_1(B_11)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3219,plain,(
    ! [A_162] :
      ( k10_relat_1('#skF_2',k10_relat_1(k2_funct_1('#skF_2'),k1_relat_1(A_162))) = k1_relat_1(A_162)
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(k2_funct_1(A_162))
      | ~ v2_funct_1(A_162)
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_162)),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3144,c_14])).

tff(c_3346,plain,(
    ! [A_163] :
      ( k10_relat_1('#skF_2',k10_relat_1(k2_funct_1('#skF_2'),k1_relat_1(A_163))) = k1_relat_1(A_163)
      | ~ v1_relat_1(k2_funct_1(A_163))
      | ~ v2_funct_1(A_163)
      | ~ v1_funct_1(A_163)
      | ~ v1_relat_1(A_163)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_163)),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_3219])).

tff(c_18,plain,(
    ! [A_13] :
      ( k2_funct_1(k2_funct_1(A_13)) = A_13
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_924,plain,(
    ! [A_98,A_99] :
      ( r1_tarski(k10_relat_1(k2_funct_1(A_98),A_99),k2_relat_1(A_98))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(A_98)))
      | ~ v2_funct_1(k2_funct_1(A_98))
      | ~ v1_funct_1(k2_funct_1(A_98))
      | ~ v1_relat_1(k2_funct_1(A_98))
      | ~ v2_funct_1(A_98)
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_165])).

tff(c_948,plain,(
    ! [A_98,A_99] :
      ( k9_relat_1(A_98,k10_relat_1(A_98,k10_relat_1(k2_funct_1(A_98),A_99))) = k10_relat_1(k2_funct_1(A_98),A_99)
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(A_98)))
      | ~ v2_funct_1(k2_funct_1(A_98))
      | ~ v1_funct_1(k2_funct_1(A_98))
      | ~ v1_relat_1(k2_funct_1(A_98))
      | ~ v2_funct_1(A_98)
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(resolution,[status(thm)],[c_924,c_12])).

tff(c_3352,plain,(
    ! [A_163] :
      ( k10_relat_1(k2_funct_1('#skF_2'),k1_relat_1(A_163)) = k9_relat_1('#skF_2',k1_relat_1(A_163))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
      | ~ v2_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(k2_funct_1(A_163))
      | ~ v2_funct_1(A_163)
      | ~ v1_funct_1(A_163)
      | ~ v1_relat_1(A_163)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_163)),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3346,c_948])).

tff(c_3406,plain,(
    ! [A_163] :
      ( k10_relat_1(k2_funct_1('#skF_2'),k1_relat_1(A_163)) = k9_relat_1('#skF_2',k1_relat_1(A_163))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
      | ~ v2_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1(A_163))
      | ~ v2_funct_1(A_163)
      | ~ v1_funct_1(A_163)
      | ~ v1_relat_1(A_163)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_163)),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_2894,c_2982,c_3352])).

tff(c_5514,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3406])).

tff(c_5520,plain,
    ( ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_5514])).

tff(c_5524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_5520])).

tff(c_5526,plain,(
    v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3406])).

tff(c_5525,plain,(
    ! [A_163] :
      ( ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
      | k10_relat_1(k2_funct_1('#skF_2'),k1_relat_1(A_163)) = k9_relat_1('#skF_2',k1_relat_1(A_163))
      | ~ v1_relat_1(k2_funct_1(A_163))
      | ~ v2_funct_1(A_163)
      | ~ v1_funct_1(A_163)
      | ~ v1_relat_1(A_163)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_163)),'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_3406])).

tff(c_5527,plain,(
    ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_5525])).

tff(c_5530,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_5527])).

tff(c_5536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_28,c_5530])).

tff(c_5538,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_5525])).

tff(c_503,plain,(
    ! [A_76] :
      ( k9_relat_1(k2_funct_1(A_76),k10_relat_1(k2_funct_1(A_76),k1_relat_1(A_76))) = k1_relat_1(A_76)
      | ~ v1_funct_1(k2_funct_1(A_76))
      | ~ v1_relat_1(k2_funct_1(A_76))
      | ~ v2_funct_1(A_76)
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(resolution,[status(thm)],[c_181,c_12])).

tff(c_517,plain,(
    ! [A_76] :
      ( k10_relat_1(A_76,k10_relat_1(k2_funct_1(A_76),k1_relat_1(A_76))) = k1_relat_1(A_76)
      | ~ v2_funct_1(A_76)
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76)
      | ~ v1_funct_1(k2_funct_1(A_76))
      | ~ v1_relat_1(k2_funct_1(A_76))
      | ~ v2_funct_1(A_76)
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_14])).

tff(c_100,plain,(
    ! [B_30,A_31] :
      ( r1_tarski(k10_relat_1(B_30,A_31),k2_relat_1(k2_funct_1(B_30)))
      | ~ v1_relat_1(k2_funct_1(B_30))
      | ~ v2_funct_1(B_30)
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_4])).

tff(c_5928,plain,(
    ! [B_211,A_212,A_213] :
      ( r1_tarski(k10_relat_1(B_211,A_212),k2_relat_1(k2_funct_1(A_213)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(B_211)),k1_relat_1(A_213))
      | ~ v1_relat_1(k2_funct_1(A_213))
      | ~ v2_funct_1(A_213)
      | ~ v1_funct_1(A_213)
      | ~ v1_relat_1(A_213)
      | ~ v1_relat_1(k2_funct_1(B_211))
      | ~ v2_funct_1(B_211)
      | ~ v1_funct_1(B_211)
      | ~ v1_relat_1(B_211) ) ),
    inference(resolution,[status(thm)],[c_100,c_414])).

tff(c_5937,plain,(
    ! [B_211,A_212] :
      ( r1_tarski(k10_relat_1(B_211,A_212),k2_relat_1(k2_funct_1('#skF_2')))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(k2_funct_1(B_211))
      | ~ v2_funct_1(B_211)
      | ~ v1_funct_1(B_211)
      | ~ v1_relat_1(B_211)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(B_211)),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_47,c_5928])).

tff(c_5941,plain,(
    ! [B_214,A_215] :
      ( r1_tarski(k10_relat_1(B_214,A_215),k2_relat_1(k2_funct_1('#skF_2')))
      | ~ v1_relat_1(k2_funct_1(B_214))
      | ~ v2_funct_1(B_214)
      | ~ v1_funct_1(B_214)
      | ~ v1_relat_1(B_214)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(B_214)),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_2894,c_5937])).

tff(c_5947,plain,(
    ! [B_214,A_215] :
      ( k9_relat_1(k2_funct_1('#skF_2'),k10_relat_1(k2_funct_1('#skF_2'),k10_relat_1(B_214,A_215))) = k10_relat_1(B_214,A_215)
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1(B_214))
      | ~ v2_funct_1(B_214)
      | ~ v1_funct_1(B_214)
      | ~ v1_relat_1(B_214)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(B_214)),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_5941,c_12])).

tff(c_6251,plain,(
    ! [B_221,A_222] :
      ( k9_relat_1(k2_funct_1('#skF_2'),k10_relat_1(k2_funct_1('#skF_2'),k10_relat_1(B_221,A_222))) = k10_relat_1(B_221,A_222)
      | ~ v1_relat_1(k2_funct_1(B_221))
      | ~ v2_funct_1(B_221)
      | ~ v1_funct_1(B_221)
      | ~ v1_relat_1(B_221)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(B_221)),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2894,c_2982,c_5947])).

tff(c_210,plain,(
    ! [A_49,A_50] :
      ( k10_relat_1(k2_funct_1(A_49),A_50) = k9_relat_1(A_49,A_50)
      | ~ v2_funct_1(k2_funct_1(A_49))
      | ~ v1_funct_1(k2_funct_1(A_49))
      | ~ v1_relat_1(k2_funct_1(A_49))
      | ~ v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_91])).

tff(c_216,plain,(
    ! [A_51,A_52] :
      ( k10_relat_1(k2_funct_1(A_51),A_52) = k9_relat_1(A_51,A_52)
      | ~ v1_funct_1(k2_funct_1(A_51))
      | ~ v1_relat_1(k2_funct_1(A_51))
      | ~ v2_funct_1(A_51)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(resolution,[status(thm)],[c_16,c_210])).

tff(c_222,plain,(
    ! [A_53,A_54] :
      ( k10_relat_1(k2_funct_1(A_53),A_54) = k9_relat_1(A_53,A_54)
      | ~ v1_funct_1(k2_funct_1(A_53))
      | ~ v2_funct_1(A_53)
      | ~ v1_funct_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(resolution,[status(thm)],[c_10,c_216])).

tff(c_227,plain,(
    ! [A_7,A_54] :
      ( k10_relat_1(k2_funct_1(A_7),A_54) = k9_relat_1(A_7,A_54)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_222])).

tff(c_119,plain,(
    ! [B_34,A_35] :
      ( k9_relat_1(B_34,k10_relat_1(B_34,A_35)) = A_35
      | ~ r1_tarski(A_35,k2_relat_1(B_34))
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_123,plain,(
    ! [B_36,A_37] :
      ( k9_relat_1(B_36,k10_relat_1(B_36,k9_relat_1(B_36,A_37))) = k9_relat_1(B_36,A_37)
      | ~ v1_funct_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_4,c_119])).

tff(c_705,plain,(
    ! [B_90,A_91] :
      ( k10_relat_1(B_90,k10_relat_1(k2_funct_1(B_90),k9_relat_1(k2_funct_1(B_90),A_91))) = k9_relat_1(k2_funct_1(B_90),A_91)
      | ~ v1_funct_1(k2_funct_1(B_90))
      | ~ v1_relat_1(k2_funct_1(B_90))
      | ~ v2_funct_1(B_90)
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_123])).

tff(c_756,plain,(
    ! [A_7,A_91] :
      ( k10_relat_1(A_7,k9_relat_1(A_7,k9_relat_1(k2_funct_1(A_7),A_91))) = k9_relat_1(k2_funct_1(A_7),A_91)
      | ~ v1_funct_1(k2_funct_1(A_7))
      | ~ v1_relat_1(k2_funct_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_705])).

tff(c_6271,plain,(
    ! [B_221,A_222] :
      ( k9_relat_1(k2_funct_1('#skF_2'),k10_relat_1(k2_funct_1('#skF_2'),k10_relat_1(B_221,A_222))) = k10_relat_1('#skF_2',k9_relat_1('#skF_2',k10_relat_1(B_221,A_222)))
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(k2_funct_1(B_221))
      | ~ v2_funct_1(B_221)
      | ~ v1_funct_1(B_221)
      | ~ v1_relat_1(B_221)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(B_221)),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6251,c_756])).

tff(c_11733,plain,(
    ! [B_288,A_289] :
      ( k9_relat_1(k2_funct_1('#skF_2'),k10_relat_1(k2_funct_1('#skF_2'),k10_relat_1(B_288,A_289))) = k10_relat_1('#skF_2',k9_relat_1('#skF_2',k10_relat_1(B_288,A_289)))
      | ~ v1_relat_1(k2_funct_1(B_288))
      | ~ v2_funct_1(B_288)
      | ~ v1_funct_1(B_288)
      | ~ v1_relat_1(B_288)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(B_288)),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_28,c_26,c_22,c_2894,c_2982,c_6271])).

tff(c_11808,plain,(
    ! [B_288,A_289] :
      ( k10_relat_1('#skF_2',k10_relat_1(k2_funct_1('#skF_2'),k10_relat_1(B_288,A_289))) = k10_relat_1('#skF_2',k9_relat_1('#skF_2',k10_relat_1(B_288,A_289)))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(k2_funct_1(B_288))
      | ~ v2_funct_1(B_288)
      | ~ v1_funct_1(B_288)
      | ~ v1_relat_1(B_288)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(B_288)),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11733,c_14])).

tff(c_12052,plain,(
    ! [B_290,A_291] :
      ( k10_relat_1('#skF_2',k10_relat_1(k2_funct_1('#skF_2'),k10_relat_1(B_290,A_291))) = k10_relat_1('#skF_2',k9_relat_1('#skF_2',k10_relat_1(B_290,A_291)))
      | ~ v1_relat_1(k2_funct_1(B_290))
      | ~ v2_funct_1(B_290)
      | ~ v1_funct_1(B_290)
      | ~ v1_relat_1(B_290)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(B_290)),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_11808])).

tff(c_12099,plain,(
    ! [B_290,A_291] :
      ( k9_relat_1('#skF_2',k10_relat_1('#skF_2',k9_relat_1('#skF_2',k10_relat_1(B_290,A_291)))) = k10_relat_1(k2_funct_1('#skF_2'),k10_relat_1(B_290,A_291))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
      | ~ v2_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(k2_funct_1(B_290))
      | ~ v2_funct_1(B_290)
      | ~ v1_funct_1(B_290)
      | ~ v1_relat_1(B_290)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(B_290)),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12052,c_948])).

tff(c_12364,plain,(
    ! [B_292,A_293] :
      ( k9_relat_1('#skF_2',k10_relat_1('#skF_2',k9_relat_1('#skF_2',k10_relat_1(B_292,A_293)))) = k10_relat_1(k2_funct_1('#skF_2'),k10_relat_1(B_292,A_293))
      | ~ v1_relat_1(k2_funct_1(B_292))
      | ~ v2_funct_1(B_292)
      | ~ v1_funct_1(B_292)
      | ~ v1_relat_1(B_292)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(B_292)),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_2894,c_2982,c_5526,c_5538,c_12099])).

tff(c_12426,plain,(
    ! [B_292,A_293] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_2'),k10_relat_1(B_292,A_293)),k2_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(k2_funct_1(B_292))
      | ~ v2_funct_1(B_292)
      | ~ v1_funct_1(B_292)
      | ~ v1_relat_1(B_292)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(B_292)),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12364,c_4])).

tff(c_12636,plain,(
    ! [B_294,A_295] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_2'),k10_relat_1(B_294,A_295)),k2_relat_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1(B_294))
      | ~ v2_funct_1(B_294)
      | ~ v1_funct_1(B_294)
      | ~ v1_relat_1(B_294)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(B_294)),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_12426])).

tff(c_12744,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1('#skF_2')),k2_relat_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))),'#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_12636])).

tff(c_12799,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1('#skF_2')),k2_relat_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))),'#skF_1')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2894,c_2982,c_5526,c_5538,c_2894,c_2982,c_5526,c_5538,c_12744])).

tff(c_13789,plain,(
    ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_12799])).

tff(c_13836,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_13789])).

tff(c_13842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_26,c_13836])).

tff(c_13844,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_12799])).

tff(c_351,plain,(
    ! [B_63,A_64] :
      ( k9_relat_1(k2_funct_1(B_63),k10_relat_1(k2_funct_1(B_63),k10_relat_1(B_63,A_64))) = k10_relat_1(B_63,A_64)
      | ~ v1_funct_1(k2_funct_1(B_63))
      | ~ v1_relat_1(k2_funct_1(B_63))
      | ~ v2_funct_1(B_63)
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(resolution,[status(thm)],[c_165,c_12])).

tff(c_1486,plain,(
    ! [B_127,A_128] :
      ( k10_relat_1(B_127,k10_relat_1(k2_funct_1(B_127),k10_relat_1(B_127,A_128))) = k10_relat_1(B_127,A_128)
      | ~ v1_funct_1(k2_funct_1(B_127))
      | ~ v1_relat_1(k2_funct_1(B_127))
      | ~ v2_funct_1(B_127)
      | ~ v1_funct_1(B_127)
      | ~ v1_relat_1(B_127)
      | ~ v2_funct_1(B_127)
      | ~ v1_funct_1(B_127)
      | ~ v1_relat_1(B_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_351])).

tff(c_1551,plain,(
    ! [A_13,A_128] :
      ( k10_relat_1(k2_funct_1(A_13),k10_relat_1(A_13,k10_relat_1(k2_funct_1(A_13),A_128))) = k10_relat_1(k2_funct_1(A_13),A_128)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1(A_13)))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(A_13)))
      | ~ v2_funct_1(k2_funct_1(A_13))
      | ~ v1_funct_1(k2_funct_1(A_13))
      | ~ v1_relat_1(k2_funct_1(A_13))
      | ~ v2_funct_1(k2_funct_1(A_13))
      | ~ v1_funct_1(k2_funct_1(A_13))
      | ~ v1_relat_1(k2_funct_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1486])).

tff(c_451,plain,(
    ! [B_74,A_75] :
      ( k9_relat_1(k2_funct_1(B_74),k10_relat_1(k2_funct_1(B_74),k10_relat_1(B_74,A_75))) = k9_relat_1(k2_funct_1(B_74),A_75)
      | ~ v1_funct_1(k2_funct_1(B_74))
      | ~ v1_relat_1(k2_funct_1(B_74))
      | ~ v2_funct_1(B_74)
      | ~ v1_funct_1(B_74)
      | ~ v1_relat_1(B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_123])).

tff(c_491,plain,(
    ! [B_11,A_75] :
      ( k10_relat_1(B_11,k10_relat_1(k2_funct_1(B_11),k10_relat_1(B_11,A_75))) = k9_relat_1(k2_funct_1(B_11),A_75)
      | ~ v1_funct_1(k2_funct_1(B_11))
      | ~ v1_relat_1(k2_funct_1(B_11))
      | ~ v2_funct_1(B_11)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v2_funct_1(B_11)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_451])).

tff(c_2730,plain,(
    ! [A_151,A_152] :
      ( k9_relat_1(A_151,k10_relat_1(A_151,k10_relat_1(k2_funct_1(A_151),A_152))) = k10_relat_1(k2_funct_1(A_151),A_152)
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(A_151)))
      | ~ v2_funct_1(k2_funct_1(A_151))
      | ~ v1_funct_1(k2_funct_1(A_151))
      | ~ v1_relat_1(k2_funct_1(A_151))
      | ~ v2_funct_1(A_151)
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151) ) ),
    inference(resolution,[status(thm)],[c_924,c_12])).

tff(c_99293,plain,(
    ! [B_717,A_718] :
      ( k9_relat_1(B_717,k9_relat_1(k2_funct_1(B_717),A_718)) = k10_relat_1(k2_funct_1(B_717),k10_relat_1(B_717,A_718))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(B_717)))
      | ~ v2_funct_1(k2_funct_1(B_717))
      | ~ v1_funct_1(k2_funct_1(B_717))
      | ~ v1_relat_1(k2_funct_1(B_717))
      | ~ v2_funct_1(B_717)
      | ~ v1_funct_1(B_717)
      | ~ v1_relat_1(B_717)
      | ~ v1_funct_1(k2_funct_1(B_717))
      | ~ v1_relat_1(k2_funct_1(B_717))
      | ~ v2_funct_1(B_717)
      | ~ v1_funct_1(B_717)
      | ~ v1_relat_1(B_717)
      | ~ v2_funct_1(B_717)
      | ~ v1_funct_1(B_717)
      | ~ v1_relat_1(B_717) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_2730])).

tff(c_99297,plain,(
    ! [A_718] :
      ( k9_relat_1('#skF_2',k9_relat_1(k2_funct_1('#skF_2'),A_718)) = k10_relat_1(k2_funct_1('#skF_2'),k10_relat_1('#skF_2',A_718))
      | ~ v2_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_5538,c_99293])).

tff(c_99332,plain,(
    ! [A_719] : k9_relat_1('#skF_2',k9_relat_1(k2_funct_1('#skF_2'),A_719)) = k10_relat_1(k2_funct_1('#skF_2'),k10_relat_1('#skF_2',A_719)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_2894,c_2982,c_5526,c_99297])).

tff(c_99403,plain,(
    ! [A_719] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_2'),k10_relat_1('#skF_2',A_719)),k2_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99332,c_4])).

tff(c_99822,plain,(
    ! [A_720] : r1_tarski(k10_relat_1(k2_funct_1('#skF_2'),k10_relat_1('#skF_2',A_720)),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_99403])).

tff(c_99896,plain,(
    ! [A_128] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_2'),A_128),k2_relat_1('#skF_2'))
      | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
      | ~ v2_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1551,c_99822])).

tff(c_100073,plain,(
    ! [A_721] : r1_tarski(k10_relat_1(k2_funct_1('#skF_2'),A_721),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_2894,c_2982,c_5526,c_2894,c_2982,c_5526,c_5538,c_13844,c_99896])).

tff(c_100243,plain,(
    ! [A_54] :
      ( r1_tarski(k9_relat_1('#skF_2',A_54),k2_relat_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_100073])).

tff(c_100345,plain,(
    ! [A_722] : r1_tarski(k9_relat_1('#skF_2',A_722),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_100243])).

tff(c_100353,plain,(
    ! [A_722] :
      ( k9_relat_1('#skF_2',k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_722))) = k9_relat_1('#skF_2',A_722)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_100345,c_12])).

tff(c_100491,plain,(
    ! [A_722] : k9_relat_1('#skF_2',k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_722))) = k9_relat_1('#skF_2',A_722) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_100353])).

tff(c_99681,plain,(
    ! [A_10] :
      ( k10_relat_1(k2_funct_1('#skF_2'),k10_relat_1('#skF_2',A_10)) = k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_10))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_99332])).

tff(c_116604,plain,(
    ! [A_759] : k10_relat_1(k2_funct_1('#skF_2'),k10_relat_1('#skF_2',A_759)) = k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_759)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_99681])).

tff(c_6005,plain,(
    ! [A_216,A_217] :
      ( k10_relat_1(k2_funct_1(A_216),k10_relat_1(k2_funct_1(k2_funct_1(A_216)),k9_relat_1(A_216,A_217))) = k9_relat_1(k2_funct_1(k2_funct_1(A_216)),A_217)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1(A_216)))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(A_216)))
      | ~ v2_funct_1(k2_funct_1(A_216))
      | ~ v1_funct_1(k2_funct_1(A_216))
      | ~ v1_relat_1(k2_funct_1(A_216))
      | ~ v2_funct_1(A_216)
      | ~ v1_funct_1(A_216)
      | ~ v1_relat_1(A_216) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_705])).

tff(c_6199,plain,(
    ! [A_13,A_217] :
      ( k10_relat_1(k2_funct_1(A_13),k10_relat_1(A_13,k9_relat_1(A_13,A_217))) = k9_relat_1(k2_funct_1(k2_funct_1(A_13)),A_217)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1(A_13)))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(A_13)))
      | ~ v2_funct_1(k2_funct_1(A_13))
      | ~ v1_funct_1(k2_funct_1(A_13))
      | ~ v1_relat_1(k2_funct_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_6005])).

tff(c_116736,plain,(
    ! [A_217] :
      ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),A_217) = k9_relat_1('#skF_2',k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_217)))
      | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
      | ~ v2_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116604,c_6199])).

tff(c_118055,plain,(
    ! [A_762] : k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),A_762) = k9_relat_1('#skF_2',A_762) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_28,c_26,c_22,c_2894,c_2982,c_5526,c_5538,c_13844,c_100491,c_116736])).

tff(c_118421,plain,(
    ! [A_762] :
      ( k10_relat_1(k2_funct_1('#skF_2'),A_762) = k9_relat_1('#skF_2',A_762)
      | ~ v2_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118055,c_14])).

tff(c_119049,plain,(
    ! [A_763] : k10_relat_1(k2_funct_1('#skF_2'),A_763) = k9_relat_1('#skF_2',A_763) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2894,c_2982,c_5526,c_118421])).

tff(c_613,plain,(
    ! [A_88,A_89] :
      ( k9_relat_1(k2_funct_1(A_88),k10_relat_1(k2_funct_1(A_88),A_89)) = A_89
      | ~ v1_funct_1(k2_funct_1(A_88))
      | ~ r1_tarski(A_89,k1_relat_1(A_88))
      | ~ v1_relat_1(k2_funct_1(A_88))
      | ~ v2_funct_1(A_88)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(resolution,[status(thm)],[c_194,c_12])).

tff(c_650,plain,(
    ! [A_88,A_89] :
      ( k10_relat_1(A_88,k10_relat_1(k2_funct_1(A_88),A_89)) = A_89
      | ~ v2_funct_1(A_88)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88)
      | ~ v1_funct_1(k2_funct_1(A_88))
      | ~ r1_tarski(A_89,k1_relat_1(A_88))
      | ~ v1_relat_1(k2_funct_1(A_88))
      | ~ v2_funct_1(A_88)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_14])).

tff(c_119420,plain,(
    ! [A_763] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_763)) = A_763
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ r1_tarski(A_763,k1_relat_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119049,c_650])).

tff(c_122254,plain,(
    ! [A_775] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_775)) = A_775
      | ~ r1_tarski(A_775,k1_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_2894,c_2982,c_28,c_26,c_22,c_119420])).

tff(c_122290,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_122254])).

tff(c_122305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_122290])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:11:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 43.94/31.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.94/31.25  
% 43.94/31.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.94/31.26  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 43.94/31.26  
% 43.94/31.26  %Foreground sorts:
% 43.94/31.26  
% 43.94/31.26  
% 43.94/31.26  %Background operators:
% 43.94/31.26  
% 43.94/31.26  
% 43.94/31.26  %Foreground operators:
% 43.94/31.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 43.94/31.26  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 43.94/31.26  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 43.94/31.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 43.94/31.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 43.94/31.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 43.94/31.26  tff('#skF_2', type, '#skF_2': $i).
% 43.94/31.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 43.94/31.26  tff('#skF_1', type, '#skF_1': $i).
% 43.94/31.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 43.94/31.26  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 43.94/31.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 43.94/31.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 43.94/31.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 43.94/31.26  
% 43.94/31.28  tff(f_90, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 43.94/31.28  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 43.94/31.28  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 43.94/31.28  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 43.94/31.28  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 43.94/31.28  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 43.94/31.28  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 43.94/31.28  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_1)).
% 43.94/31.28  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 43.94/31.28  tff(c_20, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_90])).
% 43.94/31.28  tff(c_24, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 43.94/31.28  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 43.94/31.28  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 43.94/31.28  tff(c_22, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 43.94/31.28  tff(c_10, plain, (![A_7]: (v1_relat_1(k2_funct_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 43.94/31.28  tff(c_41, plain, (![A_19, C_20, B_21]: (r1_tarski(A_19, C_20) | ~r1_tarski(B_21, C_20) | ~r1_tarski(A_19, B_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 43.94/31.28  tff(c_47, plain, (![A_19]: (r1_tarski(A_19, k1_relat_1('#skF_2')) | ~r1_tarski(A_19, '#skF_1'))), inference(resolution, [status(thm)], [c_24, c_41])).
% 43.94/31.28  tff(c_6, plain, (![A_6]: (k10_relat_1(A_6, k2_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 43.94/31.28  tff(c_91, plain, (![B_30, A_31]: (k9_relat_1(k2_funct_1(B_30), A_31)=k10_relat_1(B_30, A_31) | ~v2_funct_1(B_30) | ~v1_funct_1(B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_63])).
% 43.94/31.28  tff(c_4, plain, (![B_5, A_4]: (r1_tarski(k9_relat_1(B_5, A_4), k2_relat_1(B_5)) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 43.94/31.28  tff(c_165, plain, (![B_41, A_42]: (r1_tarski(k10_relat_1(B_41, A_42), k2_relat_1(k2_funct_1(B_41))) | ~v1_relat_1(k2_funct_1(B_41)) | ~v2_funct_1(B_41) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41))), inference(superposition, [status(thm), theory('equality')], [c_91, c_4])).
% 43.94/31.28  tff(c_177, plain, (![A_6]: (r1_tarski(k1_relat_1(A_6), k2_relat_1(k2_funct_1(A_6))) | ~v1_relat_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_165])).
% 43.94/31.28  tff(c_181, plain, (![A_43]: (r1_tarski(k1_relat_1(A_43), k2_relat_1(k2_funct_1(A_43))) | ~v1_relat_1(k2_funct_1(A_43)) | ~v2_funct_1(A_43) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43) | ~v1_relat_1(A_43))), inference(superposition, [status(thm), theory('equality')], [c_6, c_165])).
% 43.94/31.28  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 43.94/31.28  tff(c_194, plain, (![A_44, A_45]: (r1_tarski(A_44, k2_relat_1(k2_funct_1(A_45))) | ~r1_tarski(A_44, k1_relat_1(A_45)) | ~v1_relat_1(k2_funct_1(A_45)) | ~v2_funct_1(A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_181, c_2])).
% 43.94/31.28  tff(c_414, plain, (![A_70, A_71, A_72]: (r1_tarski(A_70, k2_relat_1(k2_funct_1(A_71))) | ~r1_tarski(A_70, A_72) | ~r1_tarski(A_72, k1_relat_1(A_71)) | ~v1_relat_1(k2_funct_1(A_71)) | ~v2_funct_1(A_71) | ~v1_funct_1(A_71) | ~v1_relat_1(A_71))), inference(resolution, [status(thm)], [c_194, c_2])).
% 43.94/31.28  tff(c_2868, plain, (![A_153, A_154]: (r1_tarski(k1_relat_1(A_153), k2_relat_1(k2_funct_1(A_154))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_153)), k1_relat_1(A_154)) | ~v1_relat_1(k2_funct_1(A_154)) | ~v2_funct_1(A_154) | ~v1_funct_1(A_154) | ~v1_relat_1(A_154) | ~v1_relat_1(k2_funct_1(A_153)) | ~v2_funct_1(A_153) | ~v1_funct_1(A_153) | ~v1_relat_1(A_153))), inference(resolution, [status(thm)], [c_177, c_414])).
% 43.94/31.28  tff(c_2881, plain, (![A_153]: (r1_tarski(k1_relat_1(A_153), k2_relat_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1(A_153)) | ~v2_funct_1(A_153) | ~v1_funct_1(A_153) | ~v1_relat_1(A_153) | ~r1_tarski(k2_relat_1(k2_funct_1(A_153)), '#skF_1'))), inference(resolution, [status(thm)], [c_47, c_2868])).
% 43.94/31.28  tff(c_2884, plain, (![A_153]: (r1_tarski(k1_relat_1(A_153), k2_relat_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1(A_153)) | ~v2_funct_1(A_153) | ~v1_funct_1(A_153) | ~v1_relat_1(A_153) | ~r1_tarski(k2_relat_1(k2_funct_1(A_153)), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_2881])).
% 43.94/31.28  tff(c_2885, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_2884])).
% 43.94/31.28  tff(c_2888, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_2885])).
% 43.94/31.28  tff(c_2892, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_2888])).
% 43.94/31.28  tff(c_2894, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_2884])).
% 43.94/31.28  tff(c_8, plain, (![A_7]: (v1_funct_1(k2_funct_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 43.94/31.28  tff(c_2917, plain, (![A_157]: (r1_tarski(k1_relat_1(A_157), k2_relat_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1(A_157)) | ~v2_funct_1(A_157) | ~v1_funct_1(A_157) | ~v1_relat_1(A_157) | ~r1_tarski(k2_relat_1(k2_funct_1(A_157)), '#skF_1'))), inference(splitRight, [status(thm)], [c_2884])).
% 43.94/31.28  tff(c_12, plain, (![B_9, A_8]: (k9_relat_1(B_9, k10_relat_1(B_9, A_8))=A_8 | ~r1_tarski(A_8, k2_relat_1(B_9)) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 43.94/31.28  tff(c_2921, plain, (![A_157]: (k9_relat_1(k2_funct_1('#skF_2'), k10_relat_1(k2_funct_1('#skF_2'), k1_relat_1(A_157)))=k1_relat_1(A_157) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1(A_157)) | ~v2_funct_1(A_157) | ~v1_funct_1(A_157) | ~v1_relat_1(A_157) | ~r1_tarski(k2_relat_1(k2_funct_1(A_157)), '#skF_1'))), inference(resolution, [status(thm)], [c_2917, c_12])).
% 43.94/31.28  tff(c_2935, plain, (![A_157]: (k9_relat_1(k2_funct_1('#skF_2'), k10_relat_1(k2_funct_1('#skF_2'), k1_relat_1(A_157)))=k1_relat_1(A_157) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1(A_157)) | ~v2_funct_1(A_157) | ~v1_funct_1(A_157) | ~v1_relat_1(A_157) | ~r1_tarski(k2_relat_1(k2_funct_1(A_157)), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2894, c_2921])).
% 43.94/31.28  tff(c_2973, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_2935])).
% 43.94/31.28  tff(c_2976, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_2973])).
% 43.94/31.28  tff(c_2980, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_2976])).
% 43.94/31.28  tff(c_2982, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_2935])).
% 43.94/31.28  tff(c_16, plain, (![A_12]: (v2_funct_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_71])).
% 43.94/31.28  tff(c_3144, plain, (![A_162]: (k9_relat_1(k2_funct_1('#skF_2'), k10_relat_1(k2_funct_1('#skF_2'), k1_relat_1(A_162)))=k1_relat_1(A_162) | ~v1_relat_1(k2_funct_1(A_162)) | ~v2_funct_1(A_162) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162) | ~r1_tarski(k2_relat_1(k2_funct_1(A_162)), '#skF_1'))), inference(splitRight, [status(thm)], [c_2935])).
% 43.94/31.28  tff(c_14, plain, (![B_11, A_10]: (k9_relat_1(k2_funct_1(B_11), A_10)=k10_relat_1(B_11, A_10) | ~v2_funct_1(B_11) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 43.94/31.28  tff(c_3219, plain, (![A_162]: (k10_relat_1('#skF_2', k10_relat_1(k2_funct_1('#skF_2'), k1_relat_1(A_162)))=k1_relat_1(A_162) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1(A_162)) | ~v2_funct_1(A_162) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162) | ~r1_tarski(k2_relat_1(k2_funct_1(A_162)), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3144, c_14])).
% 43.94/31.28  tff(c_3346, plain, (![A_163]: (k10_relat_1('#skF_2', k10_relat_1(k2_funct_1('#skF_2'), k1_relat_1(A_163)))=k1_relat_1(A_163) | ~v1_relat_1(k2_funct_1(A_163)) | ~v2_funct_1(A_163) | ~v1_funct_1(A_163) | ~v1_relat_1(A_163) | ~r1_tarski(k2_relat_1(k2_funct_1(A_163)), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_3219])).
% 43.94/31.28  tff(c_18, plain, (![A_13]: (k2_funct_1(k2_funct_1(A_13))=A_13 | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_79])).
% 43.94/31.28  tff(c_924, plain, (![A_98, A_99]: (r1_tarski(k10_relat_1(k2_funct_1(A_98), A_99), k2_relat_1(A_98)) | ~v1_relat_1(k2_funct_1(k2_funct_1(A_98))) | ~v2_funct_1(k2_funct_1(A_98)) | ~v1_funct_1(k2_funct_1(A_98)) | ~v1_relat_1(k2_funct_1(A_98)) | ~v2_funct_1(A_98) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(superposition, [status(thm), theory('equality')], [c_18, c_165])).
% 43.94/31.28  tff(c_948, plain, (![A_98, A_99]: (k9_relat_1(A_98, k10_relat_1(A_98, k10_relat_1(k2_funct_1(A_98), A_99)))=k10_relat_1(k2_funct_1(A_98), A_99) | ~v1_relat_1(k2_funct_1(k2_funct_1(A_98))) | ~v2_funct_1(k2_funct_1(A_98)) | ~v1_funct_1(k2_funct_1(A_98)) | ~v1_relat_1(k2_funct_1(A_98)) | ~v2_funct_1(A_98) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(resolution, [status(thm)], [c_924, c_12])).
% 43.94/31.28  tff(c_3352, plain, (![A_163]: (k10_relat_1(k2_funct_1('#skF_2'), k1_relat_1(A_163))=k9_relat_1('#skF_2', k1_relat_1(A_163)) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1(A_163)) | ~v2_funct_1(A_163) | ~v1_funct_1(A_163) | ~v1_relat_1(A_163) | ~r1_tarski(k2_relat_1(k2_funct_1(A_163)), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3346, c_948])).
% 43.94/31.28  tff(c_3406, plain, (![A_163]: (k10_relat_1(k2_funct_1('#skF_2'), k1_relat_1(A_163))=k9_relat_1('#skF_2', k1_relat_1(A_163)) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1(A_163)) | ~v2_funct_1(A_163) | ~v1_funct_1(A_163) | ~v1_relat_1(A_163) | ~r1_tarski(k2_relat_1(k2_funct_1(A_163)), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_2894, c_2982, c_3352])).
% 43.94/31.28  tff(c_5514, plain, (~v2_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_3406])).
% 43.94/31.28  tff(c_5520, plain, (~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_5514])).
% 43.94/31.28  tff(c_5524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_5520])).
% 43.94/31.28  tff(c_5526, plain, (v2_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_3406])).
% 43.94/31.28  tff(c_5525, plain, (![A_163]: (~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | k10_relat_1(k2_funct_1('#skF_2'), k1_relat_1(A_163))=k9_relat_1('#skF_2', k1_relat_1(A_163)) | ~v1_relat_1(k2_funct_1(A_163)) | ~v2_funct_1(A_163) | ~v1_funct_1(A_163) | ~v1_relat_1(A_163) | ~r1_tarski(k2_relat_1(k2_funct_1(A_163)), '#skF_1'))), inference(splitRight, [status(thm)], [c_3406])).
% 43.94/31.28  tff(c_5527, plain, (~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_5525])).
% 43.94/31.28  tff(c_5530, plain, (~v1_relat_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18, c_5527])).
% 43.94/31.28  tff(c_5536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_28, c_5530])).
% 43.94/31.28  tff(c_5538, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(splitRight, [status(thm)], [c_5525])).
% 43.94/31.28  tff(c_503, plain, (![A_76]: (k9_relat_1(k2_funct_1(A_76), k10_relat_1(k2_funct_1(A_76), k1_relat_1(A_76)))=k1_relat_1(A_76) | ~v1_funct_1(k2_funct_1(A_76)) | ~v1_relat_1(k2_funct_1(A_76)) | ~v2_funct_1(A_76) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(resolution, [status(thm)], [c_181, c_12])).
% 43.94/31.28  tff(c_517, plain, (![A_76]: (k10_relat_1(A_76, k10_relat_1(k2_funct_1(A_76), k1_relat_1(A_76)))=k1_relat_1(A_76) | ~v2_funct_1(A_76) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76) | ~v1_funct_1(k2_funct_1(A_76)) | ~v1_relat_1(k2_funct_1(A_76)) | ~v2_funct_1(A_76) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(superposition, [status(thm), theory('equality')], [c_503, c_14])).
% 43.94/31.28  tff(c_100, plain, (![B_30, A_31]: (r1_tarski(k10_relat_1(B_30, A_31), k2_relat_1(k2_funct_1(B_30))) | ~v1_relat_1(k2_funct_1(B_30)) | ~v2_funct_1(B_30) | ~v1_funct_1(B_30) | ~v1_relat_1(B_30))), inference(superposition, [status(thm), theory('equality')], [c_91, c_4])).
% 43.94/31.28  tff(c_5928, plain, (![B_211, A_212, A_213]: (r1_tarski(k10_relat_1(B_211, A_212), k2_relat_1(k2_funct_1(A_213))) | ~r1_tarski(k2_relat_1(k2_funct_1(B_211)), k1_relat_1(A_213)) | ~v1_relat_1(k2_funct_1(A_213)) | ~v2_funct_1(A_213) | ~v1_funct_1(A_213) | ~v1_relat_1(A_213) | ~v1_relat_1(k2_funct_1(B_211)) | ~v2_funct_1(B_211) | ~v1_funct_1(B_211) | ~v1_relat_1(B_211))), inference(resolution, [status(thm)], [c_100, c_414])).
% 43.94/31.28  tff(c_5937, plain, (![B_211, A_212]: (r1_tarski(k10_relat_1(B_211, A_212), k2_relat_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1(B_211)) | ~v2_funct_1(B_211) | ~v1_funct_1(B_211) | ~v1_relat_1(B_211) | ~r1_tarski(k2_relat_1(k2_funct_1(B_211)), '#skF_1'))), inference(resolution, [status(thm)], [c_47, c_5928])).
% 43.94/31.28  tff(c_5941, plain, (![B_214, A_215]: (r1_tarski(k10_relat_1(B_214, A_215), k2_relat_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1(B_214)) | ~v2_funct_1(B_214) | ~v1_funct_1(B_214) | ~v1_relat_1(B_214) | ~r1_tarski(k2_relat_1(k2_funct_1(B_214)), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_2894, c_5937])).
% 43.94/31.28  tff(c_5947, plain, (![B_214, A_215]: (k9_relat_1(k2_funct_1('#skF_2'), k10_relat_1(k2_funct_1('#skF_2'), k10_relat_1(B_214, A_215)))=k10_relat_1(B_214, A_215) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1(B_214)) | ~v2_funct_1(B_214) | ~v1_funct_1(B_214) | ~v1_relat_1(B_214) | ~r1_tarski(k2_relat_1(k2_funct_1(B_214)), '#skF_1'))), inference(resolution, [status(thm)], [c_5941, c_12])).
% 43.94/31.28  tff(c_6251, plain, (![B_221, A_222]: (k9_relat_1(k2_funct_1('#skF_2'), k10_relat_1(k2_funct_1('#skF_2'), k10_relat_1(B_221, A_222)))=k10_relat_1(B_221, A_222) | ~v1_relat_1(k2_funct_1(B_221)) | ~v2_funct_1(B_221) | ~v1_funct_1(B_221) | ~v1_relat_1(B_221) | ~r1_tarski(k2_relat_1(k2_funct_1(B_221)), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2894, c_2982, c_5947])).
% 43.94/31.28  tff(c_210, plain, (![A_49, A_50]: (k10_relat_1(k2_funct_1(A_49), A_50)=k9_relat_1(A_49, A_50) | ~v2_funct_1(k2_funct_1(A_49)) | ~v1_funct_1(k2_funct_1(A_49)) | ~v1_relat_1(k2_funct_1(A_49)) | ~v2_funct_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(superposition, [status(thm), theory('equality')], [c_18, c_91])).
% 43.94/31.28  tff(c_216, plain, (![A_51, A_52]: (k10_relat_1(k2_funct_1(A_51), A_52)=k9_relat_1(A_51, A_52) | ~v1_funct_1(k2_funct_1(A_51)) | ~v1_relat_1(k2_funct_1(A_51)) | ~v2_funct_1(A_51) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(resolution, [status(thm)], [c_16, c_210])).
% 43.94/31.28  tff(c_222, plain, (![A_53, A_54]: (k10_relat_1(k2_funct_1(A_53), A_54)=k9_relat_1(A_53, A_54) | ~v1_funct_1(k2_funct_1(A_53)) | ~v2_funct_1(A_53) | ~v1_funct_1(A_53) | ~v1_relat_1(A_53))), inference(resolution, [status(thm)], [c_10, c_216])).
% 43.94/31.28  tff(c_227, plain, (![A_7, A_54]: (k10_relat_1(k2_funct_1(A_7), A_54)=k9_relat_1(A_7, A_54) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_8, c_222])).
% 43.94/31.28  tff(c_119, plain, (![B_34, A_35]: (k9_relat_1(B_34, k10_relat_1(B_34, A_35))=A_35 | ~r1_tarski(A_35, k2_relat_1(B_34)) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_55])).
% 43.94/31.28  tff(c_123, plain, (![B_36, A_37]: (k9_relat_1(B_36, k10_relat_1(B_36, k9_relat_1(B_36, A_37)))=k9_relat_1(B_36, A_37) | ~v1_funct_1(B_36) | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_4, c_119])).
% 43.94/31.28  tff(c_705, plain, (![B_90, A_91]: (k10_relat_1(B_90, k10_relat_1(k2_funct_1(B_90), k9_relat_1(k2_funct_1(B_90), A_91)))=k9_relat_1(k2_funct_1(B_90), A_91) | ~v1_funct_1(k2_funct_1(B_90)) | ~v1_relat_1(k2_funct_1(B_90)) | ~v2_funct_1(B_90) | ~v1_funct_1(B_90) | ~v1_relat_1(B_90))), inference(superposition, [status(thm), theory('equality')], [c_14, c_123])).
% 43.94/31.28  tff(c_756, plain, (![A_7, A_91]: (k10_relat_1(A_7, k9_relat_1(A_7, k9_relat_1(k2_funct_1(A_7), A_91)))=k9_relat_1(k2_funct_1(A_7), A_91) | ~v1_funct_1(k2_funct_1(A_7)) | ~v1_relat_1(k2_funct_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_227, c_705])).
% 43.94/31.28  tff(c_6271, plain, (![B_221, A_222]: (k9_relat_1(k2_funct_1('#skF_2'), k10_relat_1(k2_funct_1('#skF_2'), k10_relat_1(B_221, A_222)))=k10_relat_1('#skF_2', k9_relat_1('#skF_2', k10_relat_1(B_221, A_222))) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1(B_221)) | ~v2_funct_1(B_221) | ~v1_funct_1(B_221) | ~v1_relat_1(B_221) | ~r1_tarski(k2_relat_1(k2_funct_1(B_221)), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6251, c_756])).
% 43.94/31.28  tff(c_11733, plain, (![B_288, A_289]: (k9_relat_1(k2_funct_1('#skF_2'), k10_relat_1(k2_funct_1('#skF_2'), k10_relat_1(B_288, A_289)))=k10_relat_1('#skF_2', k9_relat_1('#skF_2', k10_relat_1(B_288, A_289))) | ~v1_relat_1(k2_funct_1(B_288)) | ~v2_funct_1(B_288) | ~v1_funct_1(B_288) | ~v1_relat_1(B_288) | ~r1_tarski(k2_relat_1(k2_funct_1(B_288)), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_28, c_26, c_22, c_2894, c_2982, c_6271])).
% 43.94/31.28  tff(c_11808, plain, (![B_288, A_289]: (k10_relat_1('#skF_2', k10_relat_1(k2_funct_1('#skF_2'), k10_relat_1(B_288, A_289)))=k10_relat_1('#skF_2', k9_relat_1('#skF_2', k10_relat_1(B_288, A_289))) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1(B_288)) | ~v2_funct_1(B_288) | ~v1_funct_1(B_288) | ~v1_relat_1(B_288) | ~r1_tarski(k2_relat_1(k2_funct_1(B_288)), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_11733, c_14])).
% 43.94/31.28  tff(c_12052, plain, (![B_290, A_291]: (k10_relat_1('#skF_2', k10_relat_1(k2_funct_1('#skF_2'), k10_relat_1(B_290, A_291)))=k10_relat_1('#skF_2', k9_relat_1('#skF_2', k10_relat_1(B_290, A_291))) | ~v1_relat_1(k2_funct_1(B_290)) | ~v2_funct_1(B_290) | ~v1_funct_1(B_290) | ~v1_relat_1(B_290) | ~r1_tarski(k2_relat_1(k2_funct_1(B_290)), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_11808])).
% 43.94/31.28  tff(c_12099, plain, (![B_290, A_291]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', k9_relat_1('#skF_2', k10_relat_1(B_290, A_291))))=k10_relat_1(k2_funct_1('#skF_2'), k10_relat_1(B_290, A_291)) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1(B_290)) | ~v2_funct_1(B_290) | ~v1_funct_1(B_290) | ~v1_relat_1(B_290) | ~r1_tarski(k2_relat_1(k2_funct_1(B_290)), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12052, c_948])).
% 43.94/31.28  tff(c_12364, plain, (![B_292, A_293]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', k9_relat_1('#skF_2', k10_relat_1(B_292, A_293))))=k10_relat_1(k2_funct_1('#skF_2'), k10_relat_1(B_292, A_293)) | ~v1_relat_1(k2_funct_1(B_292)) | ~v2_funct_1(B_292) | ~v1_funct_1(B_292) | ~v1_relat_1(B_292) | ~r1_tarski(k2_relat_1(k2_funct_1(B_292)), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_2894, c_2982, c_5526, c_5538, c_12099])).
% 43.94/31.28  tff(c_12426, plain, (![B_292, A_293]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_2'), k10_relat_1(B_292, A_293)), k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1(B_292)) | ~v2_funct_1(B_292) | ~v1_funct_1(B_292) | ~v1_relat_1(B_292) | ~r1_tarski(k2_relat_1(k2_funct_1(B_292)), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12364, c_4])).
% 43.94/31.28  tff(c_12636, plain, (![B_294, A_295]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_2'), k10_relat_1(B_294, A_295)), k2_relat_1('#skF_2')) | ~v1_relat_1(k2_funct_1(B_294)) | ~v2_funct_1(B_294) | ~v1_funct_1(B_294) | ~v1_relat_1(B_294) | ~r1_tarski(k2_relat_1(k2_funct_1(B_294)), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_12426])).
% 43.94/31.28  tff(c_12744, plain, (r1_tarski(k1_relat_1(k2_funct_1('#skF_2')), k2_relat_1('#skF_2')) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~r1_tarski(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), '#skF_1') | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_517, c_12636])).
% 43.94/31.28  tff(c_12799, plain, (r1_tarski(k1_relat_1(k2_funct_1('#skF_2')), k2_relat_1('#skF_2')) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~r1_tarski(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), '#skF_1') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2894, c_2982, c_5526, c_5538, c_2894, c_2982, c_5526, c_5538, c_12744])).
% 43.94/31.28  tff(c_13789, plain, (~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_12799])).
% 43.94/31.28  tff(c_13836, plain, (~v1_funct_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18, c_13789])).
% 43.94/31.28  tff(c_13842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_26, c_13836])).
% 43.94/31.28  tff(c_13844, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(splitRight, [status(thm)], [c_12799])).
% 43.94/31.28  tff(c_351, plain, (![B_63, A_64]: (k9_relat_1(k2_funct_1(B_63), k10_relat_1(k2_funct_1(B_63), k10_relat_1(B_63, A_64)))=k10_relat_1(B_63, A_64) | ~v1_funct_1(k2_funct_1(B_63)) | ~v1_relat_1(k2_funct_1(B_63)) | ~v2_funct_1(B_63) | ~v1_funct_1(B_63) | ~v1_relat_1(B_63))), inference(resolution, [status(thm)], [c_165, c_12])).
% 43.94/31.28  tff(c_1486, plain, (![B_127, A_128]: (k10_relat_1(B_127, k10_relat_1(k2_funct_1(B_127), k10_relat_1(B_127, A_128)))=k10_relat_1(B_127, A_128) | ~v1_funct_1(k2_funct_1(B_127)) | ~v1_relat_1(k2_funct_1(B_127)) | ~v2_funct_1(B_127) | ~v1_funct_1(B_127) | ~v1_relat_1(B_127) | ~v2_funct_1(B_127) | ~v1_funct_1(B_127) | ~v1_relat_1(B_127))), inference(superposition, [status(thm), theory('equality')], [c_14, c_351])).
% 43.94/31.28  tff(c_1551, plain, (![A_13, A_128]: (k10_relat_1(k2_funct_1(A_13), k10_relat_1(A_13, k10_relat_1(k2_funct_1(A_13), A_128)))=k10_relat_1(k2_funct_1(A_13), A_128) | ~v1_funct_1(k2_funct_1(k2_funct_1(A_13))) | ~v1_relat_1(k2_funct_1(k2_funct_1(A_13))) | ~v2_funct_1(k2_funct_1(A_13)) | ~v1_funct_1(k2_funct_1(A_13)) | ~v1_relat_1(k2_funct_1(A_13)) | ~v2_funct_1(k2_funct_1(A_13)) | ~v1_funct_1(k2_funct_1(A_13)) | ~v1_relat_1(k2_funct_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1486])).
% 43.94/31.28  tff(c_451, plain, (![B_74, A_75]: (k9_relat_1(k2_funct_1(B_74), k10_relat_1(k2_funct_1(B_74), k10_relat_1(B_74, A_75)))=k9_relat_1(k2_funct_1(B_74), A_75) | ~v1_funct_1(k2_funct_1(B_74)) | ~v1_relat_1(k2_funct_1(B_74)) | ~v2_funct_1(B_74) | ~v1_funct_1(B_74) | ~v1_relat_1(B_74))), inference(superposition, [status(thm), theory('equality')], [c_14, c_123])).
% 43.94/31.28  tff(c_491, plain, (![B_11, A_75]: (k10_relat_1(B_11, k10_relat_1(k2_funct_1(B_11), k10_relat_1(B_11, A_75)))=k9_relat_1(k2_funct_1(B_11), A_75) | ~v1_funct_1(k2_funct_1(B_11)) | ~v1_relat_1(k2_funct_1(B_11)) | ~v2_funct_1(B_11) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v2_funct_1(B_11) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(superposition, [status(thm), theory('equality')], [c_14, c_451])).
% 43.94/31.28  tff(c_2730, plain, (![A_151, A_152]: (k9_relat_1(A_151, k10_relat_1(A_151, k10_relat_1(k2_funct_1(A_151), A_152)))=k10_relat_1(k2_funct_1(A_151), A_152) | ~v1_relat_1(k2_funct_1(k2_funct_1(A_151))) | ~v2_funct_1(k2_funct_1(A_151)) | ~v1_funct_1(k2_funct_1(A_151)) | ~v1_relat_1(k2_funct_1(A_151)) | ~v2_funct_1(A_151) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151))), inference(resolution, [status(thm)], [c_924, c_12])).
% 43.94/31.28  tff(c_99293, plain, (![B_717, A_718]: (k9_relat_1(B_717, k9_relat_1(k2_funct_1(B_717), A_718))=k10_relat_1(k2_funct_1(B_717), k10_relat_1(B_717, A_718)) | ~v1_relat_1(k2_funct_1(k2_funct_1(B_717))) | ~v2_funct_1(k2_funct_1(B_717)) | ~v1_funct_1(k2_funct_1(B_717)) | ~v1_relat_1(k2_funct_1(B_717)) | ~v2_funct_1(B_717) | ~v1_funct_1(B_717) | ~v1_relat_1(B_717) | ~v1_funct_1(k2_funct_1(B_717)) | ~v1_relat_1(k2_funct_1(B_717)) | ~v2_funct_1(B_717) | ~v1_funct_1(B_717) | ~v1_relat_1(B_717) | ~v2_funct_1(B_717) | ~v1_funct_1(B_717) | ~v1_relat_1(B_717))), inference(superposition, [status(thm), theory('equality')], [c_491, c_2730])).
% 43.94/31.28  tff(c_99297, plain, (![A_718]: (k9_relat_1('#skF_2', k9_relat_1(k2_funct_1('#skF_2'), A_718))=k10_relat_1(k2_funct_1('#skF_2'), k10_relat_1('#skF_2', A_718)) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_5538, c_99293])).
% 43.94/31.28  tff(c_99332, plain, (![A_719]: (k9_relat_1('#skF_2', k9_relat_1(k2_funct_1('#skF_2'), A_719))=k10_relat_1(k2_funct_1('#skF_2'), k10_relat_1('#skF_2', A_719)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_2894, c_2982, c_5526, c_99297])).
% 43.94/31.28  tff(c_99403, plain, (![A_719]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_2'), k10_relat_1('#skF_2', A_719)), k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_99332, c_4])).
% 43.94/31.28  tff(c_99822, plain, (![A_720]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_2'), k10_relat_1('#skF_2', A_720)), k2_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_99403])).
% 43.94/31.28  tff(c_99896, plain, (![A_128]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_2'), A_128), k2_relat_1('#skF_2')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1551, c_99822])).
% 43.94/31.28  tff(c_100073, plain, (![A_721]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_2'), A_721), k2_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_2894, c_2982, c_5526, c_2894, c_2982, c_5526, c_5538, c_13844, c_99896])).
% 43.94/31.28  tff(c_100243, plain, (![A_54]: (r1_tarski(k9_relat_1('#skF_2', A_54), k2_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_227, c_100073])).
% 43.94/31.28  tff(c_100345, plain, (![A_722]: (r1_tarski(k9_relat_1('#skF_2', A_722), k2_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_100243])).
% 43.94/31.28  tff(c_100353, plain, (![A_722]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_722)))=k9_relat_1('#skF_2', A_722) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_100345, c_12])).
% 43.94/31.28  tff(c_100491, plain, (![A_722]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_722)))=k9_relat_1('#skF_2', A_722))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_100353])).
% 43.94/31.28  tff(c_99681, plain, (![A_10]: (k10_relat_1(k2_funct_1('#skF_2'), k10_relat_1('#skF_2', A_10))=k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_10)) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_99332])).
% 43.94/31.28  tff(c_116604, plain, (![A_759]: (k10_relat_1(k2_funct_1('#skF_2'), k10_relat_1('#skF_2', A_759))=k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_759)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_99681])).
% 43.94/31.28  tff(c_6005, plain, (![A_216, A_217]: (k10_relat_1(k2_funct_1(A_216), k10_relat_1(k2_funct_1(k2_funct_1(A_216)), k9_relat_1(A_216, A_217)))=k9_relat_1(k2_funct_1(k2_funct_1(A_216)), A_217) | ~v1_funct_1(k2_funct_1(k2_funct_1(A_216))) | ~v1_relat_1(k2_funct_1(k2_funct_1(A_216))) | ~v2_funct_1(k2_funct_1(A_216)) | ~v1_funct_1(k2_funct_1(A_216)) | ~v1_relat_1(k2_funct_1(A_216)) | ~v2_funct_1(A_216) | ~v1_funct_1(A_216) | ~v1_relat_1(A_216))), inference(superposition, [status(thm), theory('equality')], [c_18, c_705])).
% 43.94/31.28  tff(c_6199, plain, (![A_13, A_217]: (k10_relat_1(k2_funct_1(A_13), k10_relat_1(A_13, k9_relat_1(A_13, A_217)))=k9_relat_1(k2_funct_1(k2_funct_1(A_13)), A_217) | ~v1_funct_1(k2_funct_1(k2_funct_1(A_13))) | ~v1_relat_1(k2_funct_1(k2_funct_1(A_13))) | ~v2_funct_1(k2_funct_1(A_13)) | ~v1_funct_1(k2_funct_1(A_13)) | ~v1_relat_1(k2_funct_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_18, c_6005])).
% 43.94/31.28  tff(c_116736, plain, (![A_217]: (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), A_217)=k9_relat_1('#skF_2', k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_217))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116604, c_6199])).
% 43.94/31.28  tff(c_118055, plain, (![A_762]: (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), A_762)=k9_relat_1('#skF_2', A_762))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_28, c_26, c_22, c_2894, c_2982, c_5526, c_5538, c_13844, c_100491, c_116736])).
% 43.94/31.28  tff(c_118421, plain, (![A_762]: (k10_relat_1(k2_funct_1('#skF_2'), A_762)=k9_relat_1('#skF_2', A_762) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_118055, c_14])).
% 43.94/31.28  tff(c_119049, plain, (![A_763]: (k10_relat_1(k2_funct_1('#skF_2'), A_763)=k9_relat_1('#skF_2', A_763))), inference(demodulation, [status(thm), theory('equality')], [c_2894, c_2982, c_5526, c_118421])).
% 43.94/31.28  tff(c_613, plain, (![A_88, A_89]: (k9_relat_1(k2_funct_1(A_88), k10_relat_1(k2_funct_1(A_88), A_89))=A_89 | ~v1_funct_1(k2_funct_1(A_88)) | ~r1_tarski(A_89, k1_relat_1(A_88)) | ~v1_relat_1(k2_funct_1(A_88)) | ~v2_funct_1(A_88) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(resolution, [status(thm)], [c_194, c_12])).
% 43.94/31.28  tff(c_650, plain, (![A_88, A_89]: (k10_relat_1(A_88, k10_relat_1(k2_funct_1(A_88), A_89))=A_89 | ~v2_funct_1(A_88) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88) | ~v1_funct_1(k2_funct_1(A_88)) | ~r1_tarski(A_89, k1_relat_1(A_88)) | ~v1_relat_1(k2_funct_1(A_88)) | ~v2_funct_1(A_88) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(superposition, [status(thm), theory('equality')], [c_613, c_14])).
% 43.94/31.28  tff(c_119420, plain, (![A_763]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_763))=A_763 | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1(k2_funct_1('#skF_2')) | ~r1_tarski(A_763, k1_relat_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_119049, c_650])).
% 43.94/31.28  tff(c_122254, plain, (![A_775]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_775))=A_775 | ~r1_tarski(A_775, k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_2894, c_2982, c_28, c_26, c_22, c_119420])).
% 43.94/31.28  tff(c_122290, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(resolution, [status(thm)], [c_24, c_122254])).
% 43.94/31.28  tff(c_122305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_122290])).
% 43.94/31.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.94/31.28  
% 43.94/31.28  Inference rules
% 43.94/31.28  ----------------------
% 43.94/31.28  #Ref     : 0
% 43.94/31.28  #Sup     : 28448
% 43.94/31.28  #Fact    : 0
% 43.94/31.28  #Define  : 0
% 43.94/31.28  #Split   : 17
% 43.94/31.28  #Chain   : 0
% 43.94/31.28  #Close   : 0
% 43.94/31.28  
% 43.94/31.28  Ordering : KBO
% 43.94/31.28  
% 43.94/31.28  Simplification rules
% 43.94/31.28  ----------------------
% 43.94/31.28  #Subsume      : 15344
% 43.94/31.28  #Demod        : 100499
% 43.94/31.28  #Tautology    : 1841
% 43.94/31.28  #SimpNegUnit  : 9
% 43.94/31.28  #BackRed      : 172
% 43.94/31.28  
% 43.94/31.28  #Partial instantiations: 0
% 43.94/31.28  #Strategies tried      : 1
% 43.94/31.28  
% 43.94/31.28  Timing (in seconds)
% 43.94/31.28  ----------------------
% 43.94/31.29  Preprocessing        : 0.28
% 43.94/31.29  Parsing              : 0.16
% 43.94/31.29  CNF conversion       : 0.02
% 43.94/31.29  Main loop            : 30.17
% 43.94/31.29  Inferencing          : 5.02
% 43.94/31.29  Reduction            : 6.62
% 43.94/31.29  Demodulation         : 4.82
% 43.94/31.29  BG Simplification    : 0.54
% 43.94/31.29  Subsumption          : 17.13
% 43.94/31.29  Abstraction          : 1.35
% 43.94/31.29  MUC search           : 0.00
% 43.94/31.29  Cooper               : 0.00
% 43.94/31.29  Total                : 30.50
% 43.94/31.29  Index Insertion      : 0.00
% 43.94/31.29  Index Deletion       : 0.00
% 43.94/31.29  Index Matching       : 0.00
% 43.94/31.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
