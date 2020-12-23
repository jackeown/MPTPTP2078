%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:28 EST 2020

% Result     : Theorem 15.88s
% Output     : CNFRefutation 15.88s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 278 expanded)
%              Number of leaves         :   22 ( 110 expanded)
%              Depth                    :   25
%              Number of atoms          :  200 ( 836 expanded)
%              Number of equality atoms :   11 (  76 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
          & r1_tarski(A,k1_relat_1(C))
          & v2_funct_1(C) )
       => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [C_8,A_6,B_7] :
      ( r1_tarski(k9_relat_1(C_8,A_6),k9_relat_1(C_8,B_7))
      | ~ r1_tarski(A_6,B_7)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_102,plain,(
    ! [C_32,A_33,B_34] :
      ( r1_tarski(k9_relat_1(C_32,A_33),k9_relat_1(C_32,B_34))
      | ~ r1_tarski(A_33,B_34)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_367,plain,(
    ! [A_58,C_59,B_60,A_61] :
      ( r1_tarski(A_58,k9_relat_1(C_59,B_60))
      | ~ r1_tarski(A_58,k9_relat_1(C_59,A_61))
      | ~ r1_tarski(A_61,B_60)
      | ~ v1_relat_1(C_59) ) ),
    inference(resolution,[status(thm)],[c_102,c_8])).

tff(c_404,plain,(
    ! [C_63,A_64,B_65,B_66] :
      ( r1_tarski(k9_relat_1(C_63,A_64),k9_relat_1(C_63,B_65))
      | ~ r1_tarski(B_66,B_65)
      | ~ r1_tarski(A_64,B_66)
      | ~ v1_relat_1(C_63) ) ),
    inference(resolution,[status(thm)],[c_10,c_367])).

tff(c_438,plain,(
    ! [C_67,A_68] :
      ( r1_tarski(k9_relat_1(C_67,A_68),k9_relat_1(C_67,k1_relat_1('#skF_2')))
      | ~ r1_tarski(A_68,'#skF_1')
      | ~ v1_relat_1(C_67) ) ),
    inference(resolution,[status(thm)],[c_26,c_404])).

tff(c_12,plain,(
    ! [A_9] :
      ( k10_relat_1(A_9,k2_relat_1(A_9)) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_89,plain,(
    ! [B_30,A_31] :
      ( r1_tarski(k9_relat_1(B_30,k10_relat_1(B_30,A_31)),A_31)
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_122,plain,(
    ! [A_37] :
      ( r1_tarski(k9_relat_1(A_37,k1_relat_1(A_37)),k2_relat_1(A_37))
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_130,plain,(
    ! [A_3,A_37] :
      ( r1_tarski(A_3,k2_relat_1(A_37))
      | ~ r1_tarski(A_3,k9_relat_1(A_37,k1_relat_1(A_37)))
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(resolution,[status(thm)],[c_122,c_8])).

tff(c_449,plain,(
    ! [A_68] :
      ( r1_tarski(k9_relat_1('#skF_2',A_68),k2_relat_1('#skF_2'))
      | ~ v1_funct_1('#skF_2')
      | ~ r1_tarski(A_68,'#skF_1')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_438,c_130])).

tff(c_477,plain,(
    ! [A_69] :
      ( r1_tarski(k9_relat_1('#skF_2',A_69),k2_relat_1('#skF_2'))
      | ~ r1_tarski(A_69,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_449])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( k9_relat_1(B_13,k10_relat_1(B_13,A_12)) = A_12
      | ~ r1_tarski(A_12,k2_relat_1(B_13))
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_481,plain,(
    ! [A_69] :
      ( k9_relat_1('#skF_2',k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_69))) = k9_relat_1('#skF_2',A_69)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(A_69,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_477,c_16])).

tff(c_598,plain,(
    ! [A_77] :
      ( k9_relat_1('#skF_2',k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_77))) = k9_relat_1('#skF_2',A_77)
      | ~ r1_tarski(A_77,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_481])).

tff(c_642,plain,(
    ! [A_77,B_7] :
      ( r1_tarski(k9_relat_1('#skF_2',A_77),k9_relat_1('#skF_2',B_7))
      | ~ r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_77)),B_7)
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(A_77,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_10])).

tff(c_37122,plain,(
    ! [A_585,B_586] :
      ( r1_tarski(k9_relat_1('#skF_2',A_585),k9_relat_1('#skF_2',B_586))
      | ~ r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_585)),B_586)
      | ~ r1_tarski(A_585,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_642])).

tff(c_37372,plain,(
    ! [A_587] :
      ( r1_tarski(k9_relat_1('#skF_2',A_587),k9_relat_1('#skF_2',k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_587))))
      | ~ r1_tarski(A_587,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6,c_37122])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] :
      ( r1_tarski(A_16,B_17)
      | ~ v2_funct_1(C_18)
      | ~ r1_tarski(A_16,k1_relat_1(C_18))
      | ~ r1_tarski(k9_relat_1(C_18,A_16),k9_relat_1(C_18,B_17))
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_37485,plain,(
    ! [A_587] :
      ( r1_tarski(A_587,k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_587)))
      | ~ v2_funct_1('#skF_2')
      | ~ r1_tarski(A_587,k1_relat_1('#skF_2'))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(A_587,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_37372,c_20])).

tff(c_37739,plain,(
    ! [A_588] :
      ( r1_tarski(A_588,k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_588)))
      | ~ r1_tarski(A_588,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_588,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_37485])).

tff(c_22,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_112,plain,(
    ! [B_35,A_36] :
      ( r1_tarski(k10_relat_1(B_35,k9_relat_1(B_35,A_36)),A_36)
      | ~ v2_funct_1(B_35)
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_53,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_tarski(A_23,C_24)
      | ~ r1_tarski(B_25,C_24)
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    ! [A_26] :
      ( r1_tarski(A_26,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_26,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_53])).

tff(c_65,plain,(
    ! [A_3,A_26] :
      ( r1_tarski(A_3,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_3,A_26)
      | ~ r1_tarski(A_26,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_60,c_8])).

tff(c_119,plain,(
    ! [B_35,A_36] :
      ( r1_tarski(k10_relat_1(B_35,k9_relat_1(B_35,A_36)),k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_36,'#skF_1')
      | ~ v2_funct_1(B_35)
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(resolution,[status(thm)],[c_112,c_65])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k10_relat_1(B_15,k9_relat_1(B_15,A_14)),A_14)
      | ~ v2_funct_1(B_15)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_212,plain,(
    ! [A_44,A_45,B_46] :
      ( r1_tarski(A_44,A_45)
      | ~ r1_tarski(A_44,k9_relat_1(B_46,k10_relat_1(B_46,A_45)))
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_89,c_8])).

tff(c_236,plain,(
    ! [C_8,A_6,A_45] :
      ( r1_tarski(k9_relat_1(C_8,A_6),A_45)
      | ~ v1_funct_1(C_8)
      | ~ r1_tarski(A_6,k10_relat_1(C_8,A_45))
      | ~ v1_relat_1(C_8) ) ),
    inference(resolution,[status(thm)],[c_10,c_212])).

tff(c_624,plain,(
    ! [A_77,A_45] :
      ( r1_tarski(k9_relat_1('#skF_2',A_77),A_45)
      | ~ v1_funct_1('#skF_2')
      | ~ r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_77)),k10_relat_1('#skF_2',A_45))
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(A_77,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_236])).

tff(c_3075,plain,(
    ! [A_176,A_177] :
      ( r1_tarski(k9_relat_1('#skF_2',A_176),A_177)
      | ~ r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_176)),k10_relat_1('#skF_2',A_177))
      | ~ r1_tarski(A_176,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_624])).

tff(c_3114,plain,(
    ! [A_177] :
      ( r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_177)),A_177)
      | ~ r1_tarski(k10_relat_1('#skF_2',A_177),'#skF_1')
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_3075])).

tff(c_3243,plain,(
    ! [A_180] :
      ( r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_180)),A_180)
      | ~ r1_tarski(k10_relat_1('#skF_2',A_180),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_3114])).

tff(c_3395,plain,(
    ! [A_181,A_182] :
      ( r1_tarski(A_181,A_182)
      | ~ r1_tarski(A_181,k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_182)))
      | ~ r1_tarski(k10_relat_1('#skF_2',A_182),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3243,c_8])).

tff(c_3446,plain,(
    ! [A_6,A_182] :
      ( r1_tarski(k9_relat_1('#skF_2',A_6),A_182)
      | ~ r1_tarski(k10_relat_1('#skF_2',A_182),'#skF_1')
      | ~ r1_tarski(A_6,k10_relat_1('#skF_2',A_182))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_10,c_3395])).

tff(c_3513,plain,(
    ! [A_184,A_185] :
      ( r1_tarski(k9_relat_1('#skF_2',A_184),A_185)
      | ~ r1_tarski(k10_relat_1('#skF_2',A_185),'#skF_1')
      | ~ r1_tarski(A_184,k10_relat_1('#skF_2',A_185)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3446])).

tff(c_3519,plain,(
    ! [A_184] :
      ( r1_tarski(k9_relat_1('#skF_2',A_184),k9_relat_1('#skF_2','#skF_1'))
      | ~ r1_tarski(A_184,k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_3513])).

tff(c_3530,plain,(
    ! [A_186] :
      ( r1_tarski(k9_relat_1('#skF_2',A_186),k9_relat_1('#skF_2','#skF_1'))
      | ~ r1_tarski(A_186,k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_3519])).

tff(c_3555,plain,(
    ! [A_186] :
      ( r1_tarski(A_186,'#skF_1')
      | ~ v2_funct_1('#skF_2')
      | ~ r1_tarski(A_186,k1_relat_1('#skF_2'))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(A_186,k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_3530,c_20])).

tff(c_3990,plain,(
    ! [A_194] :
      ( r1_tarski(A_194,'#skF_1')
      | ~ r1_tarski(A_194,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_194,k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_3555])).

tff(c_4015,plain,
    ( r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')),'#skF_1')
    | ~ r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')),k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_3990])).

tff(c_4153,plain,(
    ~ r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4015])).

tff(c_4156,plain,
    ( ~ r1_tarski('#skF_1','#skF_1')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_119,c_4153])).

tff(c_4163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_6,c_4156])).

tff(c_4164,plain,(
    r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_4015])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4183,plain,
    ( k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_4164,c_2])).

tff(c_4198,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_4183])).

tff(c_37954,plain,
    ( ~ r1_tarski('#skF_1',k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_37739,c_4198])).

tff(c_38188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_26,c_37954])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.88/7.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.88/7.79  
% 15.88/7.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.88/7.80  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 15.88/7.80  
% 15.88/7.80  %Foreground sorts:
% 15.88/7.80  
% 15.88/7.80  
% 15.88/7.80  %Background operators:
% 15.88/7.80  
% 15.88/7.80  
% 15.88/7.80  %Foreground operators:
% 15.88/7.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.88/7.80  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 15.88/7.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.88/7.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.88/7.80  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.88/7.80  tff('#skF_2', type, '#skF_2': $i).
% 15.88/7.80  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 15.88/7.80  tff('#skF_1', type, '#skF_1': $i).
% 15.88/7.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.88/7.80  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 15.88/7.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.88/7.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.88/7.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.88/7.80  
% 15.88/7.81  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.88/7.81  tff(f_92, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 15.88/7.81  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 15.88/7.81  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 15.88/7.81  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 15.88/7.81  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 15.88/7.81  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 15.88/7.81  tff(f_81, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 15.88/7.81  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 15.88/7.81  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.88/7.81  tff(c_26, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.88/7.81  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.88/7.81  tff(c_28, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.88/7.81  tff(c_24, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.88/7.81  tff(c_10, plain, (![C_8, A_6, B_7]: (r1_tarski(k9_relat_1(C_8, A_6), k9_relat_1(C_8, B_7)) | ~r1_tarski(A_6, B_7) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.88/7.81  tff(c_102, plain, (![C_32, A_33, B_34]: (r1_tarski(k9_relat_1(C_32, A_33), k9_relat_1(C_32, B_34)) | ~r1_tarski(A_33, B_34) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.88/7.81  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.88/7.81  tff(c_367, plain, (![A_58, C_59, B_60, A_61]: (r1_tarski(A_58, k9_relat_1(C_59, B_60)) | ~r1_tarski(A_58, k9_relat_1(C_59, A_61)) | ~r1_tarski(A_61, B_60) | ~v1_relat_1(C_59))), inference(resolution, [status(thm)], [c_102, c_8])).
% 15.88/7.81  tff(c_404, plain, (![C_63, A_64, B_65, B_66]: (r1_tarski(k9_relat_1(C_63, A_64), k9_relat_1(C_63, B_65)) | ~r1_tarski(B_66, B_65) | ~r1_tarski(A_64, B_66) | ~v1_relat_1(C_63))), inference(resolution, [status(thm)], [c_10, c_367])).
% 15.88/7.81  tff(c_438, plain, (![C_67, A_68]: (r1_tarski(k9_relat_1(C_67, A_68), k9_relat_1(C_67, k1_relat_1('#skF_2'))) | ~r1_tarski(A_68, '#skF_1') | ~v1_relat_1(C_67))), inference(resolution, [status(thm)], [c_26, c_404])).
% 15.88/7.81  tff(c_12, plain, (![A_9]: (k10_relat_1(A_9, k2_relat_1(A_9))=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.88/7.81  tff(c_89, plain, (![B_30, A_31]: (r1_tarski(k9_relat_1(B_30, k10_relat_1(B_30, A_31)), A_31) | ~v1_funct_1(B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.88/7.81  tff(c_122, plain, (![A_37]: (r1_tarski(k9_relat_1(A_37, k1_relat_1(A_37)), k2_relat_1(A_37)) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37) | ~v1_relat_1(A_37))), inference(superposition, [status(thm), theory('equality')], [c_12, c_89])).
% 15.88/7.81  tff(c_130, plain, (![A_3, A_37]: (r1_tarski(A_3, k2_relat_1(A_37)) | ~r1_tarski(A_3, k9_relat_1(A_37, k1_relat_1(A_37))) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(resolution, [status(thm)], [c_122, c_8])).
% 15.88/7.81  tff(c_449, plain, (![A_68]: (r1_tarski(k9_relat_1('#skF_2', A_68), k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~r1_tarski(A_68, '#skF_1') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_438, c_130])).
% 15.88/7.81  tff(c_477, plain, (![A_69]: (r1_tarski(k9_relat_1('#skF_2', A_69), k2_relat_1('#skF_2')) | ~r1_tarski(A_69, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_449])).
% 15.88/7.81  tff(c_16, plain, (![B_13, A_12]: (k9_relat_1(B_13, k10_relat_1(B_13, A_12))=A_12 | ~r1_tarski(A_12, k2_relat_1(B_13)) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.88/7.81  tff(c_481, plain, (![A_69]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_69)))=k9_relat_1('#skF_2', A_69) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~r1_tarski(A_69, '#skF_1'))), inference(resolution, [status(thm)], [c_477, c_16])).
% 15.88/7.81  tff(c_598, plain, (![A_77]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_77)))=k9_relat_1('#skF_2', A_77) | ~r1_tarski(A_77, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_481])).
% 15.88/7.81  tff(c_642, plain, (![A_77, B_7]: (r1_tarski(k9_relat_1('#skF_2', A_77), k9_relat_1('#skF_2', B_7)) | ~r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_77)), B_7) | ~v1_relat_1('#skF_2') | ~r1_tarski(A_77, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_598, c_10])).
% 15.88/7.81  tff(c_37122, plain, (![A_585, B_586]: (r1_tarski(k9_relat_1('#skF_2', A_585), k9_relat_1('#skF_2', B_586)) | ~r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_585)), B_586) | ~r1_tarski(A_585, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_642])).
% 15.88/7.81  tff(c_37372, plain, (![A_587]: (r1_tarski(k9_relat_1('#skF_2', A_587), k9_relat_1('#skF_2', k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_587)))) | ~r1_tarski(A_587, '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_37122])).
% 15.88/7.81  tff(c_20, plain, (![A_16, B_17, C_18]: (r1_tarski(A_16, B_17) | ~v2_funct_1(C_18) | ~r1_tarski(A_16, k1_relat_1(C_18)) | ~r1_tarski(k9_relat_1(C_18, A_16), k9_relat_1(C_18, B_17)) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_81])).
% 15.88/7.81  tff(c_37485, plain, (![A_587]: (r1_tarski(A_587, k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_587))) | ~v2_funct_1('#skF_2') | ~r1_tarski(A_587, k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~r1_tarski(A_587, '#skF_1'))), inference(resolution, [status(thm)], [c_37372, c_20])).
% 15.88/7.81  tff(c_37739, plain, (![A_588]: (r1_tarski(A_588, k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_588))) | ~r1_tarski(A_588, k1_relat_1('#skF_2')) | ~r1_tarski(A_588, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_37485])).
% 15.88/7.81  tff(c_22, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.88/7.81  tff(c_112, plain, (![B_35, A_36]: (r1_tarski(k10_relat_1(B_35, k9_relat_1(B_35, A_36)), A_36) | ~v2_funct_1(B_35) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.88/7.81  tff(c_53, plain, (![A_23, C_24, B_25]: (r1_tarski(A_23, C_24) | ~r1_tarski(B_25, C_24) | ~r1_tarski(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.88/7.81  tff(c_60, plain, (![A_26]: (r1_tarski(A_26, k1_relat_1('#skF_2')) | ~r1_tarski(A_26, '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_53])).
% 15.88/7.81  tff(c_65, plain, (![A_3, A_26]: (r1_tarski(A_3, k1_relat_1('#skF_2')) | ~r1_tarski(A_3, A_26) | ~r1_tarski(A_26, '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_8])).
% 15.88/7.81  tff(c_119, plain, (![B_35, A_36]: (r1_tarski(k10_relat_1(B_35, k9_relat_1(B_35, A_36)), k1_relat_1('#skF_2')) | ~r1_tarski(A_36, '#skF_1') | ~v2_funct_1(B_35) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35))), inference(resolution, [status(thm)], [c_112, c_65])).
% 15.88/7.81  tff(c_18, plain, (![B_15, A_14]: (r1_tarski(k10_relat_1(B_15, k9_relat_1(B_15, A_14)), A_14) | ~v2_funct_1(B_15) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.88/7.81  tff(c_212, plain, (![A_44, A_45, B_46]: (r1_tarski(A_44, A_45) | ~r1_tarski(A_44, k9_relat_1(B_46, k10_relat_1(B_46, A_45))) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_89, c_8])).
% 15.88/7.81  tff(c_236, plain, (![C_8, A_6, A_45]: (r1_tarski(k9_relat_1(C_8, A_6), A_45) | ~v1_funct_1(C_8) | ~r1_tarski(A_6, k10_relat_1(C_8, A_45)) | ~v1_relat_1(C_8))), inference(resolution, [status(thm)], [c_10, c_212])).
% 15.88/7.81  tff(c_624, plain, (![A_77, A_45]: (r1_tarski(k9_relat_1('#skF_2', A_77), A_45) | ~v1_funct_1('#skF_2') | ~r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_77)), k10_relat_1('#skF_2', A_45)) | ~v1_relat_1('#skF_2') | ~r1_tarski(A_77, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_598, c_236])).
% 15.88/7.81  tff(c_3075, plain, (![A_176, A_177]: (r1_tarski(k9_relat_1('#skF_2', A_176), A_177) | ~r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_176)), k10_relat_1('#skF_2', A_177)) | ~r1_tarski(A_176, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_624])).
% 15.88/7.81  tff(c_3114, plain, (![A_177]: (r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_177)), A_177) | ~r1_tarski(k10_relat_1('#skF_2', A_177), '#skF_1') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_3075])).
% 15.88/7.81  tff(c_3243, plain, (![A_180]: (r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_180)), A_180) | ~r1_tarski(k10_relat_1('#skF_2', A_180), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_3114])).
% 15.88/7.81  tff(c_3395, plain, (![A_181, A_182]: (r1_tarski(A_181, A_182) | ~r1_tarski(A_181, k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_182))) | ~r1_tarski(k10_relat_1('#skF_2', A_182), '#skF_1'))), inference(resolution, [status(thm)], [c_3243, c_8])).
% 15.88/7.81  tff(c_3446, plain, (![A_6, A_182]: (r1_tarski(k9_relat_1('#skF_2', A_6), A_182) | ~r1_tarski(k10_relat_1('#skF_2', A_182), '#skF_1') | ~r1_tarski(A_6, k10_relat_1('#skF_2', A_182)) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_3395])).
% 15.88/7.81  tff(c_3513, plain, (![A_184, A_185]: (r1_tarski(k9_relat_1('#skF_2', A_184), A_185) | ~r1_tarski(k10_relat_1('#skF_2', A_185), '#skF_1') | ~r1_tarski(A_184, k10_relat_1('#skF_2', A_185)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3446])).
% 15.88/7.81  tff(c_3519, plain, (![A_184]: (r1_tarski(k9_relat_1('#skF_2', A_184), k9_relat_1('#skF_2', '#skF_1')) | ~r1_tarski(A_184, k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_3513])).
% 15.88/7.81  tff(c_3530, plain, (![A_186]: (r1_tarski(k9_relat_1('#skF_2', A_186), k9_relat_1('#skF_2', '#skF_1')) | ~r1_tarski(A_186, k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_3519])).
% 15.88/7.81  tff(c_3555, plain, (![A_186]: (r1_tarski(A_186, '#skF_1') | ~v2_funct_1('#skF_2') | ~r1_tarski(A_186, k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~r1_tarski(A_186, k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))))), inference(resolution, [status(thm)], [c_3530, c_20])).
% 15.88/7.81  tff(c_3990, plain, (![A_194]: (r1_tarski(A_194, '#skF_1') | ~r1_tarski(A_194, k1_relat_1('#skF_2')) | ~r1_tarski(A_194, k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_3555])).
% 15.88/7.81  tff(c_4015, plain, (r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')), '#skF_1') | ~r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')), k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_3990])).
% 15.88/7.81  tff(c_4153, plain, (~r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_4015])).
% 15.88/7.81  tff(c_4156, plain, (~r1_tarski('#skF_1', '#skF_1') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_119, c_4153])).
% 15.88/7.81  tff(c_4163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_6, c_4156])).
% 15.88/7.81  tff(c_4164, plain, (r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')), '#skF_1')), inference(splitRight, [status(thm)], [c_4015])).
% 15.88/7.81  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.88/7.81  tff(c_4183, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(resolution, [status(thm)], [c_4164, c_2])).
% 15.88/7.81  tff(c_4198, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_22, c_4183])).
% 15.88/7.81  tff(c_37954, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_2')) | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_37739, c_4198])).
% 15.88/7.81  tff(c_38188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_26, c_37954])).
% 15.88/7.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.88/7.81  
% 15.88/7.81  Inference rules
% 15.88/7.81  ----------------------
% 15.88/7.81  #Ref     : 0
% 15.88/7.81  #Sup     : 8910
% 15.88/7.81  #Fact    : 0
% 15.88/7.81  #Define  : 0
% 15.88/7.81  #Split   : 26
% 15.88/7.81  #Chain   : 0
% 15.88/7.81  #Close   : 0
% 15.88/7.81  
% 15.88/7.81  Ordering : KBO
% 15.88/7.81  
% 15.88/7.81  Simplification rules
% 15.88/7.81  ----------------------
% 15.88/7.81  #Subsume      : 3895
% 15.88/7.81  #Demod        : 6875
% 15.88/7.81  #Tautology    : 751
% 15.88/7.81  #SimpNegUnit  : 11
% 15.88/7.81  #BackRed      : 1
% 15.88/7.81  
% 15.88/7.81  #Partial instantiations: 0
% 15.88/7.81  #Strategies tried      : 1
% 15.88/7.81  
% 15.88/7.81  Timing (in seconds)
% 15.88/7.81  ----------------------
% 15.88/7.82  Preprocessing        : 0.28
% 15.88/7.82  Parsing              : 0.16
% 15.88/7.82  CNF conversion       : 0.02
% 15.88/7.82  Main loop            : 6.77
% 15.88/7.82  Inferencing          : 0.98
% 15.88/7.82  Reduction            : 1.43
% 15.88/7.82  Demodulation         : 0.97
% 15.88/7.82  BG Simplification    : 0.12
% 15.88/7.82  Subsumption          : 3.89
% 15.88/7.82  Abstraction          : 0.22
% 15.88/7.82  MUC search           : 0.00
% 15.88/7.82  Cooper               : 0.00
% 15.88/7.82  Total                : 7.09
% 15.88/7.82  Index Insertion      : 0.00
% 15.88/7.82  Index Deletion       : 0.00
% 15.88/7.82  Index Matching       : 0.00
% 15.88/7.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
