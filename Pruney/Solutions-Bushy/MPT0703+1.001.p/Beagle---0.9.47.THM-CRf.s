%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0703+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:44 EST 2020

% Result     : Theorem 29.32s
% Output     : CNFRefutation 29.32s
% Verified   : 
% Statistics : Number of formulae       :   59 (  91 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  136 ( 243 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_1 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

tff(c_44,plain,(
    ~ r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_3'(A_60,B_61),A_60)
      | r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden('#skF_3'(A_13,B_14),B_14)
      | r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_59,plain,(
    ! [A_60] : r1_tarski(A_60,A_60) ),
    inference(resolution,[status(thm)],[c_54,c_22])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),A_13)
      | r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    r1_tarski('#skF_8',k2_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_61,plain,(
    ! [C_63,B_64,A_65] :
      ( r2_hidden(C_63,B_64)
      | ~ r2_hidden(C_63,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_71,plain,(
    ! [A_69,B_70,B_71] :
      ( r2_hidden('#skF_3'(A_69,B_70),B_71)
      | ~ r1_tarski(A_69,B_71)
      | r1_tarski(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_24,c_61])).

tff(c_20,plain,(
    ! [C_17,B_14,A_13] :
      ( r2_hidden(C_17,B_14)
      | ~ r2_hidden(C_17,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_98,plain,(
    ! [A_77,B_78,B_79,B_80] :
      ( r2_hidden('#skF_3'(A_77,B_78),B_79)
      | ~ r1_tarski(B_80,B_79)
      | ~ r1_tarski(A_77,B_80)
      | r1_tarski(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_71,c_20])).

tff(c_107,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_3'(A_77,B_78),k2_relat_1('#skF_10'))
      | ~ r1_tarski(A_77,'#skF_8')
      | r1_tarski(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_46,c_98])).

tff(c_52,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_50,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_117,plain,(
    ! [A_83,C_84] :
      ( r2_hidden('#skF_7'(A_83,k2_relat_1(A_83),C_84),k1_relat_1(A_83))
      | ~ r2_hidden(C_84,k2_relat_1(A_83))
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_120,plain,(
    ! [A_83,C_84,B_14] :
      ( r2_hidden('#skF_7'(A_83,k2_relat_1(A_83),C_84),B_14)
      | ~ r1_tarski(k1_relat_1(A_83),B_14)
      | ~ r2_hidden(C_84,k2_relat_1(A_83))
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(resolution,[status(thm)],[c_117,c_20])).

tff(c_48,plain,(
    r1_tarski(k10_relat_1('#skF_10','#skF_8'),k10_relat_1('#skF_10','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28,plain,(
    ! [A_18,C_54] :
      ( k1_funct_1(A_18,'#skF_7'(A_18,k2_relat_1(A_18),C_54)) = C_54
      | ~ r2_hidden(C_54,k2_relat_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_261,plain,(
    ! [D_110,A_111,B_112] :
      ( r2_hidden(D_110,k10_relat_1(A_111,B_112))
      | ~ r2_hidden(k1_funct_1(A_111,D_110),B_112)
      | ~ r2_hidden(D_110,k1_relat_1(A_111))
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9268,plain,(
    ! [A_613,C_614,B_615] :
      ( r2_hidden('#skF_7'(A_613,k2_relat_1(A_613),C_614),k10_relat_1(A_613,B_615))
      | ~ r2_hidden(C_614,B_615)
      | ~ r2_hidden('#skF_7'(A_613,k2_relat_1(A_613),C_614),k1_relat_1(A_613))
      | ~ v1_funct_1(A_613)
      | ~ v1_relat_1(A_613)
      | ~ r2_hidden(C_614,k2_relat_1(A_613))
      | ~ v1_funct_1(A_613)
      | ~ v1_relat_1(A_613) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_261])).

tff(c_41471,plain,(
    ! [A_1466,C_1467,B_1468,B_1469] :
      ( r2_hidden('#skF_7'(A_1466,k2_relat_1(A_1466),C_1467),B_1468)
      | ~ r1_tarski(k10_relat_1(A_1466,B_1469),B_1468)
      | ~ r2_hidden(C_1467,B_1469)
      | ~ r2_hidden('#skF_7'(A_1466,k2_relat_1(A_1466),C_1467),k1_relat_1(A_1466))
      | ~ r2_hidden(C_1467,k2_relat_1(A_1466))
      | ~ v1_funct_1(A_1466)
      | ~ v1_relat_1(A_1466) ) ),
    inference(resolution,[status(thm)],[c_9268,c_20])).

tff(c_41556,plain,(
    ! [C_1467] :
      ( r2_hidden('#skF_7'('#skF_10',k2_relat_1('#skF_10'),C_1467),k10_relat_1('#skF_10','#skF_9'))
      | ~ r2_hidden(C_1467,'#skF_8')
      | ~ r2_hidden('#skF_7'('#skF_10',k2_relat_1('#skF_10'),C_1467),k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_1467,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_48,c_41471])).

tff(c_41677,plain,(
    ! [C_1471] :
      ( r2_hidden('#skF_7'('#skF_10',k2_relat_1('#skF_10'),C_1471),k10_relat_1('#skF_10','#skF_9'))
      | ~ r2_hidden(C_1471,'#skF_8')
      | ~ r2_hidden('#skF_7'('#skF_10',k2_relat_1('#skF_10'),C_1471),k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_1471,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_41556])).

tff(c_190,plain,(
    ! [A_97,C_98] :
      ( k1_funct_1(A_97,'#skF_7'(A_97,k2_relat_1(A_97),C_98)) = C_98
      | ~ r2_hidden(C_98,k2_relat_1(A_97))
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [A_1,D_12,B_8] :
      ( r2_hidden(k1_funct_1(A_1,D_12),B_8)
      | ~ r2_hidden(D_12,k10_relat_1(A_1,B_8))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_199,plain,(
    ! [C_98,B_8,A_97] :
      ( r2_hidden(C_98,B_8)
      | ~ r2_hidden('#skF_7'(A_97,k2_relat_1(A_97),C_98),k10_relat_1(A_97,B_8))
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97)
      | ~ r2_hidden(C_98,k2_relat_1(A_97))
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_4])).

tff(c_41686,plain,(
    ! [C_1471] :
      ( r2_hidden(C_1471,'#skF_9')
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(C_1471,'#skF_8')
      | ~ r2_hidden('#skF_7'('#skF_10',k2_relat_1('#skF_10'),C_1471),k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_1471,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_41677,c_199])).

tff(c_42064,plain,(
    ! [C_1477] :
      ( r2_hidden(C_1477,'#skF_9')
      | ~ r2_hidden(C_1477,'#skF_8')
      | ~ r2_hidden('#skF_7'('#skF_10',k2_relat_1('#skF_10'),C_1477),k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_1477,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_41686])).

tff(c_42088,plain,(
    ! [C_84] :
      ( r2_hidden(C_84,'#skF_9')
      | ~ r2_hidden(C_84,'#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_10'),k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_84,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_120,c_42064])).

tff(c_42343,plain,(
    ! [C_1482] :
      ( r2_hidden(C_1482,'#skF_9')
      | ~ r2_hidden(C_1482,'#skF_8')
      | ~ r2_hidden(C_1482,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_59,c_42088])).

tff(c_42994,plain,(
    ! [A_1483,B_1484] :
      ( r2_hidden('#skF_3'(A_1483,B_1484),'#skF_9')
      | ~ r2_hidden('#skF_3'(A_1483,B_1484),'#skF_8')
      | ~ r1_tarski(A_1483,'#skF_8')
      | r1_tarski(A_1483,B_1484) ) ),
    inference(resolution,[status(thm)],[c_107,c_42343])).

tff(c_43076,plain,(
    ! [A_1485] :
      ( ~ r2_hidden('#skF_3'(A_1485,'#skF_9'),'#skF_8')
      | ~ r1_tarski(A_1485,'#skF_8')
      | r1_tarski(A_1485,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_42994,c_22])).

tff(c_43132,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_24,c_43076])).

tff(c_43151,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_43132])).

tff(c_43153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_43151])).

%------------------------------------------------------------------------------
