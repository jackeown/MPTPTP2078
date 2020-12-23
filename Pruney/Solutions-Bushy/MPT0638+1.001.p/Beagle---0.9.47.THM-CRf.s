%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0638+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:37 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 172 expanded)
%              Number of leaves         :   22 (  76 expanded)
%              Depth                    :   16
%              Number of atoms          :  111 ( 606 expanded)
%              Number of equality atoms :   35 ( 228 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( k2_relat_1(A) = k1_relat_1(B)
                & k5_relat_1(A,B) = A )
             => B = k6_relat_1(k1_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_39,axiom,(
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

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_30,plain,(
    k6_relat_1(k1_relat_1('#skF_7')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    ! [B_46] :
      ( r2_hidden('#skF_5'(k1_relat_1(B_46),B_46),k1_relat_1(B_46))
      | k6_relat_1(k1_relat_1(B_46)) = B_46
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    k2_relat_1('#skF_6') = k1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_61,plain,(
    ! [A_58,C_59] :
      ( k1_funct_1(A_58,'#skF_4'(A_58,k2_relat_1(A_58),C_59)) = C_59
      | ~ r2_hidden(C_59,k2_relat_1(A_58))
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_77,plain,(
    ! [C_59] :
      ( k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_59)) = C_59
      | ~ r2_hidden(C_59,k2_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_61])).

tff(c_83,plain,(
    ! [C_59] :
      ( k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_59)) = C_59
      | ~ r2_hidden(C_59,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_34,c_77])).

tff(c_32,plain,(
    k5_relat_1('#skF_6','#skF_7') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_101,plain,(
    ! [A_61,C_62] :
      ( r2_hidden('#skF_4'(A_61,k2_relat_1(A_61),C_62),k1_relat_1(A_61))
      | ~ r2_hidden(C_62,k2_relat_1(A_61))
      | ~ v1_funct_1(A_61)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_104,plain,(
    ! [C_62] :
      ( r2_hidden('#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_62),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_62,k2_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_101])).

tff(c_106,plain,(
    ! [C_62] :
      ( r2_hidden('#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_62),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_62,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_34,c_104])).

tff(c_125,plain,(
    ! [B_71,C_72,A_73] :
      ( k1_funct_1(k5_relat_1(B_71,C_72),A_73) = k1_funct_1(C_72,k1_funct_1(B_71,A_73))
      | ~ r2_hidden(A_73,k1_relat_1(B_71))
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72)
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_135,plain,(
    ! [C_72,C_62] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_72),'#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_62)) = k1_funct_1(C_72,k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_62)))
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(C_62,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_106,c_125])).

tff(c_309,plain,(
    ! [C_96,C_97] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_96),'#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_97)) = k1_funct_1(C_96,k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_97)))
      | ~ v1_funct_1(C_96)
      | ~ v1_relat_1(C_96)
      | ~ r2_hidden(C_97,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_135])).

tff(c_325,plain,(
    ! [C_97] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_97))) = k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_97))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_97,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_309])).

tff(c_330,plain,(
    ! [C_98] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_98))) = k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_98))
      | ~ r2_hidden(C_98,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_325])).

tff(c_358,plain,(
    ! [C_99] :
      ( k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_99)) = k1_funct_1('#skF_7',C_99)
      | ~ r2_hidden(C_99,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_99,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_330])).

tff(c_419,plain,(
    ! [C_102] :
      ( k1_funct_1('#skF_7',C_102) = C_102
      | ~ r2_hidden(C_102,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_102,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_102,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_83])).

tff(c_445,plain,
    ( k1_funct_1('#skF_7','#skF_5'(k1_relat_1('#skF_7'),'#skF_7')) = '#skF_5'(k1_relat_1('#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_5'(k1_relat_1('#skF_7'),'#skF_7'),k1_relat_1('#skF_7'))
    | k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_419])).

tff(c_463,plain,
    ( k1_funct_1('#skF_7','#skF_5'(k1_relat_1('#skF_7'),'#skF_7')) = '#skF_5'(k1_relat_1('#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_5'(k1_relat_1('#skF_7'),'#skF_7'),k1_relat_1('#skF_7'))
    | k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_445])).

tff(c_464,plain,
    ( k1_funct_1('#skF_7','#skF_5'(k1_relat_1('#skF_7'),'#skF_7')) = '#skF_5'(k1_relat_1('#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_5'(k1_relat_1('#skF_7'),'#skF_7'),k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_463])).

tff(c_466,plain,(
    ~ r2_hidden('#skF_5'(k1_relat_1('#skF_7'),'#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_464])).

tff(c_469,plain,
    ( k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_466])).

tff(c_472,plain,(
    k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_469])).

tff(c_474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_472])).

tff(c_475,plain,(
    k1_funct_1('#skF_7','#skF_5'(k1_relat_1('#skF_7'),'#skF_7')) = '#skF_5'(k1_relat_1('#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_464])).

tff(c_22,plain,(
    ! [B_46] :
      ( k1_funct_1(B_46,'#skF_5'(k1_relat_1(B_46),B_46)) != '#skF_5'(k1_relat_1(B_46),B_46)
      | k6_relat_1(k1_relat_1(B_46)) = B_46
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_494,plain,
    ( k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_22])).

tff(c_506,plain,(
    k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_494])).

tff(c_508,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_506])).

%------------------------------------------------------------------------------
