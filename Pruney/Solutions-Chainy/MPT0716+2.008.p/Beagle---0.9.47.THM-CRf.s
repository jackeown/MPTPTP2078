%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:37 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 150 expanded)
%              Number of leaves         :   27 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  154 ( 444 expanded)
%              Number of equality atoms :    3 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_98,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_48,plain,
    ( r1_tarski('#skF_6',k1_relat_1('#skF_4'))
    | ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5'))
    | ~ r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_127,plain,(
    ~ r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_38,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_54,plain,
    ( r1_tarski('#skF_6',k1_relat_1('#skF_4'))
    | r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_71,plain,(
    r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_12,plain,(
    ! [A_12,B_14] :
      ( k10_relat_1(A_12,k1_relat_1(B_14)) = k1_relat_1(k5_relat_1(A_12,B_14))
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_128,plain,(
    ! [D_60,A_61,B_62] :
      ( r2_hidden(D_60,k1_relat_1(A_61))
      | ~ r2_hidden(D_60,k10_relat_1(A_61,B_62))
      | ~ v1_funct_1(A_61)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_261,plain,(
    ! [A_88,B_89,B_90] :
      ( r2_hidden('#skF_1'(k10_relat_1(A_88,B_89),B_90),k1_relat_1(A_88))
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88)
      | r1_tarski(k10_relat_1(A_88,B_89),B_90) ) ),
    inference(resolution,[status(thm)],[c_6,c_128])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_273,plain,(
    ! [A_91,B_92] :
      ( ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91)
      | r1_tarski(k10_relat_1(A_91,B_92),k1_relat_1(A_91)) ) ),
    inference(resolution,[status(thm)],[c_261,c_4])).

tff(c_358,plain,(
    ! [A_101,B_102] :
      ( ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101)
      | r1_tarski(k1_relat_1(k5_relat_1(A_101,B_102)),k1_relat_1(A_101))
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_273])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_421,plain,(
    ! [A_108,A_109,B_110] :
      ( r1_tarski(A_108,k1_relat_1(A_109))
      | ~ r1_tarski(A_108,k1_relat_1(k5_relat_1(A_109,B_110)))
      | ~ v1_funct_1(A_109)
      | ~ v1_relat_1(B_110)
      | ~ v1_relat_1(A_109) ) ),
    inference(resolution,[status(thm)],[c_358,c_8])).

tff(c_446,plain,
    ( r1_tarski('#skF_7',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_71,c_421])).

tff(c_463,plain,(
    r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_40,c_446])).

tff(c_465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_463])).

tff(c_467,plain,(
    r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_10,plain,(
    ! [C_11,A_9,B_10] :
      ( r1_tarski(k9_relat_1(C_11,A_9),k9_relat_1(C_11,B_10))
      | ~ r1_tarski(A_9,B_10)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_79,plain,(
    ! [B_48,A_49] :
      ( r1_tarski(k9_relat_1(B_48,k10_relat_1(B_48,A_49)),A_49)
      | ~ v1_funct_1(B_48)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_530,plain,(
    ! [A_120,A_121,B_122] :
      ( r1_tarski(A_120,A_121)
      | ~ r1_tarski(A_120,k9_relat_1(B_122,k10_relat_1(B_122,A_121)))
      | ~ v1_funct_1(B_122)
      | ~ v1_relat_1(B_122) ) ),
    inference(resolution,[status(thm)],[c_79,c_8])).

tff(c_582,plain,(
    ! [C_129,A_130,A_131] :
      ( r1_tarski(k9_relat_1(C_129,A_130),A_131)
      | ~ v1_funct_1(C_129)
      | ~ r1_tarski(A_130,k10_relat_1(C_129,A_131))
      | ~ v1_relat_1(C_129) ) ),
    inference(resolution,[status(thm)],[c_10,c_530])).

tff(c_466,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5'))
    | r1_tarski('#skF_6',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_482,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_466])).

tff(c_593,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ r1_tarski('#skF_7',k10_relat_1('#skF_4',k1_relat_1('#skF_5')))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_582,c_482])).

tff(c_603,plain,(
    ~ r1_tarski('#skF_7',k10_relat_1('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_593])).

tff(c_608,plain,
    ( ~ r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_603])).

tff(c_611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_71,c_608])).

tff(c_613,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_466])).

tff(c_44,plain,
    ( ~ r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5'))
    | ~ r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_660,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_613,c_44])).

tff(c_612,plain,(
    r1_tarski('#skF_6',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_466])).

tff(c_46,plain,
    ( r1_tarski(k9_relat_1('#skF_4','#skF_6'),k1_relat_1('#skF_5'))
    | ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5'))
    | ~ r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_757,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_613,c_46])).

tff(c_949,plain,(
    ! [A_165,C_166,B_167] :
      ( r1_tarski(A_165,k10_relat_1(C_166,B_167))
      | ~ r1_tarski(k9_relat_1(C_166,A_165),B_167)
      | ~ r1_tarski(A_165,k1_relat_1(C_166))
      | ~ v1_funct_1(C_166)
      | ~ v1_relat_1(C_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_958,plain,
    ( r1_tarski('#skF_6',k10_relat_1('#skF_4',k1_relat_1('#skF_5')))
    | ~ r1_tarski('#skF_6',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_757,c_949])).

tff(c_993,plain,(
    r1_tarski('#skF_6',k10_relat_1('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_612,c_958])).

tff(c_1019,plain,
    ( r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_993])).

tff(c_1030,plain,(
    r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_1019])).

tff(c_1032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_660,c_1030])).

tff(c_1034,plain,(
    ~ r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_50,plain,
    ( ~ r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1089,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1034,c_50])).

tff(c_1033,plain,(
    r1_tarski('#skF_6',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,
    ( r1_tarski(k9_relat_1('#skF_4','#skF_6'),k1_relat_1('#skF_5'))
    | r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1038,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_1034,c_52])).

tff(c_1670,plain,(
    ! [A_259,C_260,B_261] :
      ( r1_tarski(A_259,k10_relat_1(C_260,B_261))
      | ~ r1_tarski(k9_relat_1(C_260,A_259),B_261)
      | ~ r1_tarski(A_259,k1_relat_1(C_260))
      | ~ v1_funct_1(C_260)
      | ~ v1_relat_1(C_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1707,plain,
    ( r1_tarski('#skF_6',k10_relat_1('#skF_4',k1_relat_1('#skF_5')))
    | ~ r1_tarski('#skF_6',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1038,c_1670])).

tff(c_1728,plain,(
    r1_tarski('#skF_6',k10_relat_1('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1033,c_1707])).

tff(c_1747,plain,
    ( r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1728])).

tff(c_1759,plain,(
    r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_1747])).

tff(c_1761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1089,c_1759])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:34:44 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.02/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.02/1.69  
% 4.02/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.02/1.69  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.02/1.69  
% 4.02/1.69  %Foreground sorts:
% 4.02/1.69  
% 4.02/1.69  
% 4.02/1.69  %Background operators:
% 4.02/1.69  
% 4.02/1.69  
% 4.02/1.69  %Foreground operators:
% 4.02/1.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.02/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.02/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.02/1.69  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.02/1.69  tff('#skF_7', type, '#skF_7': $i).
% 4.02/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.02/1.69  tff('#skF_5', type, '#skF_5': $i).
% 4.02/1.69  tff('#skF_6', type, '#skF_6': $i).
% 4.02/1.69  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.02/1.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.02/1.69  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.02/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.02/1.69  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.02/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.02/1.69  tff('#skF_4', type, '#skF_4': $i).
% 4.02/1.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.02/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.02/1.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.02/1.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.02/1.69  
% 4.02/1.71  tff(f_98, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 4.02/1.71  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 4.02/1.71  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.02/1.71  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_funct_1)).
% 4.02/1.71  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.02/1.71  tff(f_44, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 4.02/1.71  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 4.02/1.71  tff(f_81, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 4.02/1.71  tff(c_48, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_4')) | ~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5')) | ~r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.02/1.71  tff(c_127, plain, (~r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_48])).
% 4.02/1.71  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.02/1.71  tff(c_38, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.02/1.71  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.02/1.71  tff(c_54, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_4')) | r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.02/1.71  tff(c_71, plain, (r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_54])).
% 4.02/1.71  tff(c_12, plain, (![A_12, B_14]: (k10_relat_1(A_12, k1_relat_1(B_14))=k1_relat_1(k5_relat_1(A_12, B_14)) | ~v1_relat_1(B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.02/1.71  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.02/1.71  tff(c_128, plain, (![D_60, A_61, B_62]: (r2_hidden(D_60, k1_relat_1(A_61)) | ~r2_hidden(D_60, k10_relat_1(A_61, B_62)) | ~v1_funct_1(A_61) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.02/1.71  tff(c_261, plain, (![A_88, B_89, B_90]: (r2_hidden('#skF_1'(k10_relat_1(A_88, B_89), B_90), k1_relat_1(A_88)) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88) | r1_tarski(k10_relat_1(A_88, B_89), B_90))), inference(resolution, [status(thm)], [c_6, c_128])).
% 4.02/1.71  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.02/1.71  tff(c_273, plain, (![A_91, B_92]: (~v1_funct_1(A_91) | ~v1_relat_1(A_91) | r1_tarski(k10_relat_1(A_91, B_92), k1_relat_1(A_91)))), inference(resolution, [status(thm)], [c_261, c_4])).
% 4.02/1.71  tff(c_358, plain, (![A_101, B_102]: (~v1_funct_1(A_101) | ~v1_relat_1(A_101) | r1_tarski(k1_relat_1(k5_relat_1(A_101, B_102)), k1_relat_1(A_101)) | ~v1_relat_1(B_102) | ~v1_relat_1(A_101))), inference(superposition, [status(thm), theory('equality')], [c_12, c_273])).
% 4.02/1.71  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.02/1.71  tff(c_421, plain, (![A_108, A_109, B_110]: (r1_tarski(A_108, k1_relat_1(A_109)) | ~r1_tarski(A_108, k1_relat_1(k5_relat_1(A_109, B_110))) | ~v1_funct_1(A_109) | ~v1_relat_1(B_110) | ~v1_relat_1(A_109))), inference(resolution, [status(thm)], [c_358, c_8])).
% 4.02/1.71  tff(c_446, plain, (r1_tarski('#skF_7', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_71, c_421])).
% 4.02/1.71  tff(c_463, plain, (r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_40, c_446])).
% 4.02/1.71  tff(c_465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_463])).
% 4.02/1.71  tff(c_467, plain, (r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_48])).
% 4.02/1.71  tff(c_10, plain, (![C_11, A_9, B_10]: (r1_tarski(k9_relat_1(C_11, A_9), k9_relat_1(C_11, B_10)) | ~r1_tarski(A_9, B_10) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.02/1.71  tff(c_79, plain, (![B_48, A_49]: (r1_tarski(k9_relat_1(B_48, k10_relat_1(B_48, A_49)), A_49) | ~v1_funct_1(B_48) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.02/1.71  tff(c_530, plain, (![A_120, A_121, B_122]: (r1_tarski(A_120, A_121) | ~r1_tarski(A_120, k9_relat_1(B_122, k10_relat_1(B_122, A_121))) | ~v1_funct_1(B_122) | ~v1_relat_1(B_122))), inference(resolution, [status(thm)], [c_79, c_8])).
% 4.02/1.71  tff(c_582, plain, (![C_129, A_130, A_131]: (r1_tarski(k9_relat_1(C_129, A_130), A_131) | ~v1_funct_1(C_129) | ~r1_tarski(A_130, k10_relat_1(C_129, A_131)) | ~v1_relat_1(C_129))), inference(resolution, [status(thm)], [c_10, c_530])).
% 4.02/1.71  tff(c_466, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5')) | r1_tarski('#skF_6', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_48])).
% 4.02/1.71  tff(c_482, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_466])).
% 4.02/1.71  tff(c_593, plain, (~v1_funct_1('#skF_4') | ~r1_tarski('#skF_7', k10_relat_1('#skF_4', k1_relat_1('#skF_5'))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_582, c_482])).
% 4.02/1.71  tff(c_603, plain, (~r1_tarski('#skF_7', k10_relat_1('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_593])).
% 4.02/1.71  tff(c_608, plain, (~r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12, c_603])).
% 4.02/1.71  tff(c_611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_71, c_608])).
% 4.02/1.71  tff(c_613, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_466])).
% 4.02/1.71  tff(c_44, plain, (~r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5')) | ~r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.02/1.71  tff(c_660, plain, (~r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_467, c_613, c_44])).
% 4.02/1.71  tff(c_612, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_466])).
% 4.02/1.71  tff(c_46, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5')) | ~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5')) | ~r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.02/1.71  tff(c_757, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_467, c_613, c_46])).
% 4.02/1.71  tff(c_949, plain, (![A_165, C_166, B_167]: (r1_tarski(A_165, k10_relat_1(C_166, B_167)) | ~r1_tarski(k9_relat_1(C_166, A_165), B_167) | ~r1_tarski(A_165, k1_relat_1(C_166)) | ~v1_funct_1(C_166) | ~v1_relat_1(C_166))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.02/1.71  tff(c_958, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_4', k1_relat_1('#skF_5'))) | ~r1_tarski('#skF_6', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_757, c_949])).
% 4.02/1.71  tff(c_993, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_612, c_958])).
% 4.02/1.71  tff(c_1019, plain, (r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12, c_993])).
% 4.02/1.71  tff(c_1030, plain, (r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_1019])).
% 4.02/1.71  tff(c_1032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_660, c_1030])).
% 4.02/1.71  tff(c_1034, plain, (~r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_54])).
% 4.02/1.71  tff(c_50, plain, (~r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.02/1.71  tff(c_1089, plain, (~r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_1034, c_50])).
% 4.02/1.71  tff(c_1033, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_54])).
% 4.02/1.71  tff(c_52, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5')) | r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.02/1.71  tff(c_1038, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_1034, c_52])).
% 4.02/1.71  tff(c_1670, plain, (![A_259, C_260, B_261]: (r1_tarski(A_259, k10_relat_1(C_260, B_261)) | ~r1_tarski(k9_relat_1(C_260, A_259), B_261) | ~r1_tarski(A_259, k1_relat_1(C_260)) | ~v1_funct_1(C_260) | ~v1_relat_1(C_260))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.02/1.71  tff(c_1707, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_4', k1_relat_1('#skF_5'))) | ~r1_tarski('#skF_6', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1038, c_1670])).
% 4.02/1.71  tff(c_1728, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1033, c_1707])).
% 4.02/1.71  tff(c_1747, plain, (r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12, c_1728])).
% 4.02/1.71  tff(c_1759, plain, (r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_1747])).
% 4.02/1.71  tff(c_1761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1089, c_1759])).
% 4.02/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.02/1.71  
% 4.02/1.71  Inference rules
% 4.02/1.71  ----------------------
% 4.02/1.71  #Ref     : 0
% 4.02/1.71  #Sup     : 430
% 4.02/1.71  #Fact    : 0
% 4.02/1.71  #Define  : 0
% 4.02/1.71  #Split   : 7
% 4.02/1.71  #Chain   : 0
% 4.02/1.71  #Close   : 0
% 4.02/1.71  
% 4.02/1.71  Ordering : KBO
% 4.02/1.71  
% 4.02/1.71  Simplification rules
% 4.02/1.71  ----------------------
% 4.02/1.71  #Subsume      : 94
% 4.02/1.71  #Demod        : 75
% 4.02/1.71  #Tautology    : 36
% 4.02/1.71  #SimpNegUnit  : 7
% 4.02/1.71  #BackRed      : 0
% 4.02/1.71  
% 4.02/1.71  #Partial instantiations: 0
% 4.02/1.71  #Strategies tried      : 1
% 4.02/1.71  
% 4.02/1.71  Timing (in seconds)
% 4.02/1.71  ----------------------
% 4.02/1.71  Preprocessing        : 0.32
% 4.02/1.71  Parsing              : 0.16
% 4.02/1.71  CNF conversion       : 0.03
% 4.02/1.71  Main loop            : 0.60
% 4.02/1.71  Inferencing          : 0.20
% 4.02/1.71  Reduction            : 0.17
% 4.02/1.71  Demodulation         : 0.11
% 4.02/1.71  BG Simplification    : 0.03
% 4.02/1.71  Subsumption          : 0.17
% 4.02/1.71  Abstraction          : 0.03
% 4.02/1.71  MUC search           : 0.00
% 4.02/1.71  Cooper               : 0.00
% 4.02/1.71  Total                : 0.96
% 4.02/1.71  Index Insertion      : 0.00
% 4.02/1.71  Index Deletion       : 0.00
% 4.02/1.71  Index Matching       : 0.00
% 4.02/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
