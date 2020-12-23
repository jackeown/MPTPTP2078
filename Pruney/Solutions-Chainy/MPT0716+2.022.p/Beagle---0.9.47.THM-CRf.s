%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:39 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 142 expanded)
%              Number of leaves         :   23 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  134 ( 405 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_81,negated_conjecture,(
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

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_28,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_116,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_78,plain,(
    ! [A_38,B_39] :
      ( k10_relat_1(A_38,k1_relat_1(B_39)) = k1_relat_1(k5_relat_1(A_38,B_39))
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k10_relat_1(B_10,A_9),k1_relat_1(B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_117,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_45,B_46)),k1_relat_1(A_45))
      | ~ v1_relat_1(A_45)
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_8])).

tff(c_34,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_46,plain,(
    k2_xboole_0('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) = k1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    ! [C_3] :
      ( r1_tarski('#skF_4',C_3)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),C_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2])).

tff(c_123,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_117,c_63])).

tff(c_130,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_123])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_130])).

tff(c_134,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_133,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_147,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_20,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k9_relat_1(B_15,k10_relat_1(B_15,A_14)),A_14)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_311,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k9_relat_1(A_78,k1_relat_1(k5_relat_1(A_78,B_79))),k1_relat_1(B_79))
      | ~ v1_funct_1(A_78)
      | ~ v1_relat_1(A_78)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_12])).

tff(c_177,plain,(
    ! [C_52,A_53,B_54] :
      ( k2_xboole_0(k9_relat_1(C_52,A_53),k9_relat_1(C_52,B_54)) = k9_relat_1(C_52,k2_xboole_0(A_53,B_54))
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_197,plain,(
    ! [C_55,A_56,C_57,B_58] :
      ( r1_tarski(k9_relat_1(C_55,A_56),C_57)
      | ~ r1_tarski(k9_relat_1(C_55,k2_xboole_0(A_56,B_58)),C_57)
      | ~ v1_relat_1(C_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_2])).

tff(c_212,plain,(
    ! [C_55,C_57] :
      ( r1_tarski(k9_relat_1(C_55,'#skF_4'),C_57)
      | ~ r1_tarski(k9_relat_1(C_55,k1_relat_1(k5_relat_1('#skF_1','#skF_2'))),C_57)
      | ~ v1_relat_1(C_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_197])).

tff(c_318,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_311,c_212])).

tff(c_325,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_20,c_318])).

tff(c_327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_325])).

tff(c_329,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_24,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_399,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_329,c_24])).

tff(c_10,plain,(
    ! [A_11,B_13] :
      ( k10_relat_1(A_11,k1_relat_1(B_13)) = k1_relat_1(k5_relat_1(A_11,B_13))
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_328,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_26,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_374,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_329,c_26])).

tff(c_485,plain,(
    ! [A_108,C_109,B_110] :
      ( r1_tarski(A_108,k10_relat_1(C_109,B_110))
      | ~ r1_tarski(k9_relat_1(C_109,A_108),B_110)
      | ~ r1_tarski(A_108,k1_relat_1(C_109))
      | ~ v1_funct_1(C_109)
      | ~ v1_relat_1(C_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_500,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_374,c_485])).

tff(c_517,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_328,c_500])).

tff(c_527,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_517])).

tff(c_530,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_527])).

tff(c_532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_399,c_530])).

tff(c_534,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_30,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_587,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_534,c_30])).

tff(c_533,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_32,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_539,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_534,c_32])).

tff(c_773,plain,(
    ! [A_159,C_160,B_161] :
      ( r1_tarski(A_159,k10_relat_1(C_160,B_161))
      | ~ r1_tarski(k9_relat_1(C_160,A_159),B_161)
      | ~ r1_tarski(A_159,k1_relat_1(C_160))
      | ~ v1_funct_1(C_160)
      | ~ v1_relat_1(C_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_791,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_539,c_773])).

tff(c_801,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_533,c_791])).

tff(c_807,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_801])).

tff(c_810,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_807])).

tff(c_812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_587,c_810])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:08:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.63  
% 3.14/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.63  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.14/1.63  
% 3.14/1.63  %Foreground sorts:
% 3.14/1.63  
% 3.14/1.63  
% 3.14/1.63  %Background operators:
% 3.14/1.63  
% 3.14/1.63  
% 3.14/1.63  %Foreground operators:
% 3.14/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.14/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.14/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.63  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.14/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.14/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.63  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.14/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.14/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.14/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.14/1.64  
% 3.14/1.65  tff(f_81, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 3.14/1.65  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.14/1.65  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 3.14/1.65  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.14/1.65  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.14/1.65  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 3.14/1.65  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_relat_1)).
% 3.14/1.65  tff(f_64, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 3.14/1.65  tff(c_28, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.14/1.65  tff(c_116, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_28])).
% 3.14/1.65  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.14/1.65  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.14/1.65  tff(c_78, plain, (![A_38, B_39]: (k10_relat_1(A_38, k1_relat_1(B_39))=k1_relat_1(k5_relat_1(A_38, B_39)) | ~v1_relat_1(B_39) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.14/1.65  tff(c_8, plain, (![B_10, A_9]: (r1_tarski(k10_relat_1(B_10, A_9), k1_relat_1(B_10)) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.14/1.65  tff(c_117, plain, (![A_45, B_46]: (r1_tarski(k1_relat_1(k5_relat_1(A_45, B_46)), k1_relat_1(A_45)) | ~v1_relat_1(A_45) | ~v1_relat_1(B_46) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_78, c_8])).
% 3.14/1.65  tff(c_34, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.14/1.65  tff(c_42, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_34])).
% 3.14/1.65  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.14/1.65  tff(c_46, plain, (k2_xboole_0('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))=k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_4])).
% 3.14/1.65  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.14/1.65  tff(c_63, plain, (![C_3]: (r1_tarski('#skF_4', C_3) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), C_3))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2])).
% 3.14/1.65  tff(c_123, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_117, c_63])).
% 3.14/1.65  tff(c_130, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_123])).
% 3.14/1.65  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_130])).
% 3.14/1.65  tff(c_134, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_28])).
% 3.14/1.65  tff(c_133, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_28])).
% 3.14/1.65  tff(c_147, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_133])).
% 3.14/1.65  tff(c_20, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.14/1.65  tff(c_12, plain, (![B_15, A_14]: (r1_tarski(k9_relat_1(B_15, k10_relat_1(B_15, A_14)), A_14) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.14/1.65  tff(c_311, plain, (![A_78, B_79]: (r1_tarski(k9_relat_1(A_78, k1_relat_1(k5_relat_1(A_78, B_79))), k1_relat_1(B_79)) | ~v1_funct_1(A_78) | ~v1_relat_1(A_78) | ~v1_relat_1(B_79) | ~v1_relat_1(A_78))), inference(superposition, [status(thm), theory('equality')], [c_78, c_12])).
% 3.14/1.65  tff(c_177, plain, (![C_52, A_53, B_54]: (k2_xboole_0(k9_relat_1(C_52, A_53), k9_relat_1(C_52, B_54))=k9_relat_1(C_52, k2_xboole_0(A_53, B_54)) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.14/1.65  tff(c_197, plain, (![C_55, A_56, C_57, B_58]: (r1_tarski(k9_relat_1(C_55, A_56), C_57) | ~r1_tarski(k9_relat_1(C_55, k2_xboole_0(A_56, B_58)), C_57) | ~v1_relat_1(C_55))), inference(superposition, [status(thm), theory('equality')], [c_177, c_2])).
% 3.14/1.65  tff(c_212, plain, (![C_55, C_57]: (r1_tarski(k9_relat_1(C_55, '#skF_4'), C_57) | ~r1_tarski(k9_relat_1(C_55, k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), C_57) | ~v1_relat_1(C_55))), inference(superposition, [status(thm), theory('equality')], [c_46, c_197])).
% 3.14/1.65  tff(c_318, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_311, c_212])).
% 3.14/1.65  tff(c_325, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_20, c_318])).
% 3.14/1.65  tff(c_327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_325])).
% 3.14/1.65  tff(c_329, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_133])).
% 3.14/1.65  tff(c_24, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.14/1.65  tff(c_399, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_329, c_24])).
% 3.14/1.65  tff(c_10, plain, (![A_11, B_13]: (k10_relat_1(A_11, k1_relat_1(B_13))=k1_relat_1(k5_relat_1(A_11, B_13)) | ~v1_relat_1(B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.14/1.65  tff(c_328, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_133])).
% 3.14/1.65  tff(c_26, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.14/1.65  tff(c_374, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_329, c_26])).
% 3.14/1.65  tff(c_485, plain, (![A_108, C_109, B_110]: (r1_tarski(A_108, k10_relat_1(C_109, B_110)) | ~r1_tarski(k9_relat_1(C_109, A_108), B_110) | ~r1_tarski(A_108, k1_relat_1(C_109)) | ~v1_funct_1(C_109) | ~v1_relat_1(C_109))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.14/1.65  tff(c_500, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_374, c_485])).
% 3.14/1.65  tff(c_517, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_328, c_500])).
% 3.14/1.65  tff(c_527, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10, c_517])).
% 3.14/1.65  tff(c_530, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_527])).
% 3.14/1.65  tff(c_532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_399, c_530])).
% 3.14/1.65  tff(c_534, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_34])).
% 3.14/1.65  tff(c_30, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.14/1.65  tff(c_587, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_534, c_30])).
% 3.14/1.65  tff(c_533, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_34])).
% 3.14/1.65  tff(c_32, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.14/1.65  tff(c_539, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_534, c_32])).
% 3.14/1.65  tff(c_773, plain, (![A_159, C_160, B_161]: (r1_tarski(A_159, k10_relat_1(C_160, B_161)) | ~r1_tarski(k9_relat_1(C_160, A_159), B_161) | ~r1_tarski(A_159, k1_relat_1(C_160)) | ~v1_funct_1(C_160) | ~v1_relat_1(C_160))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.14/1.65  tff(c_791, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_539, c_773])).
% 3.14/1.65  tff(c_801, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_533, c_791])).
% 3.14/1.65  tff(c_807, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10, c_801])).
% 3.14/1.65  tff(c_810, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_807])).
% 3.14/1.65  tff(c_812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_587, c_810])).
% 3.14/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.65  
% 3.14/1.65  Inference rules
% 3.14/1.65  ----------------------
% 3.14/1.65  #Ref     : 0
% 3.14/1.65  #Sup     : 187
% 3.14/1.65  #Fact    : 0
% 3.14/1.65  #Define  : 0
% 3.14/1.65  #Split   : 3
% 3.14/1.65  #Chain   : 0
% 3.14/1.65  #Close   : 0
% 3.14/1.65  
% 3.14/1.65  Ordering : KBO
% 3.14/1.65  
% 3.14/1.65  Simplification rules
% 3.14/1.65  ----------------------
% 3.14/1.65  #Subsume      : 10
% 3.14/1.65  #Demod        : 47
% 3.14/1.65  #Tautology    : 60
% 3.14/1.65  #SimpNegUnit  : 6
% 3.14/1.65  #BackRed      : 0
% 3.14/1.65  
% 3.14/1.65  #Partial instantiations: 0
% 3.14/1.65  #Strategies tried      : 1
% 3.14/1.65  
% 3.14/1.65  Timing (in seconds)
% 3.14/1.65  ----------------------
% 3.14/1.65  Preprocessing        : 0.40
% 3.14/1.65  Parsing              : 0.24
% 3.14/1.65  CNF conversion       : 0.02
% 3.14/1.65  Main loop            : 0.37
% 3.14/1.65  Inferencing          : 0.16
% 3.14/1.66  Reduction            : 0.09
% 3.14/1.66  Demodulation         : 0.06
% 3.14/1.66  BG Simplification    : 0.02
% 3.14/1.66  Subsumption          : 0.06
% 3.14/1.66  Abstraction          : 0.02
% 3.14/1.66  MUC search           : 0.00
% 3.14/1.66  Cooper               : 0.00
% 3.14/1.66  Total                : 0.80
% 3.14/1.66  Index Insertion      : 0.00
% 3.14/1.66  Index Deletion       : 0.00
% 3.14/1.66  Index Matching       : 0.00
% 3.14/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
