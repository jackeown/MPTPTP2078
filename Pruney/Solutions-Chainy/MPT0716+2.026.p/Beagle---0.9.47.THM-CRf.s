%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:40 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 137 expanded)
%              Number of leaves         :   21 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  134 ( 410 expanded)
%              Number of equality atoms :    3 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_26,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_80,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_57,plain,(
    ! [A_32,B_33] :
      ( k10_relat_1(A_32,k1_relat_1(B_33)) = k1_relat_1(k5_relat_1(A_32,B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k10_relat_1(B_8,A_7),k1_relat_1(B_8))
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_98,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_39,B_40)),k1_relat_1(A_39))
      | ~ v1_relat_1(A_39)
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_6])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,(
    ! [A_44,A_45,B_46] :
      ( r1_tarski(A_44,k1_relat_1(A_45))
      | ~ r1_tarski(A_44,k1_relat_1(k5_relat_1(A_45,B_46)))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_133,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_119])).

tff(c_145,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_133])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_145])).

tff(c_149,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_8,plain,(
    ! [A_9,B_11] :
      ( k10_relat_1(A_9,k1_relat_1(B_11)) = k1_relat_1(k5_relat_1(A_9,B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_18,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4,plain,(
    ! [C_6,A_4,B_5] :
      ( r1_tarski(k9_relat_1(C_6,A_4),k9_relat_1(C_6,B_5))
      | ~ r1_tarski(A_4,B_5)
      | ~ v1_relat_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_47,plain,(
    ! [B_27,A_28] :
      ( r1_tarski(k9_relat_1(B_27,k10_relat_1(B_27,A_28)),A_28)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_231,plain,(
    ! [A_56,A_57,B_58] :
      ( r1_tarski(A_56,A_57)
      | ~ r1_tarski(A_56,k9_relat_1(B_58,k10_relat_1(B_58,A_57)))
      | ~ v1_funct_1(B_58)
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_47,c_2])).

tff(c_273,plain,(
    ! [C_62,A_63,A_64] :
      ( r1_tarski(k9_relat_1(C_62,A_63),A_64)
      | ~ v1_funct_1(C_62)
      | ~ r1_tarski(A_63,k10_relat_1(C_62,A_64))
      | ~ v1_relat_1(C_62) ) ),
    inference(resolution,[status(thm)],[c_4,c_231])).

tff(c_148,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_157,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_288,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ r1_tarski('#skF_4',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_273,c_157])).

tff(c_301,plain,(
    ~ r1_tarski('#skF_4',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_288])).

tff(c_306,plain,
    ( ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_301])).

tff(c_309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_38,c_306])).

tff(c_311,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_22,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_336,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_311,c_22])).

tff(c_310,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_24,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_421,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_311,c_24])).

tff(c_499,plain,(
    ! [A_76,C_77,B_78] :
      ( r1_tarski(A_76,k10_relat_1(C_77,B_78))
      | ~ r1_tarski(k9_relat_1(C_77,A_76),B_78)
      | ~ r1_tarski(A_76,k1_relat_1(C_77))
      | ~ v1_funct_1(C_77)
      | ~ v1_relat_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_505,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_421,c_499])).

tff(c_535,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_310,c_505])).

tff(c_560,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_535])).

tff(c_573,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_560])).

tff(c_575,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_573])).

tff(c_577,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_28,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_581,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_577,c_28])).

tff(c_576,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_30,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_617,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_577,c_30])).

tff(c_819,plain,(
    ! [A_120,C_121,B_122] :
      ( r1_tarski(A_120,k10_relat_1(C_121,B_122))
      | ~ r1_tarski(k9_relat_1(C_121,A_120),B_122)
      | ~ r1_tarski(A_120,k1_relat_1(C_121))
      | ~ v1_funct_1(C_121)
      | ~ v1_relat_1(C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_831,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_617,c_819])).

tff(c_849,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_576,c_831])).

tff(c_864,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_849])).

tff(c_873,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_864])).

tff(c_875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_581,c_873])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:42:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.49  
% 3.45/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.50  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.45/1.50  
% 3.45/1.50  %Foreground sorts:
% 3.45/1.50  
% 3.45/1.50  
% 3.45/1.50  %Background operators:
% 3.45/1.50  
% 3.45/1.50  
% 3.45/1.50  %Foreground operators:
% 3.45/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.45/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.45/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.45/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.45/1.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.45/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.45/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.45/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.50  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.45/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.45/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.45/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.45/1.50  
% 3.45/1.51  tff(f_81, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 3.45/1.51  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.45/1.51  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 3.45/1.51  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.45/1.51  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 3.45/1.51  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 3.45/1.51  tff(f_64, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 3.45/1.51  tff(c_26, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.45/1.51  tff(c_80, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_26])).
% 3.45/1.51  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.45/1.51  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.45/1.51  tff(c_32, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.45/1.51  tff(c_38, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_32])).
% 3.45/1.51  tff(c_57, plain, (![A_32, B_33]: (k10_relat_1(A_32, k1_relat_1(B_33))=k1_relat_1(k5_relat_1(A_32, B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.45/1.51  tff(c_6, plain, (![B_8, A_7]: (r1_tarski(k10_relat_1(B_8, A_7), k1_relat_1(B_8)) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.45/1.51  tff(c_98, plain, (![A_39, B_40]: (r1_tarski(k1_relat_1(k5_relat_1(A_39, B_40)), k1_relat_1(A_39)) | ~v1_relat_1(A_39) | ~v1_relat_1(B_40) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_57, c_6])).
% 3.45/1.51  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.45/1.51  tff(c_119, plain, (![A_44, A_45, B_46]: (r1_tarski(A_44, k1_relat_1(A_45)) | ~r1_tarski(A_44, k1_relat_1(k5_relat_1(A_45, B_46))) | ~v1_relat_1(B_46) | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_98, c_2])).
% 3.45/1.51  tff(c_133, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_38, c_119])).
% 3.45/1.51  tff(c_145, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_133])).
% 3.45/1.51  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_145])).
% 3.45/1.51  tff(c_149, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_26])).
% 3.45/1.51  tff(c_8, plain, (![A_9, B_11]: (k10_relat_1(A_9, k1_relat_1(B_11))=k1_relat_1(k5_relat_1(A_9, B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.45/1.51  tff(c_18, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.45/1.51  tff(c_4, plain, (![C_6, A_4, B_5]: (r1_tarski(k9_relat_1(C_6, A_4), k9_relat_1(C_6, B_5)) | ~r1_tarski(A_4, B_5) | ~v1_relat_1(C_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.45/1.51  tff(c_47, plain, (![B_27, A_28]: (r1_tarski(k9_relat_1(B_27, k10_relat_1(B_27, A_28)), A_28) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.45/1.51  tff(c_231, plain, (![A_56, A_57, B_58]: (r1_tarski(A_56, A_57) | ~r1_tarski(A_56, k9_relat_1(B_58, k10_relat_1(B_58, A_57))) | ~v1_funct_1(B_58) | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_47, c_2])).
% 3.45/1.51  tff(c_273, plain, (![C_62, A_63, A_64]: (r1_tarski(k9_relat_1(C_62, A_63), A_64) | ~v1_funct_1(C_62) | ~r1_tarski(A_63, k10_relat_1(C_62, A_64)) | ~v1_relat_1(C_62))), inference(resolution, [status(thm)], [c_4, c_231])).
% 3.45/1.51  tff(c_148, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_26])).
% 3.45/1.51  tff(c_157, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_148])).
% 3.45/1.51  tff(c_288, plain, (~v1_funct_1('#skF_1') | ~r1_tarski('#skF_4', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_273, c_157])).
% 3.45/1.51  tff(c_301, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_288])).
% 3.45/1.51  tff(c_306, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8, c_301])).
% 3.45/1.51  tff(c_309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_38, c_306])).
% 3.45/1.51  tff(c_311, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_148])).
% 3.45/1.51  tff(c_22, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.45/1.51  tff(c_336, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_311, c_22])).
% 3.45/1.51  tff(c_310, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_148])).
% 3.45/1.51  tff(c_24, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.45/1.51  tff(c_421, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_311, c_24])).
% 3.45/1.51  tff(c_499, plain, (![A_76, C_77, B_78]: (r1_tarski(A_76, k10_relat_1(C_77, B_78)) | ~r1_tarski(k9_relat_1(C_77, A_76), B_78) | ~r1_tarski(A_76, k1_relat_1(C_77)) | ~v1_funct_1(C_77) | ~v1_relat_1(C_77))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.45/1.51  tff(c_505, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_421, c_499])).
% 3.45/1.51  tff(c_535, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_310, c_505])).
% 3.45/1.51  tff(c_560, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8, c_535])).
% 3.45/1.51  tff(c_573, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_560])).
% 3.45/1.51  tff(c_575, plain, $false, inference(negUnitSimplification, [status(thm)], [c_336, c_573])).
% 3.45/1.51  tff(c_577, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_32])).
% 3.45/1.51  tff(c_28, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.45/1.51  tff(c_581, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_577, c_28])).
% 3.45/1.51  tff(c_576, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_32])).
% 3.45/1.51  tff(c_30, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.45/1.51  tff(c_617, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_577, c_30])).
% 3.45/1.51  tff(c_819, plain, (![A_120, C_121, B_122]: (r1_tarski(A_120, k10_relat_1(C_121, B_122)) | ~r1_tarski(k9_relat_1(C_121, A_120), B_122) | ~r1_tarski(A_120, k1_relat_1(C_121)) | ~v1_funct_1(C_121) | ~v1_relat_1(C_121))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.45/1.51  tff(c_831, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_617, c_819])).
% 3.45/1.51  tff(c_849, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_576, c_831])).
% 3.45/1.51  tff(c_864, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8, c_849])).
% 3.45/1.51  tff(c_873, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_864])).
% 3.45/1.51  tff(c_875, plain, $false, inference(negUnitSimplification, [status(thm)], [c_581, c_873])).
% 3.45/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.51  
% 3.45/1.51  Inference rules
% 3.45/1.51  ----------------------
% 3.45/1.51  #Ref     : 0
% 3.45/1.51  #Sup     : 201
% 3.45/1.51  #Fact    : 0
% 3.45/1.51  #Define  : 0
% 3.45/1.51  #Split   : 6
% 3.45/1.51  #Chain   : 0
% 3.45/1.51  #Close   : 0
% 3.45/1.51  
% 3.45/1.51  Ordering : KBO
% 3.45/1.51  
% 3.45/1.51  Simplification rules
% 3.45/1.51  ----------------------
% 3.45/1.51  #Subsume      : 29
% 3.45/1.51  #Demod        : 67
% 3.45/1.51  #Tautology    : 29
% 3.45/1.51  #SimpNegUnit  : 7
% 3.45/1.51  #BackRed      : 0
% 3.45/1.51  
% 3.45/1.51  #Partial instantiations: 0
% 3.45/1.51  #Strategies tried      : 1
% 3.45/1.51  
% 3.45/1.51  Timing (in seconds)
% 3.45/1.51  ----------------------
% 3.45/1.52  Preprocessing        : 0.31
% 3.45/1.52  Parsing              : 0.16
% 3.45/1.52  CNF conversion       : 0.02
% 3.45/1.52  Main loop            : 0.43
% 3.45/1.52  Inferencing          : 0.16
% 3.45/1.52  Reduction            : 0.12
% 3.45/1.52  Demodulation         : 0.08
% 3.45/1.52  BG Simplification    : 0.02
% 3.45/1.52  Subsumption          : 0.10
% 3.45/1.52  Abstraction          : 0.02
% 3.45/1.52  MUC search           : 0.00
% 3.45/1.52  Cooper               : 0.00
% 3.45/1.52  Total                : 0.78
% 3.45/1.52  Index Insertion      : 0.00
% 3.45/1.52  Index Deletion       : 0.00
% 3.45/1.52  Index Matching       : 0.00
% 3.45/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
