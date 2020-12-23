%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:40 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 144 expanded)
%              Number of leaves         :   23 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  138 ( 416 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

tff(f_83,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_43,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_66,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_120,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_78,plain,(
    ! [A_38,B_39] :
      ( k10_relat_1(A_38,k1_relat_1(B_39)) = k1_relat_1(k5_relat_1(A_38,B_39))
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k10_relat_1(B_10,A_9),k1_relat_1(B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_122,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_48,B_49)),k1_relat_1(A_48))
      | ~ v1_relat_1(A_48)
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_8])).

tff(c_34,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

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

tff(c_128,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_122,c_63])).

tff(c_135,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_128])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_135])).

tff(c_139,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_10,plain,(
    ! [A_11,B_13] :
      ( k10_relat_1(A_11,k1_relat_1(B_13)) = k1_relat_1(k5_relat_1(A_11,B_13))
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k9_relat_1(B_15,k10_relat_1(B_15,A_14)),A_14)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_100,plain,(
    ! [C_40,A_41,B_42] :
      ( r1_tarski(k9_relat_1(C_40,A_41),k9_relat_1(C_40,B_42))
      | ~ r1_tarski(A_41,B_42)
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_206,plain,(
    ! [C_64,A_65,B_66] :
      ( k2_xboole_0(k9_relat_1(C_64,A_65),k9_relat_1(C_64,B_66)) = k9_relat_1(C_64,B_66)
      | ~ r1_tarski(A_65,B_66)
      | ~ v1_relat_1(C_64) ) ),
    inference(resolution,[status(thm)],[c_100,c_4])).

tff(c_230,plain,(
    ! [C_67,A_68,C_69,B_70] :
      ( r1_tarski(k9_relat_1(C_67,A_68),C_69)
      | ~ r1_tarski(k9_relat_1(C_67,B_70),C_69)
      | ~ r1_tarski(A_68,B_70)
      | ~ v1_relat_1(C_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_2])).

tff(c_240,plain,(
    ! [B_71,A_72,A_73] :
      ( r1_tarski(k9_relat_1(B_71,A_72),A_73)
      | ~ r1_tarski(A_72,k10_relat_1(B_71,A_73))
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(resolution,[status(thm)],[c_12,c_230])).

tff(c_138,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_151,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_245,plain,
    ( ~ r1_tarski('#skF_4',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_240,c_151])).

tff(c_252,plain,(
    ~ r1_tarski('#skF_4',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_245])).

tff(c_256,plain,
    ( ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_252])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_42,c_256])).

tff(c_261,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_24,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_305,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_261,c_24])).

tff(c_260,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_26,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_280,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_261,c_26])).

tff(c_329,plain,(
    ! [A_85,C_86,B_87] :
      ( r1_tarski(A_85,k10_relat_1(C_86,B_87))
      | ~ r1_tarski(k9_relat_1(C_86,A_85),B_87)
      | ~ r1_tarski(A_85,k1_relat_1(C_86))
      | ~ v1_funct_1(C_86)
      | ~ v1_relat_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_338,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_280,c_329])).

tff(c_356,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_260,c_338])).

tff(c_367,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_356])).

tff(c_370,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_367])).

tff(c_372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_305,c_370])).

tff(c_374,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_30,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_432,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_374,c_30])).

tff(c_373,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_32,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_379,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_374,c_32])).

tff(c_762,plain,(
    ! [A_145,C_146,B_147] :
      ( r1_tarski(A_145,k10_relat_1(C_146,B_147))
      | ~ r1_tarski(k9_relat_1(C_146,A_145),B_147)
      | ~ r1_tarski(A_145,k1_relat_1(C_146))
      | ~ v1_funct_1(C_146)
      | ~ v1_relat_1(C_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_789,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_379,c_762])).

tff(c_808,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_373,c_789])).

tff(c_818,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_808])).

tff(c_824,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_818])).

tff(c_826,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_432,c_824])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.48  
% 2.79/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.48  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.79/1.48  
% 2.79/1.48  %Foreground sorts:
% 2.79/1.48  
% 2.79/1.48  
% 2.79/1.48  %Background operators:
% 2.79/1.48  
% 2.79/1.48  
% 2.79/1.48  %Foreground operators:
% 2.79/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.79/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.79/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.79/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.48  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.79/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.79/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.79/1.48  
% 2.79/1.49  tff(f_83, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 2.79/1.49  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.79/1.49  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 2.79/1.49  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.79/1.49  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.79/1.49  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 2.79/1.49  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 2.79/1.49  tff(f_66, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 2.79/1.49  tff(c_28, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.79/1.49  tff(c_120, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_28])).
% 2.79/1.49  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.79/1.49  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.79/1.49  tff(c_78, plain, (![A_38, B_39]: (k10_relat_1(A_38, k1_relat_1(B_39))=k1_relat_1(k5_relat_1(A_38, B_39)) | ~v1_relat_1(B_39) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.79/1.49  tff(c_8, plain, (![B_10, A_9]: (r1_tarski(k10_relat_1(B_10, A_9), k1_relat_1(B_10)) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.79/1.49  tff(c_122, plain, (![A_48, B_49]: (r1_tarski(k1_relat_1(k5_relat_1(A_48, B_49)), k1_relat_1(A_48)) | ~v1_relat_1(A_48) | ~v1_relat_1(B_49) | ~v1_relat_1(A_48))), inference(superposition, [status(thm), theory('equality')], [c_78, c_8])).
% 2.79/1.49  tff(c_34, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.79/1.49  tff(c_42, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_34])).
% 2.79/1.49  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.79/1.49  tff(c_46, plain, (k2_xboole_0('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))=k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_4])).
% 2.79/1.49  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.79/1.49  tff(c_63, plain, (![C_3]: (r1_tarski('#skF_4', C_3) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), C_3))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2])).
% 2.79/1.49  tff(c_128, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_122, c_63])).
% 2.79/1.49  tff(c_135, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_128])).
% 2.79/1.49  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_135])).
% 2.79/1.49  tff(c_139, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_28])).
% 2.79/1.49  tff(c_10, plain, (![A_11, B_13]: (k10_relat_1(A_11, k1_relat_1(B_13))=k1_relat_1(k5_relat_1(A_11, B_13)) | ~v1_relat_1(B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.79/1.49  tff(c_20, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.79/1.49  tff(c_12, plain, (![B_15, A_14]: (r1_tarski(k9_relat_1(B_15, k10_relat_1(B_15, A_14)), A_14) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.79/1.49  tff(c_100, plain, (![C_40, A_41, B_42]: (r1_tarski(k9_relat_1(C_40, A_41), k9_relat_1(C_40, B_42)) | ~r1_tarski(A_41, B_42) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.79/1.49  tff(c_206, plain, (![C_64, A_65, B_66]: (k2_xboole_0(k9_relat_1(C_64, A_65), k9_relat_1(C_64, B_66))=k9_relat_1(C_64, B_66) | ~r1_tarski(A_65, B_66) | ~v1_relat_1(C_64))), inference(resolution, [status(thm)], [c_100, c_4])).
% 2.79/1.49  tff(c_230, plain, (![C_67, A_68, C_69, B_70]: (r1_tarski(k9_relat_1(C_67, A_68), C_69) | ~r1_tarski(k9_relat_1(C_67, B_70), C_69) | ~r1_tarski(A_68, B_70) | ~v1_relat_1(C_67))), inference(superposition, [status(thm), theory('equality')], [c_206, c_2])).
% 2.79/1.49  tff(c_240, plain, (![B_71, A_72, A_73]: (r1_tarski(k9_relat_1(B_71, A_72), A_73) | ~r1_tarski(A_72, k10_relat_1(B_71, A_73)) | ~v1_funct_1(B_71) | ~v1_relat_1(B_71))), inference(resolution, [status(thm)], [c_12, c_230])).
% 2.79/1.49  tff(c_138, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_28])).
% 2.79/1.49  tff(c_151, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_138])).
% 2.79/1.49  tff(c_245, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_240, c_151])).
% 2.79/1.49  tff(c_252, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_245])).
% 2.79/1.49  tff(c_256, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10, c_252])).
% 2.79/1.49  tff(c_259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_42, c_256])).
% 2.79/1.49  tff(c_261, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_138])).
% 2.79/1.49  tff(c_24, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.79/1.49  tff(c_305, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_261, c_24])).
% 2.79/1.49  tff(c_260, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_138])).
% 2.79/1.49  tff(c_26, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.79/1.49  tff(c_280, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_261, c_26])).
% 2.79/1.49  tff(c_329, plain, (![A_85, C_86, B_87]: (r1_tarski(A_85, k10_relat_1(C_86, B_87)) | ~r1_tarski(k9_relat_1(C_86, A_85), B_87) | ~r1_tarski(A_85, k1_relat_1(C_86)) | ~v1_funct_1(C_86) | ~v1_relat_1(C_86))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.79/1.49  tff(c_338, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_280, c_329])).
% 2.79/1.49  tff(c_356, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_260, c_338])).
% 2.79/1.49  tff(c_367, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10, c_356])).
% 2.79/1.49  tff(c_370, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_367])).
% 2.79/1.49  tff(c_372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_305, c_370])).
% 2.79/1.49  tff(c_374, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_34])).
% 2.79/1.49  tff(c_30, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.79/1.49  tff(c_432, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_374, c_30])).
% 2.79/1.49  tff(c_373, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_34])).
% 2.79/1.49  tff(c_32, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.79/1.49  tff(c_379, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_374, c_32])).
% 2.79/1.49  tff(c_762, plain, (![A_145, C_146, B_147]: (r1_tarski(A_145, k10_relat_1(C_146, B_147)) | ~r1_tarski(k9_relat_1(C_146, A_145), B_147) | ~r1_tarski(A_145, k1_relat_1(C_146)) | ~v1_funct_1(C_146) | ~v1_relat_1(C_146))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.79/1.49  tff(c_789, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_379, c_762])).
% 2.79/1.49  tff(c_808, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_373, c_789])).
% 2.79/1.49  tff(c_818, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10, c_808])).
% 2.79/1.49  tff(c_824, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_818])).
% 2.79/1.49  tff(c_826, plain, $false, inference(negUnitSimplification, [status(thm)], [c_432, c_824])).
% 2.79/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.49  
% 2.79/1.49  Inference rules
% 2.79/1.49  ----------------------
% 2.79/1.49  #Ref     : 0
% 2.79/1.49  #Sup     : 187
% 2.79/1.49  #Fact    : 0
% 2.79/1.49  #Define  : 0
% 2.79/1.49  #Split   : 4
% 2.79/1.49  #Chain   : 0
% 2.79/1.49  #Close   : 0
% 2.79/1.49  
% 2.79/1.49  Ordering : KBO
% 2.79/1.49  
% 2.79/1.49  Simplification rules
% 2.79/1.49  ----------------------
% 2.79/1.49  #Subsume      : 8
% 2.79/1.49  #Demod        : 68
% 2.79/1.49  #Tautology    : 61
% 2.79/1.49  #SimpNegUnit  : 5
% 2.79/1.49  #BackRed      : 0
% 2.79/1.49  
% 2.79/1.49  #Partial instantiations: 0
% 2.79/1.49  #Strategies tried      : 1
% 2.79/1.49  
% 2.79/1.49  Timing (in seconds)
% 2.79/1.49  ----------------------
% 2.79/1.50  Preprocessing        : 0.29
% 2.79/1.50  Parsing              : 0.15
% 2.79/1.50  CNF conversion       : 0.02
% 2.79/1.50  Main loop            : 0.37
% 2.79/1.50  Inferencing          : 0.15
% 2.79/1.50  Reduction            : 0.10
% 2.79/1.50  Demodulation         : 0.07
% 2.79/1.50  BG Simplification    : 0.02
% 2.79/1.50  Subsumption          : 0.07
% 2.79/1.50  Abstraction          : 0.02
% 2.79/1.50  MUC search           : 0.00
% 2.79/1.50  Cooper               : 0.00
% 2.79/1.50  Total                : 0.70
% 2.79/1.50  Index Insertion      : 0.00
% 2.79/1.50  Index Deletion       : 0.00
% 2.79/1.50  Index Matching       : 0.00
% 2.79/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
