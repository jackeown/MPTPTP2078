%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:39 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 214 expanded)
%              Number of leaves         :   23 (  83 expanded)
%              Depth                    :   14
%              Number of atoms          :  129 ( 598 expanded)
%              Number of equality atoms :    8 (  29 expanded)
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

tff(f_84,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_51,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_30,B_31)),k1_relat_1(A_30))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_37,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41,plain,(
    k2_xboole_0('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) = k1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_37,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    ! [C_3] :
      ( r1_tarski('#skF_4',C_3)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),C_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_2])).

tff(c_55,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_51,c_45])).

tff(c_61,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_55])).

tff(c_28,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_109,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_28])).

tff(c_110,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_20,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_81,plain,(
    ! [A_35,B_36] :
      ( k10_relat_1(A_35,k1_relat_1(B_36)) = k1_relat_1(k5_relat_1(A_35,B_36))
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k9_relat_1(B_16,k10_relat_1(B_16,A_15)),A_15)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_244,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k9_relat_1(A_64,k1_relat_1(k5_relat_1(A_64,B_65))),k1_relat_1(B_65))
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64)
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_12])).

tff(c_123,plain,(
    ! [C_41,A_42,B_43] :
      ( k2_xboole_0(k9_relat_1(C_41,A_42),k9_relat_1(C_41,B_43)) = k9_relat_1(C_41,k2_xboole_0(A_42,B_43))
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_143,plain,(
    ! [C_44,A_45,C_46,B_47] :
      ( r1_tarski(k9_relat_1(C_44,A_45),C_46)
      | ~ r1_tarski(k9_relat_1(C_44,k2_xboole_0(A_45,B_47)),C_46)
      | ~ v1_relat_1(C_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_2])).

tff(c_158,plain,(
    ! [C_44,C_46] :
      ( r1_tarski(k9_relat_1(C_44,'#skF_4'),C_46)
      | ~ r1_tarski(k9_relat_1(C_44,k1_relat_1(k5_relat_1('#skF_1','#skF_2'))),C_46)
      | ~ v1_relat_1(C_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_143])).

tff(c_248,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_244,c_158])).

tff(c_254,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_20,c_248])).

tff(c_256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_254])).

tff(c_258,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_24,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_328,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_258,c_24])).

tff(c_8,plain,(
    ! [A_9,B_11] :
      ( k10_relat_1(A_9,k1_relat_1(B_11)) = k1_relat_1(k5_relat_1(A_9,B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_257,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_26,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_303,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_258,c_26])).

tff(c_448,plain,(
    ! [A_98,C_99,B_100] :
      ( r1_tarski(A_98,k10_relat_1(C_99,B_100))
      | ~ r1_tarski(k9_relat_1(C_99,A_98),B_100)
      | ~ r1_tarski(A_98,k1_relat_1(C_99))
      | ~ v1_funct_1(C_99)
      | ~ v1_relat_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_460,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_303,c_448])).

tff(c_476,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_257,c_460])).

tff(c_486,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_476])).

tff(c_489,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_486])).

tff(c_491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_328,c_489])).

tff(c_493,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_30,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_498,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_30])).

tff(c_492,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_32,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_529,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_32])).

tff(c_711,plain,(
    ! [A_143,C_144,B_145] :
      ( r1_tarski(A_143,k10_relat_1(C_144,B_145))
      | ~ r1_tarski(k9_relat_1(C_144,A_143),B_145)
      | ~ r1_tarski(A_143,k1_relat_1(C_144))
      | ~ v1_funct_1(C_144)
      | ~ v1_relat_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_726,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_529,c_711])).

tff(c_738,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_492,c_726])).

tff(c_745,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_738])).

tff(c_748,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_745])).

tff(c_750,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_498,c_748])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:52:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.42  
% 2.99/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.42  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.99/1.42  
% 2.99/1.42  %Foreground sorts:
% 2.99/1.42  
% 2.99/1.42  
% 2.99/1.42  %Background operators:
% 2.99/1.42  
% 2.99/1.42  
% 2.99/1.42  %Foreground operators:
% 2.99/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.99/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.99/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.99/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.42  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.99/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.99/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.99/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.99/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.99/1.43  
% 2.99/1.44  tff(f_84, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_1)).
% 2.99/1.44  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 2.99/1.44  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.99/1.44  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.99/1.44  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.99/1.44  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 2.99/1.44  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t153_relat_1)).
% 2.99/1.44  tff(f_67, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 2.99/1.44  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.99/1.44  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.99/1.44  tff(c_51, plain, (![A_30, B_31]: (r1_tarski(k1_relat_1(k5_relat_1(A_30, B_31)), k1_relat_1(A_30)) | ~v1_relat_1(B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.99/1.44  tff(c_34, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.99/1.44  tff(c_37, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_34])).
% 2.99/1.44  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.99/1.44  tff(c_41, plain, (k2_xboole_0('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))=k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_37, c_4])).
% 2.99/1.44  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.99/1.44  tff(c_45, plain, (![C_3]: (r1_tarski('#skF_4', C_3) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), C_3))), inference(superposition, [status(thm), theory('equality')], [c_41, c_2])).
% 2.99/1.44  tff(c_55, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_51, c_45])).
% 2.99/1.44  tff(c_61, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_55])).
% 2.99/1.44  tff(c_28, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.99/1.44  tff(c_109, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_28])).
% 2.99/1.44  tff(c_110, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_109])).
% 2.99/1.44  tff(c_20, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.99/1.44  tff(c_81, plain, (![A_35, B_36]: (k10_relat_1(A_35, k1_relat_1(B_36))=k1_relat_1(k5_relat_1(A_35, B_36)) | ~v1_relat_1(B_36) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.99/1.44  tff(c_12, plain, (![B_16, A_15]: (r1_tarski(k9_relat_1(B_16, k10_relat_1(B_16, A_15)), A_15) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.99/1.44  tff(c_244, plain, (![A_64, B_65]: (r1_tarski(k9_relat_1(A_64, k1_relat_1(k5_relat_1(A_64, B_65))), k1_relat_1(B_65)) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64) | ~v1_relat_1(B_65) | ~v1_relat_1(A_64))), inference(superposition, [status(thm), theory('equality')], [c_81, c_12])).
% 2.99/1.44  tff(c_123, plain, (![C_41, A_42, B_43]: (k2_xboole_0(k9_relat_1(C_41, A_42), k9_relat_1(C_41, B_43))=k9_relat_1(C_41, k2_xboole_0(A_42, B_43)) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.99/1.44  tff(c_143, plain, (![C_44, A_45, C_46, B_47]: (r1_tarski(k9_relat_1(C_44, A_45), C_46) | ~r1_tarski(k9_relat_1(C_44, k2_xboole_0(A_45, B_47)), C_46) | ~v1_relat_1(C_44))), inference(superposition, [status(thm), theory('equality')], [c_123, c_2])).
% 2.99/1.44  tff(c_158, plain, (![C_44, C_46]: (r1_tarski(k9_relat_1(C_44, '#skF_4'), C_46) | ~r1_tarski(k9_relat_1(C_44, k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), C_46) | ~v1_relat_1(C_44))), inference(superposition, [status(thm), theory('equality')], [c_41, c_143])).
% 2.99/1.44  tff(c_248, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_244, c_158])).
% 2.99/1.44  tff(c_254, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_20, c_248])).
% 2.99/1.44  tff(c_256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_254])).
% 2.99/1.44  tff(c_258, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_109])).
% 2.99/1.44  tff(c_24, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.99/1.44  tff(c_328, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_258, c_24])).
% 2.99/1.44  tff(c_8, plain, (![A_9, B_11]: (k10_relat_1(A_9, k1_relat_1(B_11))=k1_relat_1(k5_relat_1(A_9, B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.99/1.44  tff(c_257, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_109])).
% 2.99/1.44  tff(c_26, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.99/1.44  tff(c_303, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_258, c_26])).
% 2.99/1.44  tff(c_448, plain, (![A_98, C_99, B_100]: (r1_tarski(A_98, k10_relat_1(C_99, B_100)) | ~r1_tarski(k9_relat_1(C_99, A_98), B_100) | ~r1_tarski(A_98, k1_relat_1(C_99)) | ~v1_funct_1(C_99) | ~v1_relat_1(C_99))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.99/1.44  tff(c_460, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_303, c_448])).
% 2.99/1.44  tff(c_476, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_257, c_460])).
% 2.99/1.44  tff(c_486, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8, c_476])).
% 2.99/1.44  tff(c_489, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_486])).
% 2.99/1.44  tff(c_491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_328, c_489])).
% 2.99/1.44  tff(c_493, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_34])).
% 2.99/1.44  tff(c_30, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.99/1.44  tff(c_498, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_493, c_30])).
% 2.99/1.44  tff(c_492, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_34])).
% 2.99/1.44  tff(c_32, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.99/1.44  tff(c_529, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_493, c_32])).
% 2.99/1.44  tff(c_711, plain, (![A_143, C_144, B_145]: (r1_tarski(A_143, k10_relat_1(C_144, B_145)) | ~r1_tarski(k9_relat_1(C_144, A_143), B_145) | ~r1_tarski(A_143, k1_relat_1(C_144)) | ~v1_funct_1(C_144) | ~v1_relat_1(C_144))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.99/1.44  tff(c_726, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_529, c_711])).
% 2.99/1.44  tff(c_738, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_492, c_726])).
% 2.99/1.44  tff(c_745, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8, c_738])).
% 2.99/1.44  tff(c_748, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_745])).
% 2.99/1.44  tff(c_750, plain, $false, inference(negUnitSimplification, [status(thm)], [c_498, c_748])).
% 2.99/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.44  
% 2.99/1.44  Inference rules
% 2.99/1.44  ----------------------
% 2.99/1.44  #Ref     : 0
% 2.99/1.44  #Sup     : 172
% 2.99/1.44  #Fact    : 0
% 2.99/1.44  #Define  : 0
% 2.99/1.44  #Split   : 2
% 2.99/1.44  #Chain   : 0
% 2.99/1.44  #Close   : 0
% 2.99/1.44  
% 2.99/1.44  Ordering : KBO
% 2.99/1.44  
% 2.99/1.44  Simplification rules
% 2.99/1.44  ----------------------
% 2.99/1.44  #Subsume      : 5
% 2.99/1.44  #Demod        : 42
% 2.99/1.44  #Tautology    : 64
% 2.99/1.44  #SimpNegUnit  : 5
% 2.99/1.44  #BackRed      : 0
% 2.99/1.44  
% 2.99/1.44  #Partial instantiations: 0
% 2.99/1.44  #Strategies tried      : 1
% 2.99/1.44  
% 2.99/1.44  Timing (in seconds)
% 2.99/1.44  ----------------------
% 2.99/1.44  Preprocessing        : 0.30
% 2.99/1.44  Parsing              : 0.16
% 2.99/1.44  CNF conversion       : 0.02
% 2.99/1.44  Main loop            : 0.39
% 2.99/1.44  Inferencing          : 0.17
% 2.99/1.44  Reduction            : 0.10
% 2.99/1.44  Demodulation         : 0.07
% 2.99/1.44  BG Simplification    : 0.02
% 2.99/1.44  Subsumption          : 0.07
% 2.99/1.44  Abstraction          : 0.02
% 2.99/1.44  MUC search           : 0.00
% 2.99/1.44  Cooper               : 0.00
% 2.99/1.44  Total                : 0.72
% 2.99/1.44  Index Insertion      : 0.00
% 2.99/1.44  Index Deletion       : 0.00
% 2.99/1.44  Index Matching       : 0.00
% 2.99/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
