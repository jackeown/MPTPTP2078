%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:26 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 144 expanded)
%              Number of leaves         :   28 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  152 ( 319 expanded)
%              Number of equality atoms :   33 (  69 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_90,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_46,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_44,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_16,plain,(
    ! [A_8] :
      ( v1_relat_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_38,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_40,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_22,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    ! [A_9] : v1_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    ! [A_10] : v2_funct_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    ! [A_18] : k2_funct_1(k6_relat_1(A_18)) = k6_relat_1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_107,plain,(
    ! [B_32,A_33] :
      ( k9_relat_1(k2_funct_1(B_32),A_33) = k10_relat_1(B_32,A_33)
      | ~ v2_funct_1(B_32)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_120,plain,(
    ! [A_18,A_33] :
      ( k9_relat_1(k6_relat_1(A_18),A_33) = k10_relat_1(k6_relat_1(A_18),A_33)
      | ~ v2_funct_1(k6_relat_1(A_18))
      | ~ v1_funct_1(k6_relat_1(A_18))
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_107])).

tff(c_124,plain,(
    ! [A_18,A_33] : k9_relat_1(k6_relat_1(A_18),A_33) = k10_relat_1(k6_relat_1(A_18),A_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_24,c_120])).

tff(c_10,plain,(
    ! [A_7] : k1_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_200,plain,(
    ! [A_44] :
      ( k5_relat_1(A_44,k2_funct_1(A_44)) = k6_relat_1(k1_relat_1(A_44))
      | ~ v2_funct_1(A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_209,plain,(
    ! [A_18] :
      ( k5_relat_1(k6_relat_1(A_18),k6_relat_1(A_18)) = k6_relat_1(k1_relat_1(k6_relat_1(A_18)))
      | ~ v2_funct_1(k6_relat_1(A_18))
      | ~ v1_funct_1(k6_relat_1(A_18))
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_200])).

tff(c_213,plain,(
    ! [A_18] : k5_relat_1(k6_relat_1(A_18),k6_relat_1(A_18)) = k6_relat_1(A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_24,c_10,c_209])).

tff(c_238,plain,(
    ! [B_47,C_48,A_49] :
      ( k9_relat_1(k5_relat_1(B_47,C_48),A_49) = k9_relat_1(C_48,k9_relat_1(B_47,A_49))
      | ~ v1_relat_1(C_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_254,plain,(
    ! [A_18,A_49] :
      ( k9_relat_1(k6_relat_1(A_18),k9_relat_1(k6_relat_1(A_18),A_49)) = k9_relat_1(k6_relat_1(A_18),A_49)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_238])).

tff(c_264,plain,(
    ! [A_18,A_49] : k10_relat_1(k6_relat_1(A_18),k10_relat_1(k6_relat_1(A_18),A_49)) = k10_relat_1(k6_relat_1(A_18),A_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_124,c_124,c_124,c_254])).

tff(c_132,plain,(
    ! [A_36,A_37] : k9_relat_1(k6_relat_1(A_36),A_37) = k10_relat_1(k6_relat_1(A_36),A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_24,c_120])).

tff(c_26,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k9_relat_1(B_12,k10_relat_1(B_12,A_11)),A_11)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_142,plain,(
    ! [A_36,A_11] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_36),k10_relat_1(k6_relat_1(A_36),A_11)),A_11)
      | ~ v1_funct_1(k6_relat_1(A_36))
      | ~ v1_relat_1(k6_relat_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_26])).

tff(c_150,plain,(
    ! [A_36,A_11] : r1_tarski(k10_relat_1(k6_relat_1(A_36),k10_relat_1(k6_relat_1(A_36),A_11)),A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_142])).

tff(c_289,plain,(
    ! [A_36,A_11] : r1_tarski(k10_relat_1(k6_relat_1(A_36),A_11),A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_150])).

tff(c_30,plain,(
    ! [B_16,A_15] :
      ( k9_relat_1(k2_funct_1(B_16),A_15) = k10_relat_1(B_16,A_15)
      | ~ v2_funct_1(B_16)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    ! [A_17] :
      ( k5_relat_1(A_17,k2_funct_1(A_17)) = k6_relat_1(k1_relat_1(A_17))
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_260,plain,(
    ! [A_17,A_49] :
      ( k9_relat_1(k6_relat_1(k1_relat_1(A_17)),A_49) = k9_relat_1(k2_funct_1(A_17),k9_relat_1(A_17,A_49))
      | ~ v1_relat_1(k2_funct_1(A_17))
      | ~ v1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_238])).

tff(c_491,plain,(
    ! [A_68,A_69] :
      ( k9_relat_1(k2_funct_1(A_68),k9_relat_1(A_68,A_69)) = k10_relat_1(k6_relat_1(k1_relat_1(A_68)),A_69)
      | ~ v1_relat_1(k2_funct_1(A_68))
      | ~ v1_relat_1(A_68)
      | ~ v2_funct_1(A_68)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_260])).

tff(c_729,plain,(
    ! [B_84,A_85] :
      ( k10_relat_1(k6_relat_1(k1_relat_1(B_84)),A_85) = k10_relat_1(B_84,k9_relat_1(B_84,A_85))
      | ~ v1_relat_1(k2_funct_1(B_84))
      | ~ v1_relat_1(B_84)
      | ~ v2_funct_1(B_84)
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84)
      | ~ v2_funct_1(B_84)
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_491])).

tff(c_125,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,k10_relat_1(B_35,k9_relat_1(B_35,A_34)))
      | ~ r1_tarski(A_34,k1_relat_1(B_35))
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_131,plain,(
    ! [B_35,A_34] :
      ( k10_relat_1(B_35,k9_relat_1(B_35,A_34)) = A_34
      | ~ r1_tarski(k10_relat_1(B_35,k9_relat_1(B_35,A_34)),A_34)
      | ~ r1_tarski(A_34,k1_relat_1(B_35))
      | ~ v1_relat_1(B_35) ) ),
    inference(resolution,[status(thm)],[c_125,c_2])).

tff(c_784,plain,(
    ! [B_84,A_85] :
      ( k10_relat_1(B_84,k9_relat_1(B_84,A_85)) = A_85
      | ~ r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(B_84)),A_85),A_85)
      | ~ r1_tarski(A_85,k1_relat_1(B_84))
      | ~ v1_relat_1(B_84)
      | ~ v1_relat_1(k2_funct_1(B_84))
      | ~ v1_relat_1(B_84)
      | ~ v2_funct_1(B_84)
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84)
      | ~ v2_funct_1(B_84)
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_729,c_131])).

tff(c_935,plain,(
    ! [B_86,A_87] :
      ( k10_relat_1(B_86,k9_relat_1(B_86,A_87)) = A_87
      | ~ r1_tarski(A_87,k1_relat_1(B_86))
      | ~ v1_relat_1(k2_funct_1(B_86))
      | ~ v2_funct_1(B_86)
      | ~ v1_funct_1(B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_784])).

tff(c_957,plain,
    ( k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_935])).

tff(c_971,plain,
    ( k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_957])).

tff(c_972,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_971])).

tff(c_976,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_972])).

tff(c_980,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_976])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.55  
% 3.31/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.55  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.31/1.55  
% 3.31/1.55  %Foreground sorts:
% 3.31/1.55  
% 3.31/1.55  
% 3.31/1.55  %Background operators:
% 3.31/1.55  
% 3.31/1.55  
% 3.31/1.55  %Foreground operators:
% 3.31/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.31/1.55  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.31/1.55  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.31/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.55  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.31/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.31/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.55  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.31/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.31/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.55  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.31/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.31/1.55  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.31/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.31/1.55  
% 3.44/1.57  tff(f_101, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 3.44/1.57  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.44/1.57  tff(f_58, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.44/1.57  tff(f_54, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.44/1.57  tff(f_90, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 3.44/1.57  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 3.44/1.57  tff(f_42, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.44/1.57  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 3.44/1.57  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_relat_1)).
% 3.44/1.57  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 3.44/1.57  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 3.44/1.57  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.44/1.57  tff(c_46, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.44/1.57  tff(c_44, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.44/1.57  tff(c_16, plain, (![A_8]: (v1_relat_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.44/1.57  tff(c_38, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.44/1.57  tff(c_40, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.44/1.57  tff(c_42, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.44/1.57  tff(c_22, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.44/1.57  tff(c_20, plain, (![A_9]: (v1_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.44/1.57  tff(c_24, plain, (![A_10]: (v2_funct_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.44/1.57  tff(c_36, plain, (![A_18]: (k2_funct_1(k6_relat_1(A_18))=k6_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.44/1.57  tff(c_107, plain, (![B_32, A_33]: (k9_relat_1(k2_funct_1(B_32), A_33)=k10_relat_1(B_32, A_33) | ~v2_funct_1(B_32) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.44/1.57  tff(c_120, plain, (![A_18, A_33]: (k9_relat_1(k6_relat_1(A_18), A_33)=k10_relat_1(k6_relat_1(A_18), A_33) | ~v2_funct_1(k6_relat_1(A_18)) | ~v1_funct_1(k6_relat_1(A_18)) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_107])).
% 3.44/1.57  tff(c_124, plain, (![A_18, A_33]: (k9_relat_1(k6_relat_1(A_18), A_33)=k10_relat_1(k6_relat_1(A_18), A_33))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_24, c_120])).
% 3.44/1.57  tff(c_10, plain, (![A_7]: (k1_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.44/1.57  tff(c_200, plain, (![A_44]: (k5_relat_1(A_44, k2_funct_1(A_44))=k6_relat_1(k1_relat_1(A_44)) | ~v2_funct_1(A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.44/1.57  tff(c_209, plain, (![A_18]: (k5_relat_1(k6_relat_1(A_18), k6_relat_1(A_18))=k6_relat_1(k1_relat_1(k6_relat_1(A_18))) | ~v2_funct_1(k6_relat_1(A_18)) | ~v1_funct_1(k6_relat_1(A_18)) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_200])).
% 3.44/1.57  tff(c_213, plain, (![A_18]: (k5_relat_1(k6_relat_1(A_18), k6_relat_1(A_18))=k6_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_24, c_10, c_209])).
% 3.44/1.57  tff(c_238, plain, (![B_47, C_48, A_49]: (k9_relat_1(k5_relat_1(B_47, C_48), A_49)=k9_relat_1(C_48, k9_relat_1(B_47, A_49)) | ~v1_relat_1(C_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.44/1.57  tff(c_254, plain, (![A_18, A_49]: (k9_relat_1(k6_relat_1(A_18), k9_relat_1(k6_relat_1(A_18), A_49))=k9_relat_1(k6_relat_1(A_18), A_49) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_213, c_238])).
% 3.44/1.57  tff(c_264, plain, (![A_18, A_49]: (k10_relat_1(k6_relat_1(A_18), k10_relat_1(k6_relat_1(A_18), A_49))=k10_relat_1(k6_relat_1(A_18), A_49))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_124, c_124, c_124, c_254])).
% 3.44/1.57  tff(c_132, plain, (![A_36, A_37]: (k9_relat_1(k6_relat_1(A_36), A_37)=k10_relat_1(k6_relat_1(A_36), A_37))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_24, c_120])).
% 3.44/1.57  tff(c_26, plain, (![B_12, A_11]: (r1_tarski(k9_relat_1(B_12, k10_relat_1(B_12, A_11)), A_11) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.44/1.57  tff(c_142, plain, (![A_36, A_11]: (r1_tarski(k10_relat_1(k6_relat_1(A_36), k10_relat_1(k6_relat_1(A_36), A_11)), A_11) | ~v1_funct_1(k6_relat_1(A_36)) | ~v1_relat_1(k6_relat_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_132, c_26])).
% 3.44/1.57  tff(c_150, plain, (![A_36, A_11]: (r1_tarski(k10_relat_1(k6_relat_1(A_36), k10_relat_1(k6_relat_1(A_36), A_11)), A_11))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_142])).
% 3.44/1.57  tff(c_289, plain, (![A_36, A_11]: (r1_tarski(k10_relat_1(k6_relat_1(A_36), A_11), A_11))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_150])).
% 3.44/1.57  tff(c_30, plain, (![B_16, A_15]: (k9_relat_1(k2_funct_1(B_16), A_15)=k10_relat_1(B_16, A_15) | ~v2_funct_1(B_16) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.44/1.57  tff(c_34, plain, (![A_17]: (k5_relat_1(A_17, k2_funct_1(A_17))=k6_relat_1(k1_relat_1(A_17)) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.44/1.57  tff(c_260, plain, (![A_17, A_49]: (k9_relat_1(k6_relat_1(k1_relat_1(A_17)), A_49)=k9_relat_1(k2_funct_1(A_17), k9_relat_1(A_17, A_49)) | ~v1_relat_1(k2_funct_1(A_17)) | ~v1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(superposition, [status(thm), theory('equality')], [c_34, c_238])).
% 3.44/1.57  tff(c_491, plain, (![A_68, A_69]: (k9_relat_1(k2_funct_1(A_68), k9_relat_1(A_68, A_69))=k10_relat_1(k6_relat_1(k1_relat_1(A_68)), A_69) | ~v1_relat_1(k2_funct_1(A_68)) | ~v1_relat_1(A_68) | ~v2_funct_1(A_68) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_260])).
% 3.44/1.57  tff(c_729, plain, (![B_84, A_85]: (k10_relat_1(k6_relat_1(k1_relat_1(B_84)), A_85)=k10_relat_1(B_84, k9_relat_1(B_84, A_85)) | ~v1_relat_1(k2_funct_1(B_84)) | ~v1_relat_1(B_84) | ~v2_funct_1(B_84) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84) | ~v2_funct_1(B_84) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84))), inference(superposition, [status(thm), theory('equality')], [c_30, c_491])).
% 3.44/1.57  tff(c_125, plain, (![A_34, B_35]: (r1_tarski(A_34, k10_relat_1(B_35, k9_relat_1(B_35, A_34))) | ~r1_tarski(A_34, k1_relat_1(B_35)) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.44/1.57  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.44/1.57  tff(c_131, plain, (![B_35, A_34]: (k10_relat_1(B_35, k9_relat_1(B_35, A_34))=A_34 | ~r1_tarski(k10_relat_1(B_35, k9_relat_1(B_35, A_34)), A_34) | ~r1_tarski(A_34, k1_relat_1(B_35)) | ~v1_relat_1(B_35))), inference(resolution, [status(thm)], [c_125, c_2])).
% 3.44/1.57  tff(c_784, plain, (![B_84, A_85]: (k10_relat_1(B_84, k9_relat_1(B_84, A_85))=A_85 | ~r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(B_84)), A_85), A_85) | ~r1_tarski(A_85, k1_relat_1(B_84)) | ~v1_relat_1(B_84) | ~v1_relat_1(k2_funct_1(B_84)) | ~v1_relat_1(B_84) | ~v2_funct_1(B_84) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84) | ~v2_funct_1(B_84) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84))), inference(superposition, [status(thm), theory('equality')], [c_729, c_131])).
% 3.44/1.57  tff(c_935, plain, (![B_86, A_87]: (k10_relat_1(B_86, k9_relat_1(B_86, A_87))=A_87 | ~r1_tarski(A_87, k1_relat_1(B_86)) | ~v1_relat_1(k2_funct_1(B_86)) | ~v2_funct_1(B_86) | ~v1_funct_1(B_86) | ~v1_relat_1(B_86))), inference(demodulation, [status(thm), theory('equality')], [c_289, c_784])).
% 3.44/1.57  tff(c_957, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_42, c_935])).
% 3.44/1.57  tff(c_971, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_957])).
% 3.44/1.57  tff(c_972, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_971])).
% 3.44/1.57  tff(c_976, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_972])).
% 3.44/1.57  tff(c_980, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_976])).
% 3.44/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.57  
% 3.44/1.57  Inference rules
% 3.44/1.57  ----------------------
% 3.44/1.57  #Ref     : 0
% 3.44/1.57  #Sup     : 209
% 3.44/1.57  #Fact    : 0
% 3.44/1.57  #Define  : 0
% 3.44/1.57  #Split   : 1
% 3.44/1.57  #Chain   : 0
% 3.44/1.57  #Close   : 0
% 3.44/1.57  
% 3.44/1.57  Ordering : KBO
% 3.44/1.57  
% 3.44/1.57  Simplification rules
% 3.44/1.57  ----------------------
% 3.44/1.57  #Subsume      : 17
% 3.44/1.57  #Demod        : 487
% 3.44/1.57  #Tautology    : 81
% 3.44/1.57  #SimpNegUnit  : 1
% 3.44/1.57  #BackRed      : 3
% 3.44/1.57  
% 3.44/1.57  #Partial instantiations: 0
% 3.44/1.57  #Strategies tried      : 1
% 3.44/1.57  
% 3.44/1.57  Timing (in seconds)
% 3.44/1.57  ----------------------
% 3.44/1.57  Preprocessing        : 0.33
% 3.44/1.57  Parsing              : 0.18
% 3.44/1.57  CNF conversion       : 0.02
% 3.44/1.57  Main loop            : 0.44
% 3.44/1.57  Inferencing          : 0.16
% 3.44/1.57  Reduction            : 0.16
% 3.44/1.57  Demodulation         : 0.13
% 3.44/1.57  BG Simplification    : 0.02
% 3.44/1.57  Subsumption          : 0.08
% 3.44/1.57  Abstraction          : 0.03
% 3.44/1.57  MUC search           : 0.00
% 3.44/1.57  Cooper               : 0.00
% 3.44/1.57  Total                : 0.80
% 3.44/1.57  Index Insertion      : 0.00
% 3.44/1.57  Index Deletion       : 0.00
% 3.44/1.57  Index Matching       : 0.00
% 3.44/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
