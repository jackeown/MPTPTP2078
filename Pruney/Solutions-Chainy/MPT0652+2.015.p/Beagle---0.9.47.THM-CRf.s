%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:54 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 193 expanded)
%              Number of leaves         :   23 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  165 ( 536 expanded)
%              Number of equality atoms :   61 ( 220 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k2_relat_1(A) = k2_relat_1(B)
               => k2_relat_1(k5_relat_1(A,C)) = k2_relat_1(k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_24,plain,(
    ! [A_22] : v1_relat_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_14,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_713,plain,(
    ! [A_62,B_63] :
      ( k5_relat_1(k6_relat_1(A_62),B_63) = B_63
      | ~ r1_tarski(k1_relat_1(B_63),A_62)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_726,plain,(
    ! [B_63] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_63)),B_63) = B_63
      | ~ v1_relat_1(B_63) ) ),
    inference(resolution,[status(thm)],[c_6,c_713])).

tff(c_36,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_22,plain,(
    ! [A_21] :
      ( v1_relat_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_20] :
      ( k5_relat_1(A_20,k6_relat_1(k2_relat_1(A_20))) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1003,plain,(
    ! [C_76,B_77,A_78] :
      ( k1_relat_1(k5_relat_1(C_76,B_77)) = k1_relat_1(k5_relat_1(C_76,A_78))
      | k1_relat_1(B_77) != k1_relat_1(A_78)
      | ~ v1_relat_1(C_76)
      | ~ v1_relat_1(B_77)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1099,plain,(
    ! [A_20,B_77] :
      ( k1_relat_1(k5_relat_1(A_20,B_77)) = k1_relat_1(A_20)
      | k1_relat_1(k6_relat_1(k2_relat_1(A_20))) != k1_relat_1(B_77)
      | ~ v1_relat_1(A_20)
      | ~ v1_relat_1(B_77)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_20)))
      | ~ v1_relat_1(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1003])).

tff(c_1284,plain,(
    ! [A_83,B_84] :
      ( k1_relat_1(k5_relat_1(A_83,B_84)) = k1_relat_1(A_83)
      | k2_relat_1(A_83) != k1_relat_1(B_84)
      | ~ v1_relat_1(B_84)
      | ~ v1_relat_1(A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_12,c_1099])).

tff(c_34,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30,plain,(
    ! [A_23] :
      ( k1_relat_1(k2_funct_1(A_23)) = k2_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_363,plain,(
    ! [C_49,B_50,A_51] :
      ( k1_relat_1(k5_relat_1(C_49,B_50)) = k1_relat_1(k5_relat_1(C_49,A_51))
      | k1_relat_1(B_50) != k1_relat_1(A_51)
      | ~ v1_relat_1(C_49)
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_62,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_396,plain,(
    ! [B_50] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_50)) != k2_relat_1('#skF_1')
      | k1_relat_1(B_50) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_62])).

tff(c_461,plain,(
    ! [B_50] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_50)) != k2_relat_1('#skF_1')
      | k1_relat_1(B_50) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(B_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_396])).

tff(c_634,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_461])).

tff(c_637,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_634])).

tff(c_641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_637])).

tff(c_643,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_94,plain,(
    ! [A_35] :
      ( k2_relat_1(k2_funct_1(A_35)) = k1_relat_1(A_35)
      | ~ v2_funct_1(A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_100,plain,(
    ! [A_35] :
      ( k5_relat_1(k2_funct_1(A_35),k6_relat_1(k1_relat_1(A_35))) = k2_funct_1(A_35)
      | ~ v1_relat_1(k2_funct_1(A_35))
      | ~ v2_funct_1(A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_18])).

tff(c_644,plain,(
    ! [B_56] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_56)) != k2_relat_1('#skF_1')
      | k1_relat_1(B_56) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(B_56) ) ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_656,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k6_relat_1(k1_relat_1('#skF_1'))) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_1')))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_644])).

tff(c_666,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_643,c_24,c_12,c_656])).

tff(c_671,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_666])).

tff(c_675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_671])).

tff(c_677,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1309,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1284,c_677])).

tff(c_1353,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1309])).

tff(c_1381,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1353])).

tff(c_1384,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1381])).

tff(c_1388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1384])).

tff(c_1390,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1353])).

tff(c_28,plain,(
    ! [A_23] :
      ( k2_relat_1(k2_funct_1(A_23)) = k1_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1389,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1353])).

tff(c_1391,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1389])).

tff(c_1394,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1391])).

tff(c_1398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_1394])).

tff(c_1400,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1389])).

tff(c_876,plain,(
    ! [B_73,C_74,A_75] :
      ( k2_relat_1(k5_relat_1(B_73,C_74)) = k2_relat_1(k5_relat_1(A_75,C_74))
      | k2_relat_1(B_73) != k2_relat_1(A_75)
      | ~ v1_relat_1(C_74)
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_676,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_906,plain,(
    ! [A_75] :
      ( k2_relat_1(k5_relat_1(A_75,'#skF_1')) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != k2_relat_1(A_75)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_876,c_676])).

tff(c_970,plain,(
    ! [A_75] :
      ( k2_relat_1(k5_relat_1(A_75,'#skF_1')) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != k2_relat_1(A_75)
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_906])).

tff(c_1776,plain,(
    ! [A_88] :
      ( k2_relat_1(k5_relat_1(A_88,'#skF_1')) != k2_relat_1('#skF_1')
      | k2_relat_1(A_88) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1390,c_1400,c_970])).

tff(c_1788,plain,
    ( k2_relat_1(k6_relat_1(k1_relat_1('#skF_1'))) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_1')))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_1776])).

tff(c_1796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_24,c_14,c_1788])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n001.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 12:44:14 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.61/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.62  
% 3.61/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.62  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.61/1.62  
% 3.61/1.62  %Foreground sorts:
% 3.61/1.62  
% 3.61/1.62  
% 3.61/1.62  %Background operators:
% 3.61/1.62  
% 3.61/1.62  
% 3.61/1.62  %Foreground operators:
% 3.61/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.61/1.62  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.61/1.62  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.61/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.62  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.61/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.61/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.61/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.61/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.61/1.62  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.61/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.61/1.62  
% 3.61/1.64  tff(f_102, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 3.61/1.64  tff(f_81, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.61/1.64  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.61/1.64  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.61/1.64  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 3.61/1.64  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.61/1.64  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 3.61/1.64  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t198_relat_1)).
% 3.61/1.64  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.61/1.64  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k2_relat_1(A) = k2_relat_1(B)) => (k2_relat_1(k5_relat_1(A, C)) = k2_relat_1(k5_relat_1(B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t199_relat_1)).
% 3.61/1.64  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.61/1.64  tff(c_24, plain, (![A_22]: (v1_relat_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.61/1.64  tff(c_14, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.61/1.64  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.61/1.64  tff(c_713, plain, (![A_62, B_63]: (k5_relat_1(k6_relat_1(A_62), B_63)=B_63 | ~r1_tarski(k1_relat_1(B_63), A_62) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.61/1.64  tff(c_726, plain, (![B_63]: (k5_relat_1(k6_relat_1(k1_relat_1(B_63)), B_63)=B_63 | ~v1_relat_1(B_63))), inference(resolution, [status(thm)], [c_6, c_713])).
% 3.61/1.64  tff(c_36, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.61/1.64  tff(c_22, plain, (![A_21]: (v1_relat_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.61/1.64  tff(c_12, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.61/1.64  tff(c_18, plain, (![A_20]: (k5_relat_1(A_20, k6_relat_1(k2_relat_1(A_20)))=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.61/1.64  tff(c_1003, plain, (![C_76, B_77, A_78]: (k1_relat_1(k5_relat_1(C_76, B_77))=k1_relat_1(k5_relat_1(C_76, A_78)) | k1_relat_1(B_77)!=k1_relat_1(A_78) | ~v1_relat_1(C_76) | ~v1_relat_1(B_77) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.61/1.64  tff(c_1099, plain, (![A_20, B_77]: (k1_relat_1(k5_relat_1(A_20, B_77))=k1_relat_1(A_20) | k1_relat_1(k6_relat_1(k2_relat_1(A_20)))!=k1_relat_1(B_77) | ~v1_relat_1(A_20) | ~v1_relat_1(B_77) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_20))) | ~v1_relat_1(A_20))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1003])).
% 3.61/1.64  tff(c_1284, plain, (![A_83, B_84]: (k1_relat_1(k5_relat_1(A_83, B_84))=k1_relat_1(A_83) | k2_relat_1(A_83)!=k1_relat_1(B_84) | ~v1_relat_1(B_84) | ~v1_relat_1(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_12, c_1099])).
% 3.61/1.64  tff(c_34, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.61/1.64  tff(c_30, plain, (![A_23]: (k1_relat_1(k2_funct_1(A_23))=k2_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.61/1.64  tff(c_363, plain, (![C_49, B_50, A_51]: (k1_relat_1(k5_relat_1(C_49, B_50))=k1_relat_1(k5_relat_1(C_49, A_51)) | k1_relat_1(B_50)!=k1_relat_1(A_51) | ~v1_relat_1(C_49) | ~v1_relat_1(B_50) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.61/1.64  tff(c_32, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.61/1.64  tff(c_62, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_32])).
% 3.61/1.64  tff(c_396, plain, (![B_50]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_50))!=k2_relat_1('#skF_1') | k1_relat_1(B_50)!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(B_50) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_363, c_62])).
% 3.61/1.64  tff(c_461, plain, (![B_50]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_50))!=k2_relat_1('#skF_1') | k1_relat_1(B_50)!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(B_50))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_396])).
% 3.61/1.64  tff(c_634, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_461])).
% 3.61/1.64  tff(c_637, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_634])).
% 3.61/1.64  tff(c_641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_637])).
% 3.61/1.64  tff(c_643, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_461])).
% 3.61/1.64  tff(c_94, plain, (![A_35]: (k2_relat_1(k2_funct_1(A_35))=k1_relat_1(A_35) | ~v2_funct_1(A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.61/1.64  tff(c_100, plain, (![A_35]: (k5_relat_1(k2_funct_1(A_35), k6_relat_1(k1_relat_1(A_35)))=k2_funct_1(A_35) | ~v1_relat_1(k2_funct_1(A_35)) | ~v2_funct_1(A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_94, c_18])).
% 3.61/1.64  tff(c_644, plain, (![B_56]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_56))!=k2_relat_1('#skF_1') | k1_relat_1(B_56)!=k1_relat_1('#skF_1') | ~v1_relat_1(B_56))), inference(splitRight, [status(thm)], [c_461])).
% 3.61/1.64  tff(c_656, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k6_relat_1(k1_relat_1('#skF_1')))!=k1_relat_1('#skF_1') | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_1'))) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_100, c_644])).
% 3.61/1.64  tff(c_666, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_643, c_24, c_12, c_656])).
% 3.61/1.64  tff(c_671, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30, c_666])).
% 3.61/1.64  tff(c_675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_671])).
% 3.61/1.64  tff(c_677, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 3.61/1.64  tff(c_1309, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1284, c_677])).
% 3.61/1.64  tff(c_1353, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1309])).
% 3.61/1.64  tff(c_1381, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1353])).
% 3.61/1.64  tff(c_1384, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1381])).
% 3.61/1.64  tff(c_1388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1384])).
% 3.61/1.64  tff(c_1390, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_1353])).
% 3.61/1.64  tff(c_28, plain, (![A_23]: (k2_relat_1(k2_funct_1(A_23))=k1_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.61/1.64  tff(c_1389, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_1353])).
% 3.61/1.64  tff(c_1391, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_1389])).
% 3.61/1.64  tff(c_1394, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_1391])).
% 3.61/1.64  tff(c_1398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_1394])).
% 3.61/1.64  tff(c_1400, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_1389])).
% 3.61/1.64  tff(c_876, plain, (![B_73, C_74, A_75]: (k2_relat_1(k5_relat_1(B_73, C_74))=k2_relat_1(k5_relat_1(A_75, C_74)) | k2_relat_1(B_73)!=k2_relat_1(A_75) | ~v1_relat_1(C_74) | ~v1_relat_1(B_73) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.61/1.64  tff(c_676, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 3.61/1.64  tff(c_906, plain, (![A_75]: (k2_relat_1(k5_relat_1(A_75, '#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1(A_75) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_75))), inference(superposition, [status(thm), theory('equality')], [c_876, c_676])).
% 3.61/1.64  tff(c_970, plain, (![A_75]: (k2_relat_1(k5_relat_1(A_75, '#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1(A_75) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_75))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_906])).
% 3.61/1.64  tff(c_1776, plain, (![A_88]: (k2_relat_1(k5_relat_1(A_88, '#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(A_88)!=k1_relat_1('#skF_1') | ~v1_relat_1(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_1390, c_1400, c_970])).
% 3.61/1.64  tff(c_1788, plain, (k2_relat_1(k6_relat_1(k1_relat_1('#skF_1')))!=k1_relat_1('#skF_1') | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_1'))) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_726, c_1776])).
% 3.61/1.64  tff(c_1796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_24, c_14, c_1788])).
% 3.61/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.64  
% 3.61/1.64  Inference rules
% 3.61/1.64  ----------------------
% 3.61/1.64  #Ref     : 0
% 3.61/1.64  #Sup     : 374
% 3.61/1.64  #Fact    : 0
% 3.61/1.64  #Define  : 0
% 3.61/1.64  #Split   : 6
% 3.61/1.64  #Chain   : 0
% 3.61/1.64  #Close   : 0
% 3.61/1.64  
% 3.61/1.64  Ordering : KBO
% 3.61/1.64  
% 3.61/1.64  Simplification rules
% 3.61/1.64  ----------------------
% 3.61/1.64  #Subsume      : 19
% 3.61/1.64  #Demod        : 503
% 3.61/1.64  #Tautology    : 148
% 3.61/1.64  #SimpNegUnit  : 0
% 3.61/1.64  #BackRed      : 0
% 3.61/1.64  
% 3.61/1.64  #Partial instantiations: 0
% 3.61/1.64  #Strategies tried      : 1
% 3.61/1.64  
% 3.61/1.64  Timing (in seconds)
% 3.61/1.64  ----------------------
% 3.61/1.64  Preprocessing        : 0.38
% 3.61/1.64  Parsing              : 0.22
% 3.61/1.64  CNF conversion       : 0.02
% 3.61/1.64  Main loop            : 0.52
% 3.61/1.64  Inferencing          : 0.19
% 3.61/1.64  Reduction            : 0.17
% 3.61/1.64  Demodulation         : 0.13
% 3.61/1.64  BG Simplification    : 0.03
% 3.61/1.64  Subsumption          : 0.09
% 3.61/1.64  Abstraction          : 0.04
% 3.61/1.64  MUC search           : 0.00
% 3.61/1.64  Cooper               : 0.00
% 3.61/1.64  Total                : 0.93
% 3.61/1.64  Index Insertion      : 0.00
% 3.61/1.64  Index Deletion       : 0.00
% 3.61/1.64  Index Matching       : 0.00
% 3.61/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
