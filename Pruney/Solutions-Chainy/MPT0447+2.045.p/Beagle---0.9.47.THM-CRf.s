%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:33 EST 2020

% Result     : Theorem 5.33s
% Output     : CNFRefutation 5.33s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 208 expanded)
%              Number of leaves         :   22 (  79 expanded)
%              Depth                    :   17
%              Number of atoms          :  140 ( 446 expanded)
%              Number of equality atoms :   30 (  81 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k2_relat_1(A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_82,plain,(
    ! [A_40] :
      ( k2_xboole_0(k1_relat_1(A_40),k2_relat_1(A_40)) = k3_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_97,plain,(
    ! [A_40] :
      ( r1_tarski(k1_relat_1(A_40),k3_relat_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_18])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [C_11,A_9,B_10] :
      ( r1_tarski(C_11,'#skF_1'(A_9,B_10,C_11))
      | k2_xboole_0(A_9,C_11) = B_10
      | ~ r1_tarski(C_11,B_10)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1593,plain,(
    ! [B_107,A_108,C_109] :
      ( ~ r1_tarski(B_107,'#skF_1'(A_108,B_107,C_109))
      | k2_xboole_0(A_108,C_109) = B_107
      | ~ r1_tarski(C_109,B_107)
      | ~ r1_tarski(A_108,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1601,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(B_10,B_10)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_14,c_1593])).

tff(c_1611,plain,(
    ! [A_110,B_111] :
      ( k2_xboole_0(A_110,B_111) = B_111
      | ~ r1_tarski(A_110,B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1601])).

tff(c_1698,plain,(
    ! [A_40] :
      ( k2_xboole_0(k1_relat_1(A_40),k3_relat_1(A_40)) = k3_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(resolution,[status(thm)],[c_97,c_1611])).

tff(c_30,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_20,plain,(
    ! [A_15,C_17,B_16] :
      ( r1_tarski(k2_xboole_0(A_15,C_17),B_16)
      | ~ r1_tarski(C_17,B_16)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_116,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_tarski(k2_xboole_0(A_44,C_45),B_46)
      | ~ r1_tarski(C_45,B_46)
      | ~ r1_tarski(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_62,plain,(
    ! [B_38,A_39] :
      ( B_38 = A_39
      | ~ r1_tarski(B_38,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(k2_xboole_0(A_13,B_14),A_13) ) ),
    inference(resolution,[status(thm)],[c_18,c_62])).

tff(c_120,plain,(
    ! [B_46,C_45] :
      ( k2_xboole_0(B_46,C_45) = B_46
      | ~ r1_tarski(C_45,B_46)
      | ~ r1_tarski(B_46,B_46) ) ),
    inference(resolution,[status(thm)],[c_116,c_75])).

tff(c_134,plain,(
    ! [B_47,C_48] :
      ( k2_xboole_0(B_47,C_48) = B_47
      | ~ r1_tarski(C_48,B_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_120])).

tff(c_162,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_134])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_39,plain,(
    ! [A_32,C_33,B_34] :
      ( r1_tarski(A_32,C_33)
      | ~ r1_tarski(k2_xboole_0(A_32,B_34),C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_471,plain,(
    ! [A_65,C_66,B_67,B_68] :
      ( r1_tarski(A_65,k2_xboole_0(C_66,B_67))
      | ~ r1_tarski(k2_xboole_0(A_65,B_68),B_67) ) ),
    inference(resolution,[status(thm)],[c_8,c_39])).

tff(c_511,plain,(
    ! [A_69,C_70,B_71] : r1_tarski(A_69,k2_xboole_0(C_70,k2_xboole_0(A_69,B_71))) ),
    inference(resolution,[status(thm)],[c_6,c_471])).

tff(c_556,plain,(
    ! [C_72] : r1_tarski('#skF_3',k2_xboole_0(C_72,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_511])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_982,plain,(
    ! [C_87] :
      ( k2_xboole_0(C_87,'#skF_3') = '#skF_3'
      | ~ r1_tarski(k2_xboole_0(C_87,'#skF_3'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_556,c_2])).

tff(c_998,plain,(
    ! [A_15] :
      ( k2_xboole_0(A_15,'#skF_3') = '#skF_3'
      | ~ r1_tarski('#skF_3','#skF_3')
      | ~ r1_tarski(A_15,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_982])).

tff(c_1006,plain,(
    ! [A_88] :
      ( k2_xboole_0(A_88,'#skF_3') = '#skF_3'
      | ~ r1_tarski(A_88,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_998])).

tff(c_1021,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_1006])).

tff(c_425,plain,(
    ! [A_63,B_64] :
      ( k2_xboole_0(k1_relat_1(A_63),k1_relat_1(B_64)) = k1_relat_1(k2_xboole_0(A_63,B_64))
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3822,plain,(
    ! [A_154,B_155] :
      ( r1_tarski(k1_relat_1(A_154),k1_relat_1(k2_xboole_0(A_154,B_155)))
      | ~ v1_relat_1(B_155)
      | ~ v1_relat_1(A_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_18])).

tff(c_3860,plain,
    ( r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1021,c_3822])).

tff(c_3898,plain,(
    r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_3860])).

tff(c_131,plain,(
    ! [B_46,C_45] :
      ( k2_xboole_0(B_46,C_45) = B_46
      | ~ r1_tarski(C_45,B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_120])).

tff(c_3914,plain,(
    k2_xboole_0(k1_relat_1('#skF_3'),k1_relat_1('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3898,c_131])).

tff(c_161,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_134])).

tff(c_542,plain,(
    ! [B_2,C_70] : r1_tarski(B_2,k2_xboole_0(C_70,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_511])).

tff(c_2026,plain,(
    ! [B_116,C_117] : k2_xboole_0(B_116,k2_xboole_0(C_117,B_116)) = k2_xboole_0(C_117,B_116) ),
    inference(resolution,[status(thm)],[c_542,c_1611])).

tff(c_53,plain,(
    ! [A_32,B_34,B_14] : r1_tarski(A_32,k2_xboole_0(k2_xboole_0(A_32,B_34),B_14)) ),
    inference(resolution,[status(thm)],[c_18,c_39])).

tff(c_2132,plain,(
    ! [B_116,C_117,B_14] : r1_tarski(B_116,k2_xboole_0(k2_xboole_0(C_117,B_116),B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2026,c_53])).

tff(c_4105,plain,(
    ! [B_156] : r1_tarski(k1_relat_1('#skF_2'),k2_xboole_0(k1_relat_1('#skF_3'),B_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3914,c_2132])).

tff(c_4119,plain,
    ( r1_tarski(k1_relat_1('#skF_2'),k3_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1698,c_4105])).

tff(c_4145,plain,(
    r1_tarski(k1_relat_1('#skF_2'),k3_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4119])).

tff(c_22,plain,(
    ! [A_18] :
      ( k2_xboole_0(k1_relat_1(A_18),k2_relat_1(A_18)) = k3_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_919,plain,(
    ! [A_85,B_86] :
      ( k2_xboole_0(k2_relat_1(A_85),k2_relat_1(B_86)) = k2_relat_1(k2_xboole_0(A_85,B_86))
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3465,plain,(
    ! [A_150,B_151] :
      ( r1_tarski(k2_relat_1(A_150),k2_relat_1(k2_xboole_0(A_150,B_151)))
      | ~ v1_relat_1(B_151)
      | ~ v1_relat_1(A_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_919,c_18])).

tff(c_3497,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1021,c_3465])).

tff(c_3534,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_3497])).

tff(c_1609,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1601])).

tff(c_3549,plain,(
    k2_xboole_0(k2_relat_1('#skF_2'),k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3534,c_1609])).

tff(c_510,plain,(
    ! [A_65,C_66,B_68] : r1_tarski(A_65,k2_xboole_0(C_66,k2_xboole_0(A_65,B_68))) ),
    inference(resolution,[status(thm)],[c_6,c_471])).

tff(c_3733,plain,(
    ! [C_152] : r1_tarski(k2_relat_1('#skF_2'),k2_xboole_0(C_152,k2_relat_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3549,c_510])).

tff(c_3763,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),k3_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_3733])).

tff(c_3773,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k3_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3763])).

tff(c_4533,plain,(
    ! [A_162,B_163] :
      ( r1_tarski(k3_relat_1(A_162),B_163)
      | ~ r1_tarski(k2_relat_1(A_162),B_163)
      | ~ r1_tarski(k1_relat_1(A_162),B_163)
      | ~ v1_relat_1(A_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_116])).

tff(c_28,plain,(
    ~ r1_tarski(k3_relat_1('#skF_2'),k3_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4561,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),k3_relat_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1('#skF_2'),k3_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4533,c_28])).

tff(c_4575,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4145,c_3773,c_4561])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:49:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.33/2.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.01  
% 5.33/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.01  %$ r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 5.33/2.01  
% 5.33/2.01  %Foreground sorts:
% 5.33/2.01  
% 5.33/2.01  
% 5.33/2.01  %Background operators:
% 5.33/2.01  
% 5.33/2.01  
% 5.33/2.01  %Foreground operators:
% 5.33/2.01  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.33/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.33/2.01  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 5.33/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.33/2.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.33/2.01  tff('#skF_2', type, '#skF_2': $i).
% 5.33/2.01  tff('#skF_3', type, '#skF_3': $i).
% 5.33/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.33/2.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.33/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.33/2.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.33/2.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.33/2.01  
% 5.33/2.03  tff(f_88, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 5.33/2.03  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 5.33/2.03  tff(f_54, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.33/2.03  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.33/2.03  tff(f_52, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 5.33/2.03  tff(f_60, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 5.33/2.03  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 5.33/2.03  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.33/2.03  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relat_1)).
% 5.33/2.03  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_relat_1)).
% 5.33/2.03  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.33/2.03  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.33/2.03  tff(c_82, plain, (![A_40]: (k2_xboole_0(k1_relat_1(A_40), k2_relat_1(A_40))=k3_relat_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.33/2.03  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.33/2.03  tff(c_97, plain, (![A_40]: (r1_tarski(k1_relat_1(A_40), k3_relat_1(A_40)) | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_82, c_18])).
% 5.33/2.03  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.33/2.03  tff(c_14, plain, (![C_11, A_9, B_10]: (r1_tarski(C_11, '#skF_1'(A_9, B_10, C_11)) | k2_xboole_0(A_9, C_11)=B_10 | ~r1_tarski(C_11, B_10) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.33/2.03  tff(c_1593, plain, (![B_107, A_108, C_109]: (~r1_tarski(B_107, '#skF_1'(A_108, B_107, C_109)) | k2_xboole_0(A_108, C_109)=B_107 | ~r1_tarski(C_109, B_107) | ~r1_tarski(A_108, B_107))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.33/2.03  tff(c_1601, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(B_10, B_10) | ~r1_tarski(A_9, B_10))), inference(resolution, [status(thm)], [c_14, c_1593])).
% 5.33/2.03  tff(c_1611, plain, (![A_110, B_111]: (k2_xboole_0(A_110, B_111)=B_111 | ~r1_tarski(A_110, B_111))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1601])).
% 5.33/2.03  tff(c_1698, plain, (![A_40]: (k2_xboole_0(k1_relat_1(A_40), k3_relat_1(A_40))=k3_relat_1(A_40) | ~v1_relat_1(A_40))), inference(resolution, [status(thm)], [c_97, c_1611])).
% 5.33/2.03  tff(c_30, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.33/2.03  tff(c_20, plain, (![A_15, C_17, B_16]: (r1_tarski(k2_xboole_0(A_15, C_17), B_16) | ~r1_tarski(C_17, B_16) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.33/2.03  tff(c_116, plain, (![A_44, C_45, B_46]: (r1_tarski(k2_xboole_0(A_44, C_45), B_46) | ~r1_tarski(C_45, B_46) | ~r1_tarski(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.33/2.03  tff(c_62, plain, (![B_38, A_39]: (B_38=A_39 | ~r1_tarski(B_38, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.33/2.03  tff(c_75, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(k2_xboole_0(A_13, B_14), A_13))), inference(resolution, [status(thm)], [c_18, c_62])).
% 5.33/2.03  tff(c_120, plain, (![B_46, C_45]: (k2_xboole_0(B_46, C_45)=B_46 | ~r1_tarski(C_45, B_46) | ~r1_tarski(B_46, B_46))), inference(resolution, [status(thm)], [c_116, c_75])).
% 5.33/2.03  tff(c_134, plain, (![B_47, C_48]: (k2_xboole_0(B_47, C_48)=B_47 | ~r1_tarski(C_48, B_47))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_120])).
% 5.33/2.03  tff(c_162, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_30, c_134])).
% 5.33/2.03  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.33/2.03  tff(c_39, plain, (![A_32, C_33, B_34]: (r1_tarski(A_32, C_33) | ~r1_tarski(k2_xboole_0(A_32, B_34), C_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.33/2.03  tff(c_471, plain, (![A_65, C_66, B_67, B_68]: (r1_tarski(A_65, k2_xboole_0(C_66, B_67)) | ~r1_tarski(k2_xboole_0(A_65, B_68), B_67))), inference(resolution, [status(thm)], [c_8, c_39])).
% 5.33/2.03  tff(c_511, plain, (![A_69, C_70, B_71]: (r1_tarski(A_69, k2_xboole_0(C_70, k2_xboole_0(A_69, B_71))))), inference(resolution, [status(thm)], [c_6, c_471])).
% 5.33/2.03  tff(c_556, plain, (![C_72]: (r1_tarski('#skF_3', k2_xboole_0(C_72, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_162, c_511])).
% 5.33/2.03  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.33/2.03  tff(c_982, plain, (![C_87]: (k2_xboole_0(C_87, '#skF_3')='#skF_3' | ~r1_tarski(k2_xboole_0(C_87, '#skF_3'), '#skF_3'))), inference(resolution, [status(thm)], [c_556, c_2])).
% 5.33/2.03  tff(c_998, plain, (![A_15]: (k2_xboole_0(A_15, '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski(A_15, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_982])).
% 5.33/2.03  tff(c_1006, plain, (![A_88]: (k2_xboole_0(A_88, '#skF_3')='#skF_3' | ~r1_tarski(A_88, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_998])).
% 5.33/2.03  tff(c_1021, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_30, c_1006])).
% 5.33/2.03  tff(c_425, plain, (![A_63, B_64]: (k2_xboole_0(k1_relat_1(A_63), k1_relat_1(B_64))=k1_relat_1(k2_xboole_0(A_63, B_64)) | ~v1_relat_1(B_64) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.33/2.03  tff(c_3822, plain, (![A_154, B_155]: (r1_tarski(k1_relat_1(A_154), k1_relat_1(k2_xboole_0(A_154, B_155))) | ~v1_relat_1(B_155) | ~v1_relat_1(A_154))), inference(superposition, [status(thm), theory('equality')], [c_425, c_18])).
% 5.33/2.03  tff(c_3860, plain, (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1021, c_3822])).
% 5.33/2.03  tff(c_3898, plain, (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_3860])).
% 5.33/2.03  tff(c_131, plain, (![B_46, C_45]: (k2_xboole_0(B_46, C_45)=B_46 | ~r1_tarski(C_45, B_46))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_120])).
% 5.33/2.03  tff(c_3914, plain, (k2_xboole_0(k1_relat_1('#skF_3'), k1_relat_1('#skF_2'))=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3898, c_131])).
% 5.33/2.03  tff(c_161, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_134])).
% 5.33/2.03  tff(c_542, plain, (![B_2, C_70]: (r1_tarski(B_2, k2_xboole_0(C_70, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_161, c_511])).
% 5.33/2.03  tff(c_2026, plain, (![B_116, C_117]: (k2_xboole_0(B_116, k2_xboole_0(C_117, B_116))=k2_xboole_0(C_117, B_116))), inference(resolution, [status(thm)], [c_542, c_1611])).
% 5.33/2.03  tff(c_53, plain, (![A_32, B_34, B_14]: (r1_tarski(A_32, k2_xboole_0(k2_xboole_0(A_32, B_34), B_14)))), inference(resolution, [status(thm)], [c_18, c_39])).
% 5.33/2.03  tff(c_2132, plain, (![B_116, C_117, B_14]: (r1_tarski(B_116, k2_xboole_0(k2_xboole_0(C_117, B_116), B_14)))), inference(superposition, [status(thm), theory('equality')], [c_2026, c_53])).
% 5.33/2.03  tff(c_4105, plain, (![B_156]: (r1_tarski(k1_relat_1('#skF_2'), k2_xboole_0(k1_relat_1('#skF_3'), B_156)))), inference(superposition, [status(thm), theory('equality')], [c_3914, c_2132])).
% 5.33/2.03  tff(c_4119, plain, (r1_tarski(k1_relat_1('#skF_2'), k3_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1698, c_4105])).
% 5.33/2.03  tff(c_4145, plain, (r1_tarski(k1_relat_1('#skF_2'), k3_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4119])).
% 5.33/2.03  tff(c_22, plain, (![A_18]: (k2_xboole_0(k1_relat_1(A_18), k2_relat_1(A_18))=k3_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.33/2.03  tff(c_919, plain, (![A_85, B_86]: (k2_xboole_0(k2_relat_1(A_85), k2_relat_1(B_86))=k2_relat_1(k2_xboole_0(A_85, B_86)) | ~v1_relat_1(B_86) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.33/2.03  tff(c_3465, plain, (![A_150, B_151]: (r1_tarski(k2_relat_1(A_150), k2_relat_1(k2_xboole_0(A_150, B_151))) | ~v1_relat_1(B_151) | ~v1_relat_1(A_150))), inference(superposition, [status(thm), theory('equality')], [c_919, c_18])).
% 5.33/2.03  tff(c_3497, plain, (r1_tarski(k2_relat_1('#skF_2'), k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1021, c_3465])).
% 5.33/2.03  tff(c_3534, plain, (r1_tarski(k2_relat_1('#skF_2'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_3497])).
% 5.33/2.03  tff(c_1609, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1601])).
% 5.33/2.03  tff(c_3549, plain, (k2_xboole_0(k2_relat_1('#skF_2'), k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3534, c_1609])).
% 5.33/2.03  tff(c_510, plain, (![A_65, C_66, B_68]: (r1_tarski(A_65, k2_xboole_0(C_66, k2_xboole_0(A_65, B_68))))), inference(resolution, [status(thm)], [c_6, c_471])).
% 5.33/2.03  tff(c_3733, plain, (![C_152]: (r1_tarski(k2_relat_1('#skF_2'), k2_xboole_0(C_152, k2_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_3549, c_510])).
% 5.33/2.03  tff(c_3763, plain, (r1_tarski(k2_relat_1('#skF_2'), k3_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_3733])).
% 5.33/2.03  tff(c_3773, plain, (r1_tarski(k2_relat_1('#skF_2'), k3_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3763])).
% 5.33/2.03  tff(c_4533, plain, (![A_162, B_163]: (r1_tarski(k3_relat_1(A_162), B_163) | ~r1_tarski(k2_relat_1(A_162), B_163) | ~r1_tarski(k1_relat_1(A_162), B_163) | ~v1_relat_1(A_162))), inference(superposition, [status(thm), theory('equality')], [c_22, c_116])).
% 5.33/2.03  tff(c_28, plain, (~r1_tarski(k3_relat_1('#skF_2'), k3_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.33/2.03  tff(c_4561, plain, (~r1_tarski(k2_relat_1('#skF_2'), k3_relat_1('#skF_3')) | ~r1_tarski(k1_relat_1('#skF_2'), k3_relat_1('#skF_3')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4533, c_28])).
% 5.33/2.03  tff(c_4575, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_4145, c_3773, c_4561])).
% 5.33/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.03  
% 5.33/2.03  Inference rules
% 5.33/2.03  ----------------------
% 5.33/2.03  #Ref     : 0
% 5.33/2.03  #Sup     : 1111
% 5.33/2.03  #Fact    : 0
% 5.33/2.03  #Define  : 0
% 5.33/2.03  #Split   : 3
% 5.33/2.03  #Chain   : 0
% 5.33/2.03  #Close   : 0
% 5.33/2.03  
% 5.33/2.03  Ordering : KBO
% 5.33/2.03  
% 5.33/2.03  Simplification rules
% 5.33/2.03  ----------------------
% 5.33/2.03  #Subsume      : 125
% 5.33/2.03  #Demod        : 659
% 5.33/2.03  #Tautology    : 538
% 5.33/2.03  #SimpNegUnit  : 0
% 5.33/2.03  #BackRed      : 0
% 5.33/2.03  
% 5.33/2.03  #Partial instantiations: 0
% 5.33/2.03  #Strategies tried      : 1
% 5.33/2.03  
% 5.33/2.03  Timing (in seconds)
% 5.33/2.03  ----------------------
% 5.33/2.03  Preprocessing        : 0.29
% 5.33/2.03  Parsing              : 0.15
% 5.33/2.03  CNF conversion       : 0.02
% 5.33/2.03  Main loop            : 0.97
% 5.33/2.03  Inferencing          : 0.31
% 5.33/2.03  Reduction            : 0.34
% 5.33/2.03  Demodulation         : 0.26
% 5.33/2.03  BG Simplification    : 0.04
% 5.33/2.03  Subsumption          : 0.22
% 5.33/2.03  Abstraction          : 0.05
% 5.33/2.03  MUC search           : 0.00
% 5.33/2.03  Cooper               : 0.00
% 5.33/2.03  Total                : 1.30
% 5.33/2.03  Index Insertion      : 0.00
% 5.33/2.03  Index Deletion       : 0.00
% 5.33/2.03  Index Matching       : 0.00
% 5.33/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
