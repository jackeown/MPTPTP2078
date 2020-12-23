%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:56 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 185 expanded)
%              Number of leaves         :   25 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  155 ( 499 expanded)
%              Number of equality atoms :   62 ( 207 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k2_relat_1(A) = k2_relat_1(B)
               => k2_relat_1(k5_relat_1(A,C)) = k2_relat_1(k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_34,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_32,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_26,plain,(
    ! [A_24] :
      ( k2_relat_1(k2_funct_1(A_24)) = k1_relat_1(A_24)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2,plain,(
    ! [A_1] :
      ( k9_relat_1(A_1,k1_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( k2_relat_1(k7_relat_1(B_3,A_2)) = k9_relat_1(B_3,A_2)
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_22] :
      ( v1_relat_1(k2_funct_1(A_22))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [A_23] : v1_relat_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12,plain,(
    ! [A_18] : k2_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [A_20,B_21] :
      ( k5_relat_1(k6_relat_1(A_20),B_21) = k7_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1054,plain,(
    ! [B_79,C_80,A_81] :
      ( k2_relat_1(k5_relat_1(B_79,C_80)) = k2_relat_1(k5_relat_1(A_81,C_80))
      | k2_relat_1(B_79) != k2_relat_1(A_81)
      | ~ v1_relat_1(C_80)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1096,plain,(
    ! [B_21,A_20,B_79] :
      ( k2_relat_1(k7_relat_1(B_21,A_20)) = k2_relat_1(k5_relat_1(B_79,B_21))
      | k2_relat_1(k6_relat_1(A_20)) != k2_relat_1(B_79)
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1054])).

tff(c_1178,plain,(
    ! [B_84,A_85,B_86] :
      ( k2_relat_1(k7_relat_1(B_84,A_85)) = k2_relat_1(k5_relat_1(B_86,B_84))
      | k2_relat_1(B_86) != A_85
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_12,c_1096])).

tff(c_28,plain,(
    ! [A_24] :
      ( k1_relat_1(k2_funct_1(A_24)) = k2_relat_1(A_24)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_450,plain,(
    ! [C_53,B_54,A_55] :
      ( k1_relat_1(k5_relat_1(C_53,B_54)) = k1_relat_1(k5_relat_1(C_53,A_55))
      | k1_relat_1(B_54) != k1_relat_1(A_55)
      | ~ v1_relat_1(C_53)
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_59,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_480,plain,(
    ! [A_55] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),A_55)) != k2_relat_1('#skF_1')
      | k1_relat_1(A_55) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_59])).

tff(c_526,plain,(
    ! [A_55] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),A_55)) != k2_relat_1('#skF_1')
      | k1_relat_1(A_55) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_480])).

tff(c_856,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_526])).

tff(c_859,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_856])).

tff(c_863,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_859])).

tff(c_865,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_526])).

tff(c_10,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_19] :
      ( k5_relat_1(A_19,k6_relat_1(k2_relat_1(A_19))) = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_519,plain,(
    ! [A_19,A_55] :
      ( k1_relat_1(k5_relat_1(A_19,A_55)) = k1_relat_1(A_19)
      | k1_relat_1(k6_relat_1(k2_relat_1(A_19))) != k1_relat_1(A_55)
      | ~ v1_relat_1(A_19)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_19)))
      | ~ v1_relat_1(A_55)
      | ~ v1_relat_1(A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_450])).

tff(c_763,plain,(
    ! [A_64,A_65] :
      ( k1_relat_1(k5_relat_1(A_64,A_65)) = k1_relat_1(A_64)
      | k2_relat_1(A_64) != k1_relat_1(A_65)
      | ~ v1_relat_1(A_65)
      | ~ v1_relat_1(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_10,c_519])).

tff(c_785,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_59])).

tff(c_817,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_785])).

tff(c_855,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_817])).

tff(c_867,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_865,c_855])).

tff(c_868,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_817])).

tff(c_870,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_868])).

tff(c_873,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_870])).

tff(c_877,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_873])).

tff(c_878,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_868])).

tff(c_908,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_878])).

tff(c_912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_908])).

tff(c_913,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1206,plain,(
    ! [A_85] :
      ( k2_relat_1(k7_relat_1('#skF_1',A_85)) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != A_85
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1178,c_913])).

tff(c_1240,plain,(
    ! [A_85] :
      ( k2_relat_1(k7_relat_1('#skF_1',A_85)) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != A_85
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1206])).

tff(c_1253,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1240])).

tff(c_1256,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1253])).

tff(c_1260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1256])).

tff(c_1264,plain,(
    ! [A_87] :
      ( k2_relat_1(k7_relat_1('#skF_1',A_87)) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != A_87 ) ),
    inference(splitRight,[status(thm)],[c_1240])).

tff(c_1272,plain,(
    ! [A_2] :
      ( k9_relat_1('#skF_1',A_2) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != A_2
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1264])).

tff(c_1278,plain,(
    ! [A_88] :
      ( k9_relat_1('#skF_1',A_88) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != A_88 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1272])).

tff(c_1281,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1278])).

tff(c_1284,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1281])).

tff(c_1287,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1284])).

tff(c_1291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_1287])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.30  % Computer   : n003.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % DateTime   : Tue Dec  1 20:37:27 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.11/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.45  
% 3.28/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.46  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.28/1.46  
% 3.28/1.46  %Foreground sorts:
% 3.28/1.46  
% 3.28/1.46  
% 3.28/1.46  %Background operators:
% 3.28/1.46  
% 3.28/1.46  
% 3.28/1.46  %Foreground operators:
% 3.28/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.28/1.46  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.28/1.46  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.28/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.28/1.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.28/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.28/1.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.28/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.28/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.28/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.28/1.46  
% 3.28/1.47  tff(f_102, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 3.28/1.47  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.28/1.47  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.28/1.47  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.28/1.47  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.28/1.47  tff(f_81, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.28/1.47  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.28/1.47  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.28/1.47  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k2_relat_1(A) = k2_relat_1(B)) => (k2_relat_1(k5_relat_1(A, C)) = k2_relat_1(k5_relat_1(B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t199_relat_1)).
% 3.28/1.47  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t198_relat_1)).
% 3.28/1.47  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 3.28/1.47  tff(c_36, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.28/1.47  tff(c_34, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.28/1.47  tff(c_32, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.28/1.47  tff(c_26, plain, (![A_24]: (k2_relat_1(k2_funct_1(A_24))=k1_relat_1(A_24) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.28/1.47  tff(c_2, plain, (![A_1]: (k9_relat_1(A_1, k1_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.28/1.47  tff(c_4, plain, (![B_3, A_2]: (k2_relat_1(k7_relat_1(B_3, A_2))=k9_relat_1(B_3, A_2) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.28/1.47  tff(c_20, plain, (![A_22]: (v1_relat_1(k2_funct_1(A_22)) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.28/1.47  tff(c_22, plain, (![A_23]: (v1_relat_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.28/1.47  tff(c_12, plain, (![A_18]: (k2_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.28/1.47  tff(c_16, plain, (![A_20, B_21]: (k5_relat_1(k6_relat_1(A_20), B_21)=k7_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.28/1.47  tff(c_1054, plain, (![B_79, C_80, A_81]: (k2_relat_1(k5_relat_1(B_79, C_80))=k2_relat_1(k5_relat_1(A_81, C_80)) | k2_relat_1(B_79)!=k2_relat_1(A_81) | ~v1_relat_1(C_80) | ~v1_relat_1(B_79) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.28/1.47  tff(c_1096, plain, (![B_21, A_20, B_79]: (k2_relat_1(k7_relat_1(B_21, A_20))=k2_relat_1(k5_relat_1(B_79, B_21)) | k2_relat_1(k6_relat_1(A_20))!=k2_relat_1(B_79) | ~v1_relat_1(B_21) | ~v1_relat_1(B_79) | ~v1_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(B_21))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1054])).
% 3.28/1.47  tff(c_1178, plain, (![B_84, A_85, B_86]: (k2_relat_1(k7_relat_1(B_84, A_85))=k2_relat_1(k5_relat_1(B_86, B_84)) | k2_relat_1(B_86)!=A_85 | ~v1_relat_1(B_86) | ~v1_relat_1(B_84))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_12, c_1096])).
% 3.28/1.47  tff(c_28, plain, (![A_24]: (k1_relat_1(k2_funct_1(A_24))=k2_relat_1(A_24) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.28/1.47  tff(c_450, plain, (![C_53, B_54, A_55]: (k1_relat_1(k5_relat_1(C_53, B_54))=k1_relat_1(k5_relat_1(C_53, A_55)) | k1_relat_1(B_54)!=k1_relat_1(A_55) | ~v1_relat_1(C_53) | ~v1_relat_1(B_54) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.28/1.47  tff(c_30, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.28/1.47  tff(c_59, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 3.28/1.47  tff(c_480, plain, (![A_55]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), A_55))!=k2_relat_1('#skF_1') | k1_relat_1(A_55)!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_55))), inference(superposition, [status(thm), theory('equality')], [c_450, c_59])).
% 3.28/1.47  tff(c_526, plain, (![A_55]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), A_55))!=k2_relat_1('#skF_1') | k1_relat_1(A_55)!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_55))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_480])).
% 3.28/1.47  tff(c_856, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_526])).
% 3.28/1.47  tff(c_859, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_856])).
% 3.28/1.47  tff(c_863, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_859])).
% 3.28/1.47  tff(c_865, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_526])).
% 3.28/1.47  tff(c_10, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.28/1.47  tff(c_14, plain, (![A_19]: (k5_relat_1(A_19, k6_relat_1(k2_relat_1(A_19)))=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.28/1.47  tff(c_519, plain, (![A_19, A_55]: (k1_relat_1(k5_relat_1(A_19, A_55))=k1_relat_1(A_19) | k1_relat_1(k6_relat_1(k2_relat_1(A_19)))!=k1_relat_1(A_55) | ~v1_relat_1(A_19) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_19))) | ~v1_relat_1(A_55) | ~v1_relat_1(A_19))), inference(superposition, [status(thm), theory('equality')], [c_14, c_450])).
% 3.28/1.47  tff(c_763, plain, (![A_64, A_65]: (k1_relat_1(k5_relat_1(A_64, A_65))=k1_relat_1(A_64) | k2_relat_1(A_64)!=k1_relat_1(A_65) | ~v1_relat_1(A_65) | ~v1_relat_1(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_10, c_519])).
% 3.28/1.47  tff(c_785, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_763, c_59])).
% 3.28/1.47  tff(c_817, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_785])).
% 3.28/1.47  tff(c_855, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_817])).
% 3.28/1.47  tff(c_867, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_865, c_855])).
% 3.28/1.47  tff(c_868, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_817])).
% 3.28/1.47  tff(c_870, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_868])).
% 3.28/1.47  tff(c_873, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_870])).
% 3.28/1.47  tff(c_877, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_873])).
% 3.28/1.47  tff(c_878, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_868])).
% 3.28/1.47  tff(c_908, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_878])).
% 3.28/1.47  tff(c_912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_908])).
% 3.28/1.47  tff(c_913, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 3.28/1.47  tff(c_1206, plain, (![A_85]: (k2_relat_1(k7_relat_1('#skF_1', A_85))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=A_85 | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1178, c_913])).
% 3.28/1.47  tff(c_1240, plain, (![A_85]: (k2_relat_1(k7_relat_1('#skF_1', A_85))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=A_85 | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1206])).
% 3.28/1.47  tff(c_1253, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1240])).
% 3.28/1.47  tff(c_1256, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_1253])).
% 3.28/1.47  tff(c_1260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1256])).
% 3.28/1.47  tff(c_1264, plain, (![A_87]: (k2_relat_1(k7_relat_1('#skF_1', A_87))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=A_87)), inference(splitRight, [status(thm)], [c_1240])).
% 3.28/1.47  tff(c_1272, plain, (![A_2]: (k9_relat_1('#skF_1', A_2)!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=A_2 | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1264])).
% 3.28/1.47  tff(c_1278, plain, (![A_88]: (k9_relat_1('#skF_1', A_88)!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=A_88)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1272])).
% 3.28/1.47  tff(c_1281, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2, c_1278])).
% 3.28/1.47  tff(c_1284, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1281])).
% 3.28/1.47  tff(c_1287, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_1284])).
% 3.28/1.47  tff(c_1291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_1287])).
% 3.28/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.47  
% 3.28/1.47  Inference rules
% 3.28/1.47  ----------------------
% 3.28/1.47  #Ref     : 0
% 3.28/1.47  #Sup     : 280
% 3.28/1.47  #Fact    : 0
% 3.28/1.47  #Define  : 0
% 3.28/1.47  #Split   : 6
% 3.28/1.47  #Chain   : 0
% 3.28/1.47  #Close   : 0
% 3.28/1.47  
% 3.28/1.47  Ordering : KBO
% 3.28/1.47  
% 3.28/1.47  Simplification rules
% 3.28/1.47  ----------------------
% 3.28/1.47  #Subsume      : 10
% 3.28/1.47  #Demod        : 248
% 3.28/1.47  #Tautology    : 103
% 3.28/1.47  #SimpNegUnit  : 0
% 3.28/1.47  #BackRed      : 0
% 3.28/1.47  
% 3.28/1.47  #Partial instantiations: 0
% 3.28/1.47  #Strategies tried      : 1
% 3.28/1.47  
% 3.28/1.47  Timing (in seconds)
% 3.28/1.47  ----------------------
% 3.28/1.47  Preprocessing        : 0.31
% 3.28/1.47  Parsing              : 0.18
% 3.28/1.47  CNF conversion       : 0.02
% 3.28/1.47  Main loop            : 0.45
% 3.28/1.47  Inferencing          : 0.18
% 3.28/1.47  Reduction            : 0.14
% 3.28/1.47  Demodulation         : 0.10
% 3.28/1.48  BG Simplification    : 0.03
% 3.28/1.48  Subsumption          : 0.07
% 3.28/1.48  Abstraction          : 0.03
% 3.28/1.48  MUC search           : 0.00
% 3.28/1.48  Cooper               : 0.00
% 3.28/1.48  Total                : 0.78
% 3.28/1.48  Index Insertion      : 0.00
% 3.28/1.48  Index Deletion       : 0.00
% 3.28/1.48  Index Matching       : 0.00
% 3.28/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
