%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:50 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.27s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 162 expanded)
%              Number of leaves         :   24 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  130 ( 388 expanded)
%              Number of equality atoms :   41 ( 131 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_28,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_73,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4,plain,(
    ! [A_2] : v1_relat_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_74,plain,(
    ! [A_23] :
      ( k5_relat_1(A_23,k6_relat_1(k2_relat_1(A_23))) = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_86,plain,(
    ! [A_13] :
      ( k5_relat_1(k6_relat_1(A_13),k6_relat_1(A_13)) = k6_relat_1(A_13)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_74])).

tff(c_90,plain,(
    ! [A_13] : k5_relat_1(k6_relat_1(A_13),k6_relat_1(A_13)) = k6_relat_1(A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_86])).

tff(c_188,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_28,B_29)),k1_relat_1(A_28))
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_200,plain,(
    ! [A_13] :
      ( r1_tarski(k1_relat_1(k6_relat_1(A_13)),k1_relat_1(k6_relat_1(A_13)))
      | ~ v1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_188])).

tff(c_215,plain,(
    ! [A_13] : r1_tarski(A_13,A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_16,c_16,c_200])).

tff(c_32,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_30,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_100,plain,(
    ! [A_25] :
      ( k4_relat_1(A_25) = k2_funct_1(A_25)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_103,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_100])).

tff(c_106,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_103])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_116,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_2])).

tff(c_124,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_116])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_relat_1(k4_relat_1(A_3)) = k2_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_110,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_8])).

tff(c_120,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_110])).

tff(c_500,plain,(
    ! [A_44,B_45] :
      ( k1_relat_1(k5_relat_1(A_44,B_45)) = k1_relat_1(A_44)
      | ~ r1_tarski(k2_relat_1(A_44),k1_relat_1(B_45))
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_521,plain,(
    ! [A_44] :
      ( k1_relat_1(k5_relat_1(A_44,k2_funct_1('#skF_1'))) = k1_relat_1(A_44)
      | ~ r1_tarski(k2_relat_1(A_44),k2_relat_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_500])).

tff(c_1222,plain,(
    ! [A_62] :
      ( k1_relat_1(k5_relat_1(A_62,k2_funct_1('#skF_1'))) = k1_relat_1(A_62)
      | ~ r1_tarski(k2_relat_1(A_62),k2_relat_1('#skF_1'))
      | ~ v1_relat_1(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_521])).

tff(c_1250,plain,
    ( k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_215,c_1222])).

tff(c_1267,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1250])).

tff(c_1269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_1267])).

tff(c_1270,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1302,plain,(
    ! [A_65] :
      ( k4_relat_1(A_65) = k2_funct_1(A_65)
      | ~ v2_funct_1(A_65)
      | ~ v1_funct_1(A_65)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1305,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1302])).

tff(c_1308,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1305])).

tff(c_1318,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1308,c_2])).

tff(c_1326,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1318])).

tff(c_6,plain,(
    ! [A_3] :
      ( k2_relat_1(k4_relat_1(A_3)) = k1_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1315,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1308,c_6])).

tff(c_1324,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1315])).

tff(c_20,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k6_relat_1(k2_relat_1(A_14))) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1390,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_68,B_69)),k1_relat_1(A_68))
      | ~ v1_relat_1(B_69)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2027,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(A_92),B_93)),k2_relat_1(A_92))
      | ~ v1_relat_1(B_93)
      | ~ v1_relat_1(k4_relat_1(A_92))
      | ~ v1_relat_1(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1390])).

tff(c_2062,plain,(
    ! [A_92] :
      ( r1_tarski(k1_relat_1(k4_relat_1(A_92)),k2_relat_1(A_92))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(A_92))))
      | ~ v1_relat_1(k4_relat_1(A_92))
      | ~ v1_relat_1(A_92)
      | ~ v1_relat_1(k4_relat_1(A_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2027])).

tff(c_2166,plain,(
    ! [A_96] :
      ( r1_tarski(k1_relat_1(k4_relat_1(A_96)),k2_relat_1(A_96))
      | ~ v1_relat_1(A_96)
      | ~ v1_relat_1(k4_relat_1(A_96)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2062])).

tff(c_14,plain,(
    ! [B_12,A_10] :
      ( k2_relat_1(k5_relat_1(B_12,A_10)) = k2_relat_1(A_10)
      | ~ r1_tarski(k1_relat_1(A_10),k2_relat_1(B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2241,plain,(
    ! [A_97] :
      ( k2_relat_1(k5_relat_1(A_97,k4_relat_1(A_97))) = k2_relat_1(k4_relat_1(A_97))
      | ~ v1_relat_1(A_97)
      | ~ v1_relat_1(k4_relat_1(A_97)) ) ),
    inference(resolution,[status(thm)],[c_2166,c_14])).

tff(c_2276,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_relat_1(k4_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k4_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1308,c_2241])).

tff(c_2286,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1326,c_1308,c_34,c_1324,c_1308,c_2276])).

tff(c_2288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1270,c_2286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:28:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.04/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.67  
% 4.04/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.67  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 4.04/1.67  
% 4.04/1.67  %Foreground sorts:
% 4.04/1.67  
% 4.04/1.67  
% 4.04/1.67  %Background operators:
% 4.04/1.67  
% 4.04/1.67  
% 4.04/1.67  %Foreground operators:
% 4.04/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.04/1.67  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.04/1.67  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.04/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.04/1.67  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.04/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.04/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.04/1.67  tff('#skF_1', type, '#skF_1': $i).
% 4.04/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.04/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.04/1.67  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.04/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.04/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.04/1.67  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.04/1.67  
% 4.27/1.68  tff(f_99, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 4.27/1.68  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 4.27/1.68  tff(f_66, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.27/1.68  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 4.27/1.68  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 4.27/1.68  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 4.27/1.68  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 4.27/1.68  tff(f_37, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 4.27/1.68  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 4.27/1.68  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 4.27/1.68  tff(c_28, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.27/1.68  tff(c_73, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 4.27/1.68  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.27/1.68  tff(c_4, plain, (![A_2]: (v1_relat_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.27/1.68  tff(c_16, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.27/1.68  tff(c_18, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.27/1.68  tff(c_74, plain, (![A_23]: (k5_relat_1(A_23, k6_relat_1(k2_relat_1(A_23)))=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.27/1.68  tff(c_86, plain, (![A_13]: (k5_relat_1(k6_relat_1(A_13), k6_relat_1(A_13))=k6_relat_1(A_13) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_74])).
% 4.27/1.68  tff(c_90, plain, (![A_13]: (k5_relat_1(k6_relat_1(A_13), k6_relat_1(A_13))=k6_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_86])).
% 4.27/1.68  tff(c_188, plain, (![A_28, B_29]: (r1_tarski(k1_relat_1(k5_relat_1(A_28, B_29)), k1_relat_1(A_28)) | ~v1_relat_1(B_29) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.27/1.68  tff(c_200, plain, (![A_13]: (r1_tarski(k1_relat_1(k6_relat_1(A_13)), k1_relat_1(k6_relat_1(A_13))) | ~v1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_90, c_188])).
% 4.27/1.68  tff(c_215, plain, (![A_13]: (r1_tarski(A_13, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_16, c_16, c_200])).
% 4.27/1.68  tff(c_32, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.27/1.68  tff(c_30, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.27/1.68  tff(c_100, plain, (![A_25]: (k4_relat_1(A_25)=k2_funct_1(A_25) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.27/1.68  tff(c_103, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_30, c_100])).
% 4.27/1.68  tff(c_106, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_103])).
% 4.27/1.68  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.27/1.68  tff(c_116, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_106, c_2])).
% 4.27/1.68  tff(c_124, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_116])).
% 4.27/1.68  tff(c_8, plain, (![A_3]: (k1_relat_1(k4_relat_1(A_3))=k2_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.27/1.68  tff(c_110, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_106, c_8])).
% 4.27/1.68  tff(c_120, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_110])).
% 4.27/1.68  tff(c_500, plain, (![A_44, B_45]: (k1_relat_1(k5_relat_1(A_44, B_45))=k1_relat_1(A_44) | ~r1_tarski(k2_relat_1(A_44), k1_relat_1(B_45)) | ~v1_relat_1(B_45) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.27/1.68  tff(c_521, plain, (![A_44]: (k1_relat_1(k5_relat_1(A_44, k2_funct_1('#skF_1')))=k1_relat_1(A_44) | ~r1_tarski(k2_relat_1(A_44), k2_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_44))), inference(superposition, [status(thm), theory('equality')], [c_120, c_500])).
% 4.27/1.68  tff(c_1222, plain, (![A_62]: (k1_relat_1(k5_relat_1(A_62, k2_funct_1('#skF_1')))=k1_relat_1(A_62) | ~r1_tarski(k2_relat_1(A_62), k2_relat_1('#skF_1')) | ~v1_relat_1(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_521])).
% 4.27/1.68  tff(c_1250, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_215, c_1222])).
% 4.27/1.68  tff(c_1267, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1250])).
% 4.27/1.68  tff(c_1269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_1267])).
% 4.27/1.68  tff(c_1270, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 4.27/1.68  tff(c_1302, plain, (![A_65]: (k4_relat_1(A_65)=k2_funct_1(A_65) | ~v2_funct_1(A_65) | ~v1_funct_1(A_65) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.27/1.68  tff(c_1305, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1302])).
% 4.27/1.68  tff(c_1308, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1305])).
% 4.27/1.68  tff(c_1318, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1308, c_2])).
% 4.27/1.68  tff(c_1326, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1318])).
% 4.27/1.68  tff(c_6, plain, (![A_3]: (k2_relat_1(k4_relat_1(A_3))=k1_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.27/1.68  tff(c_1315, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1308, c_6])).
% 4.27/1.68  tff(c_1324, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1315])).
% 4.27/1.68  tff(c_20, plain, (![A_14]: (k5_relat_1(A_14, k6_relat_1(k2_relat_1(A_14)))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.27/1.68  tff(c_1390, plain, (![A_68, B_69]: (r1_tarski(k1_relat_1(k5_relat_1(A_68, B_69)), k1_relat_1(A_68)) | ~v1_relat_1(B_69) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.27/1.68  tff(c_2027, plain, (![A_92, B_93]: (r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(A_92), B_93)), k2_relat_1(A_92)) | ~v1_relat_1(B_93) | ~v1_relat_1(k4_relat_1(A_92)) | ~v1_relat_1(A_92))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1390])).
% 4.27/1.68  tff(c_2062, plain, (![A_92]: (r1_tarski(k1_relat_1(k4_relat_1(A_92)), k2_relat_1(A_92)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k4_relat_1(A_92)))) | ~v1_relat_1(k4_relat_1(A_92)) | ~v1_relat_1(A_92) | ~v1_relat_1(k4_relat_1(A_92)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2027])).
% 4.27/1.68  tff(c_2166, plain, (![A_96]: (r1_tarski(k1_relat_1(k4_relat_1(A_96)), k2_relat_1(A_96)) | ~v1_relat_1(A_96) | ~v1_relat_1(k4_relat_1(A_96)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2062])).
% 4.27/1.68  tff(c_14, plain, (![B_12, A_10]: (k2_relat_1(k5_relat_1(B_12, A_10))=k2_relat_1(A_10) | ~r1_tarski(k1_relat_1(A_10), k2_relat_1(B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.27/1.68  tff(c_2241, plain, (![A_97]: (k2_relat_1(k5_relat_1(A_97, k4_relat_1(A_97)))=k2_relat_1(k4_relat_1(A_97)) | ~v1_relat_1(A_97) | ~v1_relat_1(k4_relat_1(A_97)))), inference(resolution, [status(thm)], [c_2166, c_14])).
% 4.27/1.68  tff(c_2276, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_relat_1(k4_relat_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k4_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1308, c_2241])).
% 4.27/1.68  tff(c_2286, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1326, c_1308, c_34, c_1324, c_1308, c_2276])).
% 4.27/1.68  tff(c_2288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1270, c_2286])).
% 4.27/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.27/1.68  
% 4.27/1.68  Inference rules
% 4.27/1.68  ----------------------
% 4.27/1.68  #Ref     : 0
% 4.27/1.68  #Sup     : 526
% 4.27/1.68  #Fact    : 0
% 4.27/1.68  #Define  : 0
% 4.27/1.68  #Split   : 9
% 4.27/1.68  #Chain   : 0
% 4.27/1.68  #Close   : 0
% 4.27/1.68  
% 4.27/1.68  Ordering : KBO
% 4.27/1.68  
% 4.27/1.68  Simplification rules
% 4.27/1.68  ----------------------
% 4.27/1.68  #Subsume      : 26
% 4.27/1.68  #Demod        : 565
% 4.27/1.68  #Tautology    : 230
% 4.27/1.68  #SimpNegUnit  : 2
% 4.27/1.68  #BackRed      : 0
% 4.27/1.68  
% 4.27/1.68  #Partial instantiations: 0
% 4.27/1.68  #Strategies tried      : 1
% 4.27/1.68  
% 4.27/1.68  Timing (in seconds)
% 4.27/1.68  ----------------------
% 4.27/1.69  Preprocessing        : 0.31
% 4.27/1.69  Parsing              : 0.16
% 4.27/1.69  CNF conversion       : 0.02
% 4.27/1.69  Main loop            : 0.60
% 4.27/1.69  Inferencing          : 0.21
% 4.27/1.69  Reduction            : 0.22
% 4.27/1.69  Demodulation         : 0.17
% 4.27/1.69  BG Simplification    : 0.03
% 4.27/1.69  Subsumption          : 0.10
% 4.27/1.69  Abstraction          : 0.03
% 4.27/1.69  MUC search           : 0.00
% 4.27/1.69  Cooper               : 0.00
% 4.27/1.69  Total                : 0.94
% 4.27/1.69  Index Insertion      : 0.00
% 4.27/1.69  Index Deletion       : 0.00
% 4.27/1.69  Index Matching       : 0.00
% 4.27/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
