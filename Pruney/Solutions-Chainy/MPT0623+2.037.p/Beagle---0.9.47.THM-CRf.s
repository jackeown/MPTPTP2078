%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:11 EST 2020

% Result     : Theorem 10.99s
% Output     : CNFRefutation 11.26s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 577 expanded)
%              Number of leaves         :   33 ( 194 expanded)
%              Depth                    :   17
%              Number of atoms          :  227 (1504 expanded)
%              Number of equality atoms :  114 ( 861 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_8 > #skF_3 > #skF_10 > #skF_7 > #skF_2 > #skF_1 > #skF_9 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_52,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_85,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_72,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_60,plain,
    ( k1_xboole_0 = '#skF_11'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_81,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_458,plain,(
    ! [A_128,C_129] :
      ( r2_hidden(k4_tarski('#skF_7'(A_128,k2_relat_1(A_128),C_129),C_129),A_128)
      | ~ r2_hidden(C_129,k2_relat_1(A_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_476,plain,(
    ! [C_129] :
      ( r2_hidden(k4_tarski('#skF_7'(k1_xboole_0,k1_xboole_0,C_129),C_129),k1_xboole_0)
      | ~ r2_hidden(C_129,k2_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_458])).

tff(c_487,plain,(
    ! [C_132] :
      ( r2_hidden(k4_tarski('#skF_7'(k1_xboole_0,k1_xboole_0,C_132),C_132),k1_xboole_0)
      | ~ r2_hidden(C_132,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_476])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_495,plain,(
    ! [C_132,B_2] :
      ( r2_hidden(k4_tarski('#skF_7'(k1_xboole_0,k1_xboole_0,C_132),C_132),B_2)
      | ~ r1_tarski(k1_xboole_0,B_2)
      | ~ r2_hidden(C_132,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_487,c_2])).

tff(c_501,plain,(
    ! [C_132,B_2] :
      ( r2_hidden(k4_tarski('#skF_7'(k1_xboole_0,k1_xboole_0,C_132),C_132),B_2)
      | ~ r2_hidden(C_132,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_495])).

tff(c_52,plain,(
    ! [A_38,B_42] :
      ( k1_relat_1('#skF_9'(A_38,B_42)) = A_38
      | k1_xboole_0 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_54,plain,(
    ! [A_38,B_42] :
      ( v1_funct_1('#skF_9'(A_38,B_42))
      | k1_xboole_0 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_56,plain,(
    ! [A_38,B_42] :
      ( v1_relat_1('#skF_9'(A_38,B_42))
      | k1_xboole_0 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_236,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_1'(A_70,B_71),A_70)
      | r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_304,plain,(
    ! [A_91,B_92] :
      ( '#skF_1'(k1_tarski(A_91),B_92) = A_91
      | r1_tarski(k1_tarski(A_91),B_92) ) ),
    inference(resolution,[status(thm)],[c_236,c_10])).

tff(c_243,plain,(
    ! [A_72,B_73] :
      ( k2_relat_1('#skF_9'(A_72,B_73)) = k1_tarski(B_73)
      | k1_xboole_0 = A_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_58,plain,(
    ! [C_45] :
      ( ~ r1_tarski(k2_relat_1(C_45),'#skF_10')
      | k1_relat_1(C_45) != '#skF_11'
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_249,plain,(
    ! [B_73,A_72] :
      ( ~ r1_tarski(k1_tarski(B_73),'#skF_10')
      | k1_relat_1('#skF_9'(A_72,B_73)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_72,B_73))
      | ~ v1_relat_1('#skF_9'(A_72,B_73))
      | k1_xboole_0 = A_72 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_58])).

tff(c_374,plain,(
    ! [A_108,A_109] :
      ( k1_relat_1('#skF_9'(A_108,A_109)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_108,A_109))
      | ~ v1_relat_1('#skF_9'(A_108,A_109))
      | k1_xboole_0 = A_108
      | '#skF_1'(k1_tarski(A_109),'#skF_10') = A_109 ) ),
    inference(resolution,[status(thm)],[c_304,c_249])).

tff(c_482,plain,(
    ! [A_130,B_131] :
      ( k1_relat_1('#skF_9'(A_130,B_131)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_130,B_131))
      | '#skF_1'(k1_tarski(B_131),'#skF_10') = B_131
      | k1_xboole_0 = A_130 ) ),
    inference(resolution,[status(thm)],[c_56,c_374])).

tff(c_831,plain,(
    ! [A_1885,B_1886] :
      ( k1_relat_1('#skF_9'(A_1885,B_1886)) != '#skF_11'
      | '#skF_1'(k1_tarski(B_1886),'#skF_10') = B_1886
      | k1_xboole_0 = A_1885 ) ),
    inference(resolution,[status(thm)],[c_54,c_482])).

tff(c_834,plain,(
    ! [A_38,B_42] :
      ( A_38 != '#skF_11'
      | '#skF_1'(k1_tarski(B_42),'#skF_10') = B_42
      | k1_xboole_0 = A_38
      | k1_xboole_0 = A_38 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_831])).

tff(c_13900,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_834])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_83,plain,(
    ! [C_51] :
      ( ~ r1_tarski(k2_relat_1(C_51),'#skF_10')
      | k1_relat_1(C_51) != '#skF_11'
      | ~ v1_funct_1(C_51)
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_86,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_10')
    | k1_relat_1(k1_xboole_0) != '#skF_11'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_83])).

tff(c_88,plain,
    ( k1_xboole_0 != '#skF_11'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8,c_86])).

tff(c_97,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_44,plain,(
    ! [A_32] : k1_relat_1('#skF_8'(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_48,plain,(
    ! [A_32] : v1_relat_1('#skF_8'(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_108,plain,(
    ! [A_60] :
      ( k1_relat_1(A_60) != k1_xboole_0
      | k1_xboole_0 = A_60
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_114,plain,(
    ! [A_32] :
      ( k1_relat_1('#skF_8'(A_32)) != k1_xboole_0
      | '#skF_8'(A_32) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_48,c_108])).

tff(c_119,plain,(
    ! [A_61] :
      ( k1_xboole_0 != A_61
      | '#skF_8'(A_61) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_114])).

tff(c_129,plain,(
    ! [A_61] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_61 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_48])).

tff(c_135,plain,(
    ! [A_61] : k1_xboole_0 != A_61 ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_129])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_34])).

tff(c_145,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != '#skF_11' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_147,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_13953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13900,c_147])).

tff(c_13956,plain,(
    ! [B_12409] : '#skF_1'(k1_tarski(B_12409),'#skF_10') = B_12409 ),
    inference(splitRight,[status(thm)],[c_834])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_13995,plain,(
    ! [B_12460] :
      ( ~ r2_hidden(B_12460,'#skF_10')
      | r1_tarski(k1_tarski(B_12460),'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13956,c_4])).

tff(c_14563,plain,(
    ! [A_12768,B_12769] :
      ( k1_relat_1('#skF_9'(A_12768,B_12769)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_12768,B_12769))
      | ~ v1_relat_1('#skF_9'(A_12768,B_12769))
      | k1_xboole_0 = A_12768
      | ~ r2_hidden(B_12769,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_13995,c_249])).

tff(c_36692,plain,(
    ! [A_21865,B_21866] :
      ( k1_relat_1('#skF_9'(A_21865,B_21866)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_21865,B_21866))
      | ~ r2_hidden(B_21866,'#skF_10')
      | k1_xboole_0 = A_21865 ) ),
    inference(resolution,[status(thm)],[c_56,c_14563])).

tff(c_36701,plain,(
    ! [A_21917,B_21918] :
      ( k1_relat_1('#skF_9'(A_21917,B_21918)) != '#skF_11'
      | ~ r2_hidden(B_21918,'#skF_10')
      | k1_xboole_0 = A_21917 ) ),
    inference(resolution,[status(thm)],[c_54,c_36692])).

tff(c_36712,plain,(
    ! [A_38,B_42] :
      ( A_38 != '#skF_11'
      | ~ r2_hidden(B_42,'#skF_10')
      | k1_xboole_0 = A_38
      | k1_xboole_0 = A_38 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_36701])).

tff(c_36714,plain,(
    ! [B_21969] : ~ r2_hidden(B_21969,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_36712])).

tff(c_36798,plain,(
    ! [C_132] : ~ r2_hidden(C_132,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_501,c_36714])).

tff(c_12044,plain,(
    ! [A_9294,B_9295] :
      ( r2_hidden(k4_tarski('#skF_5'(A_9294,B_9295),'#skF_4'(A_9294,B_9295)),A_9294)
      | r2_hidden('#skF_6'(A_9294,B_9295),B_9295)
      | k2_relat_1(A_9294) = B_9295 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ! [C_27,A_12,D_30] :
      ( r2_hidden(C_27,k2_relat_1(A_12))
      | ~ r2_hidden(k4_tarski(D_30,C_27),A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12206,plain,(
    ! [A_9402,B_9403] :
      ( r2_hidden('#skF_4'(A_9402,B_9403),k2_relat_1(A_9402))
      | r2_hidden('#skF_6'(A_9402,B_9403),B_9403)
      | k2_relat_1(A_9402) = B_9403 ) ),
    inference(resolution,[status(thm)],[c_12044,c_24])).

tff(c_12235,plain,(
    ! [B_9403] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_9403),k1_xboole_0)
      | r2_hidden('#skF_6'(k1_xboole_0,B_9403),B_9403)
      | k2_relat_1(k1_xboole_0) = B_9403 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_12206])).

tff(c_12241,plain,(
    ! [B_9403] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_9403),k1_xboole_0)
      | r2_hidden('#skF_6'(k1_xboole_0,B_9403),B_9403)
      | k1_xboole_0 = B_9403 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_12235])).

tff(c_36923,plain,(
    ! [B_22022] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_22022),B_22022)
      | k1_xboole_0 = B_22022 ) ),
    inference(negUnitSimplification,[status(thm)],[c_36798,c_12241])).

tff(c_36713,plain,(
    ! [B_42] : ~ r2_hidden(B_42,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_36712])).

tff(c_36931,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_36923,c_36713])).

tff(c_36958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_36931])).

tff(c_36960,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_36712])).

tff(c_37020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36960,c_147])).

tff(c_37022,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_37021,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_37023,plain,(
    ~ v1_funct_1('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37022,c_37021])).

tff(c_40,plain,(
    ! [A_31] :
      ( k1_relat_1(A_31) != k1_xboole_0
      | k1_xboole_0 = A_31
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_37050,plain,(
    ! [A_22024] :
      ( k1_relat_1(A_22024) != '#skF_11'
      | A_22024 = '#skF_11'
      | ~ v1_relat_1(A_22024) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37022,c_37022,c_40])).

tff(c_37056,plain,(
    ! [A_32] :
      ( k1_relat_1('#skF_8'(A_32)) != '#skF_11'
      | '#skF_8'(A_32) = '#skF_11' ) ),
    inference(resolution,[status(thm)],[c_48,c_37050])).

tff(c_37064,plain,(
    ! [A_22025] :
      ( A_22025 != '#skF_11'
      | '#skF_8'(A_22025) = '#skF_11' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_37056])).

tff(c_46,plain,(
    ! [A_32] : v1_funct_1('#skF_8'(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_37072,plain,(
    ! [A_22025] :
      ( v1_funct_1('#skF_11')
      | A_22025 != '#skF_11' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37064,c_46])).

tff(c_37080,plain,(
    ! [A_22025] : A_22025 != '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_37023,c_37072])).

tff(c_37030,plain,(
    k1_relat_1('#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37022,c_37022,c_36])).

tff(c_37088,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37080,c_37030])).

tff(c_37090,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_37089,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_37099,plain,(
    '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37090,c_37089])).

tff(c_37093,plain,(
    k1_relat_1('#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37089,c_37089,c_36])).

tff(c_37109,plain,(
    k1_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37099,c_37099,c_37093])).

tff(c_37092,plain,(
    ! [A_6] : r1_tarski('#skF_11',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37089,c_8])).

tff(c_37114,plain,(
    ! [A_6] : r1_tarski('#skF_10',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37099,c_37092])).

tff(c_37091,plain,(
    k2_relat_1('#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37089,c_37089,c_34])).

tff(c_37116,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37099,c_37099,c_37091])).

tff(c_37132,plain,(
    ! [C_22035] :
      ( ~ r1_tarski(k2_relat_1(C_22035),'#skF_10')
      | k1_relat_1(C_22035) != '#skF_10'
      | ~ v1_funct_1(C_22035)
      | ~ v1_relat_1(C_22035) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37099,c_58])).

tff(c_37135,plain,
    ( ~ r1_tarski('#skF_10','#skF_10')
    | k1_relat_1('#skF_10') != '#skF_10'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_37116,c_37132])).

tff(c_37137,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37109,c_37114,c_37135])).

tff(c_37138,plain,(
    ~ v1_relat_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_37137])).

tff(c_37151,plain,(
    ! [A_22038] :
      ( k1_relat_1(A_22038) != '#skF_10'
      | A_22038 = '#skF_10'
      | ~ v1_relat_1(A_22038) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37090,c_37090,c_40])).

tff(c_37157,plain,(
    ! [A_32] :
      ( k1_relat_1('#skF_8'(A_32)) != '#skF_10'
      | '#skF_8'(A_32) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_48,c_37151])).

tff(c_37162,plain,(
    ! [A_22039] :
      ( A_22039 != '#skF_10'
      | '#skF_8'(A_22039) = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_37157])).

tff(c_37172,plain,(
    ! [A_22039] :
      ( v1_relat_1('#skF_10')
      | A_22039 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37162,c_48])).

tff(c_37178,plain,(
    ! [A_22039] : A_22039 != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_37138,c_37172])).

tff(c_37200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37178,c_37116])).

tff(c_37201,plain,(
    ~ v1_funct_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_37137])).

tff(c_37204,plain,(
    ! [A_22041] :
      ( k1_relat_1(A_22041) != '#skF_10'
      | A_22041 = '#skF_10'
      | ~ v1_relat_1(A_22041) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37090,c_37090,c_40])).

tff(c_37213,plain,(
    ! [A_32] :
      ( k1_relat_1('#skF_8'(A_32)) != '#skF_10'
      | '#skF_8'(A_32) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_48,c_37204])).

tff(c_37222,plain,(
    ! [A_22042] :
      ( A_22042 != '#skF_10'
      | '#skF_8'(A_22042) = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_37213])).

tff(c_37230,plain,(
    ! [A_22042] :
      ( v1_funct_1('#skF_10')
      | A_22042 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37222,c_46])).

tff(c_37238,plain,(
    ! [A_22042] : A_22042 != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_37201,c_37230])).

tff(c_37249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37238,c_37116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.99/4.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.99/4.12  
% 10.99/4.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.99/4.12  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_8 > #skF_3 > #skF_10 > #skF_7 > #skF_2 > #skF_1 > #skF_9 > #skF_5 > #skF_4
% 10.99/4.12  
% 10.99/4.12  %Foreground sorts:
% 10.99/4.12  
% 10.99/4.12  
% 10.99/4.12  %Background operators:
% 10.99/4.12  
% 10.99/4.12  
% 10.99/4.12  %Foreground operators:
% 10.99/4.12  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 10.99/4.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.99/4.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.99/4.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.99/4.12  tff('#skF_11', type, '#skF_11': $i).
% 10.99/4.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.99/4.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.99/4.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.99/4.12  tff('#skF_8', type, '#skF_8': $i > $i).
% 10.99/4.12  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.99/4.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.99/4.12  tff('#skF_10', type, '#skF_10': $i).
% 10.99/4.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.99/4.12  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 10.99/4.12  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.99/4.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.99/4.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.99/4.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.99/4.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.99/4.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.99/4.12  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 10.99/4.12  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 10.99/4.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.99/4.12  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.99/4.12  
% 11.26/4.14  tff(f_103, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 11.26/4.14  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.26/4.14  tff(f_52, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 11.26/4.14  tff(f_49, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 11.26/4.14  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.26/4.14  tff(f_85, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 11.26/4.14  tff(f_41, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 11.26/4.14  tff(f_72, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 11.26/4.14  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 11.26/4.14  tff(c_60, plain, (k1_xboole_0='#skF_11' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.26/4.14  tff(c_81, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_60])).
% 11.26/4.14  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.26/4.14  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.26/4.14  tff(c_458, plain, (![A_128, C_129]: (r2_hidden(k4_tarski('#skF_7'(A_128, k2_relat_1(A_128), C_129), C_129), A_128) | ~r2_hidden(C_129, k2_relat_1(A_128)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.26/4.14  tff(c_476, plain, (![C_129]: (r2_hidden(k4_tarski('#skF_7'(k1_xboole_0, k1_xboole_0, C_129), C_129), k1_xboole_0) | ~r2_hidden(C_129, k2_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_458])).
% 11.26/4.14  tff(c_487, plain, (![C_132]: (r2_hidden(k4_tarski('#skF_7'(k1_xboole_0, k1_xboole_0, C_132), C_132), k1_xboole_0) | ~r2_hidden(C_132, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_476])).
% 11.26/4.14  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.26/4.14  tff(c_495, plain, (![C_132, B_2]: (r2_hidden(k4_tarski('#skF_7'(k1_xboole_0, k1_xboole_0, C_132), C_132), B_2) | ~r1_tarski(k1_xboole_0, B_2) | ~r2_hidden(C_132, k1_xboole_0))), inference(resolution, [status(thm)], [c_487, c_2])).
% 11.26/4.14  tff(c_501, plain, (![C_132, B_2]: (r2_hidden(k4_tarski('#skF_7'(k1_xboole_0, k1_xboole_0, C_132), C_132), B_2) | ~r2_hidden(C_132, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_495])).
% 11.26/4.14  tff(c_52, plain, (![A_38, B_42]: (k1_relat_1('#skF_9'(A_38, B_42))=A_38 | k1_xboole_0=A_38)), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.26/4.14  tff(c_54, plain, (![A_38, B_42]: (v1_funct_1('#skF_9'(A_38, B_42)) | k1_xboole_0=A_38)), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.26/4.14  tff(c_56, plain, (![A_38, B_42]: (v1_relat_1('#skF_9'(A_38, B_42)) | k1_xboole_0=A_38)), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.26/4.14  tff(c_236, plain, (![A_70, B_71]: (r2_hidden('#skF_1'(A_70, B_71), A_70) | r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.26/4.14  tff(c_10, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.26/4.14  tff(c_304, plain, (![A_91, B_92]: ('#skF_1'(k1_tarski(A_91), B_92)=A_91 | r1_tarski(k1_tarski(A_91), B_92))), inference(resolution, [status(thm)], [c_236, c_10])).
% 11.26/4.14  tff(c_243, plain, (![A_72, B_73]: (k2_relat_1('#skF_9'(A_72, B_73))=k1_tarski(B_73) | k1_xboole_0=A_72)), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.26/4.14  tff(c_58, plain, (![C_45]: (~r1_tarski(k2_relat_1(C_45), '#skF_10') | k1_relat_1(C_45)!='#skF_11' | ~v1_funct_1(C_45) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.26/4.14  tff(c_249, plain, (![B_73, A_72]: (~r1_tarski(k1_tarski(B_73), '#skF_10') | k1_relat_1('#skF_9'(A_72, B_73))!='#skF_11' | ~v1_funct_1('#skF_9'(A_72, B_73)) | ~v1_relat_1('#skF_9'(A_72, B_73)) | k1_xboole_0=A_72)), inference(superposition, [status(thm), theory('equality')], [c_243, c_58])).
% 11.26/4.14  tff(c_374, plain, (![A_108, A_109]: (k1_relat_1('#skF_9'(A_108, A_109))!='#skF_11' | ~v1_funct_1('#skF_9'(A_108, A_109)) | ~v1_relat_1('#skF_9'(A_108, A_109)) | k1_xboole_0=A_108 | '#skF_1'(k1_tarski(A_109), '#skF_10')=A_109)), inference(resolution, [status(thm)], [c_304, c_249])).
% 11.26/4.14  tff(c_482, plain, (![A_130, B_131]: (k1_relat_1('#skF_9'(A_130, B_131))!='#skF_11' | ~v1_funct_1('#skF_9'(A_130, B_131)) | '#skF_1'(k1_tarski(B_131), '#skF_10')=B_131 | k1_xboole_0=A_130)), inference(resolution, [status(thm)], [c_56, c_374])).
% 11.26/4.14  tff(c_831, plain, (![A_1885, B_1886]: (k1_relat_1('#skF_9'(A_1885, B_1886))!='#skF_11' | '#skF_1'(k1_tarski(B_1886), '#skF_10')=B_1886 | k1_xboole_0=A_1885)), inference(resolution, [status(thm)], [c_54, c_482])).
% 11.26/4.14  tff(c_834, plain, (![A_38, B_42]: (A_38!='#skF_11' | '#skF_1'(k1_tarski(B_42), '#skF_10')=B_42 | k1_xboole_0=A_38 | k1_xboole_0=A_38)), inference(superposition, [status(thm), theory('equality')], [c_52, c_831])).
% 11.26/4.14  tff(c_13900, plain, (k1_xboole_0='#skF_11'), inference(splitLeft, [status(thm)], [c_834])).
% 11.26/4.14  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.26/4.14  tff(c_83, plain, (![C_51]: (~r1_tarski(k2_relat_1(C_51), '#skF_10') | k1_relat_1(C_51)!='#skF_11' | ~v1_funct_1(C_51) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.26/4.14  tff(c_86, plain, (~r1_tarski(k1_xboole_0, '#skF_10') | k1_relat_1(k1_xboole_0)!='#skF_11' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_83])).
% 11.26/4.14  tff(c_88, plain, (k1_xboole_0!='#skF_11' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8, c_86])).
% 11.26/4.14  tff(c_97, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_88])).
% 11.26/4.14  tff(c_44, plain, (![A_32]: (k1_relat_1('#skF_8'(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.26/4.14  tff(c_48, plain, (![A_32]: (v1_relat_1('#skF_8'(A_32)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.26/4.14  tff(c_108, plain, (![A_60]: (k1_relat_1(A_60)!=k1_xboole_0 | k1_xboole_0=A_60 | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.26/4.14  tff(c_114, plain, (![A_32]: (k1_relat_1('#skF_8'(A_32))!=k1_xboole_0 | '#skF_8'(A_32)=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_108])).
% 11.26/4.14  tff(c_119, plain, (![A_61]: (k1_xboole_0!=A_61 | '#skF_8'(A_61)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_114])).
% 11.26/4.14  tff(c_129, plain, (![A_61]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_61)), inference(superposition, [status(thm), theory('equality')], [c_119, c_48])).
% 11.26/4.14  tff(c_135, plain, (![A_61]: (k1_xboole_0!=A_61)), inference(negUnitSimplification, [status(thm)], [c_97, c_129])).
% 11.26/4.14  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_34])).
% 11.26/4.14  tff(c_145, plain, (~v1_funct_1(k1_xboole_0) | k1_xboole_0!='#skF_11'), inference(splitRight, [status(thm)], [c_88])).
% 11.26/4.14  tff(c_147, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_145])).
% 11.26/4.14  tff(c_13953, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13900, c_147])).
% 11.26/4.14  tff(c_13956, plain, (![B_12409]: ('#skF_1'(k1_tarski(B_12409), '#skF_10')=B_12409)), inference(splitRight, [status(thm)], [c_834])).
% 11.26/4.14  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.26/4.14  tff(c_13995, plain, (![B_12460]: (~r2_hidden(B_12460, '#skF_10') | r1_tarski(k1_tarski(B_12460), '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_13956, c_4])).
% 11.26/4.14  tff(c_14563, plain, (![A_12768, B_12769]: (k1_relat_1('#skF_9'(A_12768, B_12769))!='#skF_11' | ~v1_funct_1('#skF_9'(A_12768, B_12769)) | ~v1_relat_1('#skF_9'(A_12768, B_12769)) | k1_xboole_0=A_12768 | ~r2_hidden(B_12769, '#skF_10'))), inference(resolution, [status(thm)], [c_13995, c_249])).
% 11.26/4.14  tff(c_36692, plain, (![A_21865, B_21866]: (k1_relat_1('#skF_9'(A_21865, B_21866))!='#skF_11' | ~v1_funct_1('#skF_9'(A_21865, B_21866)) | ~r2_hidden(B_21866, '#skF_10') | k1_xboole_0=A_21865)), inference(resolution, [status(thm)], [c_56, c_14563])).
% 11.26/4.14  tff(c_36701, plain, (![A_21917, B_21918]: (k1_relat_1('#skF_9'(A_21917, B_21918))!='#skF_11' | ~r2_hidden(B_21918, '#skF_10') | k1_xboole_0=A_21917)), inference(resolution, [status(thm)], [c_54, c_36692])).
% 11.26/4.14  tff(c_36712, plain, (![A_38, B_42]: (A_38!='#skF_11' | ~r2_hidden(B_42, '#skF_10') | k1_xboole_0=A_38 | k1_xboole_0=A_38)), inference(superposition, [status(thm), theory('equality')], [c_52, c_36701])).
% 11.26/4.14  tff(c_36714, plain, (![B_21969]: (~r2_hidden(B_21969, '#skF_10'))), inference(splitLeft, [status(thm)], [c_36712])).
% 11.26/4.14  tff(c_36798, plain, (![C_132]: (~r2_hidden(C_132, k1_xboole_0))), inference(resolution, [status(thm)], [c_501, c_36714])).
% 11.26/4.14  tff(c_12044, plain, (![A_9294, B_9295]: (r2_hidden(k4_tarski('#skF_5'(A_9294, B_9295), '#skF_4'(A_9294, B_9295)), A_9294) | r2_hidden('#skF_6'(A_9294, B_9295), B_9295) | k2_relat_1(A_9294)=B_9295)), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.26/4.14  tff(c_24, plain, (![C_27, A_12, D_30]: (r2_hidden(C_27, k2_relat_1(A_12)) | ~r2_hidden(k4_tarski(D_30, C_27), A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.26/4.14  tff(c_12206, plain, (![A_9402, B_9403]: (r2_hidden('#skF_4'(A_9402, B_9403), k2_relat_1(A_9402)) | r2_hidden('#skF_6'(A_9402, B_9403), B_9403) | k2_relat_1(A_9402)=B_9403)), inference(resolution, [status(thm)], [c_12044, c_24])).
% 11.26/4.14  tff(c_12235, plain, (![B_9403]: (r2_hidden('#skF_4'(k1_xboole_0, B_9403), k1_xboole_0) | r2_hidden('#skF_6'(k1_xboole_0, B_9403), B_9403) | k2_relat_1(k1_xboole_0)=B_9403)), inference(superposition, [status(thm), theory('equality')], [c_34, c_12206])).
% 11.26/4.14  tff(c_12241, plain, (![B_9403]: (r2_hidden('#skF_4'(k1_xboole_0, B_9403), k1_xboole_0) | r2_hidden('#skF_6'(k1_xboole_0, B_9403), B_9403) | k1_xboole_0=B_9403)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_12235])).
% 11.26/4.14  tff(c_36923, plain, (![B_22022]: (r2_hidden('#skF_6'(k1_xboole_0, B_22022), B_22022) | k1_xboole_0=B_22022)), inference(negUnitSimplification, [status(thm)], [c_36798, c_12241])).
% 11.26/4.14  tff(c_36713, plain, (![B_42]: (~r2_hidden(B_42, '#skF_10'))), inference(splitLeft, [status(thm)], [c_36712])).
% 11.26/4.14  tff(c_36931, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_36923, c_36713])).
% 11.26/4.14  tff(c_36958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_36931])).
% 11.26/4.14  tff(c_36960, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_36712])).
% 11.26/4.14  tff(c_37020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36960, c_147])).
% 11.26/4.14  tff(c_37022, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_145])).
% 11.26/4.14  tff(c_37021, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_145])).
% 11.26/4.14  tff(c_37023, plain, (~v1_funct_1('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_37022, c_37021])).
% 11.26/4.14  tff(c_40, plain, (![A_31]: (k1_relat_1(A_31)!=k1_xboole_0 | k1_xboole_0=A_31 | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.26/4.14  tff(c_37050, plain, (![A_22024]: (k1_relat_1(A_22024)!='#skF_11' | A_22024='#skF_11' | ~v1_relat_1(A_22024))), inference(demodulation, [status(thm), theory('equality')], [c_37022, c_37022, c_40])).
% 11.26/4.14  tff(c_37056, plain, (![A_32]: (k1_relat_1('#skF_8'(A_32))!='#skF_11' | '#skF_8'(A_32)='#skF_11')), inference(resolution, [status(thm)], [c_48, c_37050])).
% 11.26/4.14  tff(c_37064, plain, (![A_22025]: (A_22025!='#skF_11' | '#skF_8'(A_22025)='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_37056])).
% 11.26/4.14  tff(c_46, plain, (![A_32]: (v1_funct_1('#skF_8'(A_32)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.26/4.14  tff(c_37072, plain, (![A_22025]: (v1_funct_1('#skF_11') | A_22025!='#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_37064, c_46])).
% 11.26/4.14  tff(c_37080, plain, (![A_22025]: (A_22025!='#skF_11')), inference(negUnitSimplification, [status(thm)], [c_37023, c_37072])).
% 11.26/4.14  tff(c_37030, plain, (k1_relat_1('#skF_11')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_37022, c_37022, c_36])).
% 11.26/4.14  tff(c_37088, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37080, c_37030])).
% 11.26/4.14  tff(c_37090, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_60])).
% 11.26/4.14  tff(c_37089, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_60])).
% 11.26/4.14  tff(c_37099, plain, ('#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_37090, c_37089])).
% 11.26/4.14  tff(c_37093, plain, (k1_relat_1('#skF_11')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_37089, c_37089, c_36])).
% 11.26/4.14  tff(c_37109, plain, (k1_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_37099, c_37099, c_37093])).
% 11.26/4.14  tff(c_37092, plain, (![A_6]: (r1_tarski('#skF_11', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_37089, c_8])).
% 11.26/4.14  tff(c_37114, plain, (![A_6]: (r1_tarski('#skF_10', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_37099, c_37092])).
% 11.26/4.14  tff(c_37091, plain, (k2_relat_1('#skF_11')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_37089, c_37089, c_34])).
% 11.26/4.14  tff(c_37116, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_37099, c_37099, c_37091])).
% 11.26/4.14  tff(c_37132, plain, (![C_22035]: (~r1_tarski(k2_relat_1(C_22035), '#skF_10') | k1_relat_1(C_22035)!='#skF_10' | ~v1_funct_1(C_22035) | ~v1_relat_1(C_22035))), inference(demodulation, [status(thm), theory('equality')], [c_37099, c_58])).
% 11.26/4.14  tff(c_37135, plain, (~r1_tarski('#skF_10', '#skF_10') | k1_relat_1('#skF_10')!='#skF_10' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_37116, c_37132])).
% 11.26/4.14  tff(c_37137, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_37109, c_37114, c_37135])).
% 11.26/4.14  tff(c_37138, plain, (~v1_relat_1('#skF_10')), inference(splitLeft, [status(thm)], [c_37137])).
% 11.26/4.14  tff(c_37151, plain, (![A_22038]: (k1_relat_1(A_22038)!='#skF_10' | A_22038='#skF_10' | ~v1_relat_1(A_22038))), inference(demodulation, [status(thm), theory('equality')], [c_37090, c_37090, c_40])).
% 11.26/4.14  tff(c_37157, plain, (![A_32]: (k1_relat_1('#skF_8'(A_32))!='#skF_10' | '#skF_8'(A_32)='#skF_10')), inference(resolution, [status(thm)], [c_48, c_37151])).
% 11.26/4.14  tff(c_37162, plain, (![A_22039]: (A_22039!='#skF_10' | '#skF_8'(A_22039)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_37157])).
% 11.26/4.14  tff(c_37172, plain, (![A_22039]: (v1_relat_1('#skF_10') | A_22039!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_37162, c_48])).
% 11.26/4.14  tff(c_37178, plain, (![A_22039]: (A_22039!='#skF_10')), inference(negUnitSimplification, [status(thm)], [c_37138, c_37172])).
% 11.26/4.14  tff(c_37200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37178, c_37116])).
% 11.26/4.14  tff(c_37201, plain, (~v1_funct_1('#skF_10')), inference(splitRight, [status(thm)], [c_37137])).
% 11.26/4.14  tff(c_37204, plain, (![A_22041]: (k1_relat_1(A_22041)!='#skF_10' | A_22041='#skF_10' | ~v1_relat_1(A_22041))), inference(demodulation, [status(thm), theory('equality')], [c_37090, c_37090, c_40])).
% 11.26/4.14  tff(c_37213, plain, (![A_32]: (k1_relat_1('#skF_8'(A_32))!='#skF_10' | '#skF_8'(A_32)='#skF_10')), inference(resolution, [status(thm)], [c_48, c_37204])).
% 11.26/4.14  tff(c_37222, plain, (![A_22042]: (A_22042!='#skF_10' | '#skF_8'(A_22042)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_37213])).
% 11.26/4.14  tff(c_37230, plain, (![A_22042]: (v1_funct_1('#skF_10') | A_22042!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_37222, c_46])).
% 11.26/4.14  tff(c_37238, plain, (![A_22042]: (A_22042!='#skF_10')), inference(negUnitSimplification, [status(thm)], [c_37201, c_37230])).
% 11.26/4.14  tff(c_37249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37238, c_37116])).
% 11.26/4.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.26/4.14  
% 11.26/4.14  Inference rules
% 11.26/4.14  ----------------------
% 11.26/4.14  #Ref     : 0
% 11.26/4.14  #Sup     : 6877
% 11.26/4.14  #Fact    : 5
% 11.26/4.14  #Define  : 0
% 11.26/4.14  #Split   : 13
% 11.26/4.14  #Chain   : 0
% 11.26/4.14  #Close   : 0
% 11.26/4.14  
% 11.26/4.14  Ordering : KBO
% 11.26/4.14  
% 11.26/4.14  Simplification rules
% 11.26/4.14  ----------------------
% 11.26/4.14  #Subsume      : 1508
% 11.26/4.15  #Demod        : 939
% 11.26/4.15  #Tautology    : 435
% 11.26/4.15  #SimpNegUnit  : 67
% 11.26/4.15  #BackRed      : 150
% 11.26/4.15  
% 11.26/4.15  #Partial instantiations: 12239
% 11.26/4.15  #Strategies tried      : 1
% 11.26/4.15  
% 11.26/4.15  Timing (in seconds)
% 11.26/4.15  ----------------------
% 11.26/4.15  Preprocessing        : 0.31
% 11.26/4.15  Parsing              : 0.16
% 11.26/4.15  CNF conversion       : 0.03
% 11.26/4.15  Main loop            : 3.06
% 11.26/4.15  Inferencing          : 1.03
% 11.26/4.15  Reduction            : 0.70
% 11.26/4.15  Demodulation         : 0.48
% 11.26/4.15  BG Simplification    : 0.15
% 11.26/4.15  Subsumption          : 0.80
% 11.26/4.15  Abstraction          : 0.19
% 11.26/4.15  MUC search           : 0.00
% 11.26/4.15  Cooper               : 0.00
% 11.26/4.15  Total                : 3.41
% 11.26/4.15  Index Insertion      : 0.00
% 11.26/4.15  Index Deletion       : 0.00
% 11.26/4.15  Index Matching       : 0.00
% 11.26/4.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
