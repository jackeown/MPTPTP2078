%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:07 EST 2020

% Result     : Theorem 7.10s
% Output     : CNFRefutation 7.10s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 627 expanded)
%              Number of leaves         :   34 ( 212 expanded)
%              Depth                    :   19
%              Number of atoms          :  260 (1614 expanded)
%              Number of equality atoms :  131 ( 835 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_100,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_79,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_74,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_26,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k3_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_66,plain,(
    ! [A_32,B_36] :
      ( k1_relat_1('#skF_7'(A_32,B_36)) = A_32
      | k1_xboole_0 = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_68,plain,(
    ! [A_32,B_36] :
      ( v1_funct_1('#skF_7'(A_32,B_36))
      | k1_xboole_0 = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_70,plain,(
    ! [A_32,B_36] :
      ( v1_relat_1('#skF_7'(A_32,B_36))
      | k1_xboole_0 = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_271,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_1'(A_66,B_67),A_66)
      | r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_276,plain,(
    ! [A_16,B_67] :
      ( '#skF_1'(k1_tarski(A_16),B_67) = A_16
      | r1_tarski(k1_tarski(A_16),B_67) ) ),
    inference(resolution,[status(thm)],[c_271,c_32])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_496,plain,(
    ! [C_92,B_93,A_94] :
      ( r2_hidden(C_92,B_93)
      | ~ r2_hidden(C_92,A_94)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_597,plain,(
    ! [A_113,B_114,B_115] :
      ( r2_hidden('#skF_1'(A_113,B_114),B_115)
      | ~ r1_tarski(A_113,B_115)
      | r1_tarski(A_113,B_114) ) ),
    inference(resolution,[status(thm)],[c_6,c_496])).

tff(c_331,plain,(
    ! [D_71,A_72,B_73] :
      ( r2_hidden(D_71,A_72)
      | ~ r2_hidden(D_71,k3_xboole_0(A_72,B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_338,plain,(
    ! [D_71,A_12] :
      ( r2_hidden(D_71,A_12)
      | ~ r2_hidden(D_71,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_331])).

tff(c_663,plain,(
    ! [A_120,B_121,A_122] :
      ( r2_hidden('#skF_1'(A_120,B_121),A_122)
      | ~ r1_tarski(A_120,k1_xboole_0)
      | r1_tarski(A_120,B_121) ) ),
    inference(resolution,[status(thm)],[c_597,c_338])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_698,plain,(
    ! [A_123,A_124] :
      ( ~ r1_tarski(A_123,k1_xboole_0)
      | r1_tarski(A_123,A_124) ) ),
    inference(resolution,[status(thm)],[c_663,c_4])).

tff(c_713,plain,(
    ! [A_125,A_126] :
      ( r1_tarski(k1_tarski(A_125),A_126)
      | '#skF_1'(k1_tarski(A_125),k1_xboole_0) = A_125 ) ),
    inference(resolution,[status(thm)],[c_276,c_698])).

tff(c_34,plain,(
    ! [C_20] : r2_hidden(C_20,k1_tarski(C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_502,plain,(
    ! [C_20,B_93] :
      ( r2_hidden(C_20,B_93)
      | ~ r1_tarski(k1_tarski(C_20),B_93) ) ),
    inference(resolution,[status(thm)],[c_34,c_496])).

tff(c_731,plain,(
    ! [A_129,A_130] :
      ( r2_hidden(A_129,A_130)
      | '#skF_1'(k1_tarski(A_129),k1_xboole_0) = A_129 ) ),
    inference(resolution,[status(thm)],[c_713,c_502])).

tff(c_781,plain,(
    ! [A_16,A_129] :
      ( A_16 = A_129
      | '#skF_1'(k1_tarski(A_129),k1_xboole_0) = A_129 ) ),
    inference(resolution,[status(thm)],[c_731,c_32])).

tff(c_8811,plain,(
    ! [A_2873] : '#skF_1'(k1_tarski(A_2873),k1_xboole_0) = A_2873 ),
    inference(factorization,[status(thm),theory(equality)],[c_781])).

tff(c_8887,plain,(
    ! [A_2878] :
      ( ~ r2_hidden(A_2878,k1_xboole_0)
      | r1_tarski(k1_tarski(A_2878),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8811,c_4])).

tff(c_694,plain,(
    ! [A_120,A_122] :
      ( ~ r1_tarski(A_120,k1_xboole_0)
      | r1_tarski(A_120,A_122) ) ),
    inference(resolution,[status(thm)],[c_663,c_4])).

tff(c_8895,plain,(
    ! [A_2879,A_2880] :
      ( r1_tarski(k1_tarski(A_2879),A_2880)
      | ~ r2_hidden(A_2879,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8887,c_694])).

tff(c_471,plain,(
    ! [A_86,B_87] :
      ( k2_relat_1('#skF_7'(A_86,B_87)) = k1_tarski(B_87)
      | k1_xboole_0 = A_86 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_72,plain,(
    ! [C_39] :
      ( ~ r1_tarski(k2_relat_1(C_39),'#skF_8')
      | k1_relat_1(C_39) != '#skF_9'
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_477,plain,(
    ! [B_87,A_86] :
      ( ~ r1_tarski(k1_tarski(B_87),'#skF_8')
      | k1_relat_1('#skF_7'(A_86,B_87)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_86,B_87))
      | ~ v1_relat_1('#skF_7'(A_86,B_87))
      | k1_xboole_0 = A_86 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_72])).

tff(c_9018,plain,(
    ! [A_2887,A_2888] :
      ( k1_relat_1('#skF_7'(A_2887,A_2888)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_2887,A_2888))
      | ~ v1_relat_1('#skF_7'(A_2887,A_2888))
      | k1_xboole_0 = A_2887
      | ~ r2_hidden(A_2888,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8895,c_477])).

tff(c_9330,plain,(
    ! [A_2914,B_2915] :
      ( k1_relat_1('#skF_7'(A_2914,B_2915)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_2914,B_2915))
      | ~ r2_hidden(B_2915,k1_xboole_0)
      | k1_xboole_0 = A_2914 ) ),
    inference(resolution,[status(thm)],[c_70,c_9018])).

tff(c_9335,plain,(
    ! [A_2916,B_2917] :
      ( k1_relat_1('#skF_7'(A_2916,B_2917)) != '#skF_9'
      | ~ r2_hidden(B_2917,k1_xboole_0)
      | k1_xboole_0 = A_2916 ) ),
    inference(resolution,[status(thm)],[c_68,c_9330])).

tff(c_9338,plain,(
    ! [A_32,B_36] :
      ( A_32 != '#skF_9'
      | ~ r2_hidden(B_36,k1_xboole_0)
      | k1_xboole_0 = A_32
      | k1_xboole_0 = A_32 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_9335])).

tff(c_9340,plain,(
    ! [B_2918] : ~ r2_hidden(B_2918,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_9338])).

tff(c_9358,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,k1_xboole_0,C_8),C_8)
      | k3_xboole_0(A_6,k1_xboole_0) = C_8 ) ),
    inference(resolution,[status(thm)],[c_22,c_9340])).

tff(c_9384,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,k1_xboole_0,C_8),C_8)
      | k1_xboole_0 = C_8 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_9358])).

tff(c_539,plain,(
    ! [A_100,B_101] :
      ( '#skF_1'(k1_tarski(A_100),B_101) = A_100
      | r1_tarski(k1_tarski(A_100),B_101) ) ),
    inference(resolution,[status(thm)],[c_271,c_32])).

tff(c_578,plain,(
    ! [A_106,A_107] :
      ( k1_relat_1('#skF_7'(A_106,A_107)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_106,A_107))
      | ~ v1_relat_1('#skF_7'(A_106,A_107))
      | k1_xboole_0 = A_106
      | '#skF_1'(k1_tarski(A_107),'#skF_8') = A_107 ) ),
    inference(resolution,[status(thm)],[c_539,c_477])).

tff(c_9547,plain,(
    ! [A_2929,B_2930] :
      ( k1_relat_1('#skF_7'(A_2929,B_2930)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_2929,B_2930))
      | '#skF_1'(k1_tarski(B_2930),'#skF_8') = B_2930
      | k1_xboole_0 = A_2929 ) ),
    inference(resolution,[status(thm)],[c_70,c_578])).

tff(c_10245,plain,(
    ! [A_2975,B_2976] :
      ( k1_relat_1('#skF_7'(A_2975,B_2976)) != '#skF_9'
      | '#skF_1'(k1_tarski(B_2976),'#skF_8') = B_2976
      | k1_xboole_0 = A_2975 ) ),
    inference(resolution,[status(thm)],[c_68,c_9547])).

tff(c_10248,plain,(
    ! [A_32,B_36] :
      ( A_32 != '#skF_9'
      | '#skF_1'(k1_tarski(B_36),'#skF_8') = B_36
      | k1_xboole_0 = A_32
      | k1_xboole_0 = A_32 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_10245])).

tff(c_10250,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_10248])).

tff(c_48,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_95,plain,(
    ! [C_45] :
      ( ~ r1_tarski(k2_relat_1(C_45),'#skF_8')
      | k1_relat_1(C_45) != '#skF_9'
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_98,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_8')
    | k1_relat_1(k1_xboole_0) != '#skF_9'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_95])).

tff(c_100,plain,
    ( k1_xboole_0 != '#skF_9'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_28,c_98])).

tff(c_166,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_56,plain,(
    ! [A_24] : k1_relat_1('#skF_6'(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_60,plain,(
    ! [A_24] : v1_relat_1('#skF_6'(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_186,plain,(
    ! [A_60] :
      ( k1_relat_1(A_60) != k1_xboole_0
      | k1_xboole_0 = A_60
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_192,plain,(
    ! [A_24] :
      ( k1_relat_1('#skF_6'(A_24)) != k1_xboole_0
      | '#skF_6'(A_24) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_60,c_186])).

tff(c_197,plain,(
    ! [A_61] :
      ( k1_xboole_0 != A_61
      | '#skF_6'(A_61) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_192])).

tff(c_207,plain,(
    ! [A_61] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_61 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_60])).

tff(c_213,plain,(
    ! [A_61] : k1_xboole_0 != A_61 ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_207])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_26])).

tff(c_225,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_227,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_10296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10250,c_227])).

tff(c_10300,plain,(
    ! [B_2977] : '#skF_1'(k1_tarski(B_2977),'#skF_8') = B_2977 ),
    inference(splitRight,[status(thm)],[c_10248])).

tff(c_10334,plain,(
    ! [B_2978] :
      ( ~ r2_hidden(B_2978,'#skF_8')
      | r1_tarski(k1_tarski(B_2978),'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10300,c_4])).

tff(c_10399,plain,(
    ! [A_2981,B_2982] :
      ( k1_relat_1('#skF_7'(A_2981,B_2982)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_2981,B_2982))
      | ~ v1_relat_1('#skF_7'(A_2981,B_2982))
      | k1_xboole_0 = A_2981
      | ~ r2_hidden(B_2982,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_10334,c_477])).

tff(c_10623,plain,(
    ! [A_2998,B_2999] :
      ( k1_relat_1('#skF_7'(A_2998,B_2999)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_2998,B_2999))
      | ~ r2_hidden(B_2999,'#skF_8')
      | k1_xboole_0 = A_2998 ) ),
    inference(resolution,[status(thm)],[c_70,c_10399])).

tff(c_10628,plain,(
    ! [A_3000,B_3001] :
      ( k1_relat_1('#skF_7'(A_3000,B_3001)) != '#skF_9'
      | ~ r2_hidden(B_3001,'#skF_8')
      | k1_xboole_0 = A_3000 ) ),
    inference(resolution,[status(thm)],[c_68,c_10623])).

tff(c_10631,plain,(
    ! [A_32,B_36] :
      ( A_32 != '#skF_9'
      | ~ r2_hidden(B_36,'#skF_8')
      | k1_xboole_0 = A_32
      | k1_xboole_0 = A_32 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_10628])).

tff(c_10633,plain,(
    ! [B_3002] : ~ r2_hidden(B_3002,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_10631])).

tff(c_10661,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_9384,c_10633])).

tff(c_10715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_10661])).

tff(c_10717,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_10631])).

tff(c_10766,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10717,c_227])).

tff(c_10768,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_9338])).

tff(c_10806,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10768,c_227])).

tff(c_10808,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_10807,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_10825,plain,(
    ~ v1_funct_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10808,c_10807])).

tff(c_52,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10861,plain,(
    ! [A_3006] :
      ( k1_relat_1(A_3006) != '#skF_9'
      | A_3006 = '#skF_9'
      | ~ v1_relat_1(A_3006) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10808,c_10808,c_52])).

tff(c_10867,plain,(
    ! [A_24] :
      ( k1_relat_1('#skF_6'(A_24)) != '#skF_9'
      | '#skF_6'(A_24) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_60,c_10861])).

tff(c_10875,plain,(
    ! [A_3007] :
      ( A_3007 != '#skF_9'
      | '#skF_6'(A_3007) = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_10867])).

tff(c_58,plain,(
    ! [A_24] : v1_funct_1('#skF_6'(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10883,plain,(
    ! [A_3007] :
      ( v1_funct_1('#skF_9')
      | A_3007 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10875,c_58])).

tff(c_10891,plain,(
    ! [A_3007] : A_3007 != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_10825,c_10883])).

tff(c_10830,plain,(
    ! [A_12] : k3_xboole_0(A_12,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10808,c_10808,c_26])).

tff(c_10900,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10891,c_10830])).

tff(c_10902,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_10901,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_10911,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10902,c_10901])).

tff(c_10905,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10901,c_10901,c_48])).

tff(c_10921,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10911,c_10911,c_10905])).

tff(c_10904,plain,(
    ! [A_13] : r1_tarski('#skF_9',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10901,c_28])).

tff(c_10926,plain,(
    ! [A_13] : r1_tarski('#skF_8',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10911,c_10904])).

tff(c_10903,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10901,c_10901,c_46])).

tff(c_10928,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10911,c_10911,c_10903])).

tff(c_10984,plain,(
    ! [C_3015] :
      ( ~ r1_tarski(k2_relat_1(C_3015),'#skF_8')
      | k1_relat_1(C_3015) != '#skF_8'
      | ~ v1_funct_1(C_3015)
      | ~ v1_relat_1(C_3015) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10911,c_72])).

tff(c_10987,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | k1_relat_1('#skF_8') != '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_10928,c_10984])).

tff(c_10989,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10921,c_10926,c_10987])).

tff(c_10990,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_10989])).

tff(c_11038,plain,(
    ! [A_3027] :
      ( k1_relat_1(A_3027) != '#skF_8'
      | A_3027 = '#skF_8'
      | ~ v1_relat_1(A_3027) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10902,c_10902,c_52])).

tff(c_11044,plain,(
    ! [A_24] :
      ( k1_relat_1('#skF_6'(A_24)) != '#skF_8'
      | '#skF_6'(A_24) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_60,c_11038])).

tff(c_11050,plain,(
    ! [A_3030] :
      ( A_3030 != '#skF_8'
      | '#skF_6'(A_3030) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_11044])).

tff(c_11060,plain,(
    ! [A_3030] :
      ( v1_relat_1('#skF_8')
      | A_3030 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11050,c_60])).

tff(c_11066,plain,(
    ! [A_3030] : A_3030 != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_10990,c_11060])).

tff(c_10942,plain,(
    ! [A_12] : k3_xboole_0(A_12,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10902,c_10902,c_26])).

tff(c_11079,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11066,c_10942])).

tff(c_11080,plain,(
    ~ v1_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_10989])).

tff(c_11110,plain,(
    ! [A_3038] :
      ( k1_relat_1(A_3038) != '#skF_8'
      | A_3038 = '#skF_8'
      | ~ v1_relat_1(A_3038) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10902,c_10902,c_52])).

tff(c_11119,plain,(
    ! [A_24] :
      ( k1_relat_1('#skF_6'(A_24)) != '#skF_8'
      | '#skF_6'(A_24) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_60,c_11110])).

tff(c_11143,plain,(
    ! [A_3041] :
      ( A_3041 != '#skF_8'
      | '#skF_6'(A_3041) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_11119])).

tff(c_11151,plain,(
    ! [A_3041] :
      ( v1_funct_1('#skF_8')
      | A_3041 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11143,c_58])).

tff(c_11159,plain,(
    ! [A_3041] : A_3041 != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_11080,c_11151])).

tff(c_11172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11159,c_10942])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:25:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.10/2.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.10/2.52  
% 7.10/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.10/2.52  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_6 > #skF_4
% 7.10/2.52  
% 7.10/2.52  %Foreground sorts:
% 7.10/2.52  
% 7.10/2.52  
% 7.10/2.52  %Background operators:
% 7.10/2.52  
% 7.10/2.52  
% 7.10/2.52  %Foreground operators:
% 7.10/2.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.10/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.10/2.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.10/2.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.10/2.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.10/2.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.10/2.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.10/2.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.10/2.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.10/2.52  tff('#skF_9', type, '#skF_9': $i).
% 7.10/2.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.10/2.52  tff('#skF_8', type, '#skF_8': $i).
% 7.10/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.10/2.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.10/2.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.10/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.10/2.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.10/2.52  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 7.10/2.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.10/2.52  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.10/2.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.10/2.52  tff('#skF_6', type, '#skF_6': $i > $i).
% 7.10/2.52  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.10/2.52  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.10/2.52  
% 7.10/2.54  tff(f_118, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 7.10/2.54  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 7.10/2.54  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.10/2.54  tff(f_100, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 7.10/2.54  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.10/2.54  tff(f_54, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 7.10/2.54  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 7.10/2.54  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.10/2.54  tff(f_79, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 7.10/2.54  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 7.10/2.54  tff(c_74, plain, (k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.10/2.54  tff(c_86, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_74])).
% 7.10/2.54  tff(c_26, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.10/2.54  tff(c_22, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k3_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.10/2.54  tff(c_66, plain, (![A_32, B_36]: (k1_relat_1('#skF_7'(A_32, B_36))=A_32 | k1_xboole_0=A_32)), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.10/2.54  tff(c_68, plain, (![A_32, B_36]: (v1_funct_1('#skF_7'(A_32, B_36)) | k1_xboole_0=A_32)), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.10/2.54  tff(c_70, plain, (![A_32, B_36]: (v1_relat_1('#skF_7'(A_32, B_36)) | k1_xboole_0=A_32)), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.10/2.54  tff(c_271, plain, (![A_66, B_67]: (r2_hidden('#skF_1'(A_66, B_67), A_66) | r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.10/2.54  tff(c_32, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.10/2.54  tff(c_276, plain, (![A_16, B_67]: ('#skF_1'(k1_tarski(A_16), B_67)=A_16 | r1_tarski(k1_tarski(A_16), B_67))), inference(resolution, [status(thm)], [c_271, c_32])).
% 7.10/2.54  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.10/2.54  tff(c_496, plain, (![C_92, B_93, A_94]: (r2_hidden(C_92, B_93) | ~r2_hidden(C_92, A_94) | ~r1_tarski(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.10/2.54  tff(c_597, plain, (![A_113, B_114, B_115]: (r2_hidden('#skF_1'(A_113, B_114), B_115) | ~r1_tarski(A_113, B_115) | r1_tarski(A_113, B_114))), inference(resolution, [status(thm)], [c_6, c_496])).
% 7.10/2.54  tff(c_331, plain, (![D_71, A_72, B_73]: (r2_hidden(D_71, A_72) | ~r2_hidden(D_71, k3_xboole_0(A_72, B_73)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.10/2.54  tff(c_338, plain, (![D_71, A_12]: (r2_hidden(D_71, A_12) | ~r2_hidden(D_71, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_331])).
% 7.10/2.54  tff(c_663, plain, (![A_120, B_121, A_122]: (r2_hidden('#skF_1'(A_120, B_121), A_122) | ~r1_tarski(A_120, k1_xboole_0) | r1_tarski(A_120, B_121))), inference(resolution, [status(thm)], [c_597, c_338])).
% 7.10/2.54  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.10/2.54  tff(c_698, plain, (![A_123, A_124]: (~r1_tarski(A_123, k1_xboole_0) | r1_tarski(A_123, A_124))), inference(resolution, [status(thm)], [c_663, c_4])).
% 7.10/2.54  tff(c_713, plain, (![A_125, A_126]: (r1_tarski(k1_tarski(A_125), A_126) | '#skF_1'(k1_tarski(A_125), k1_xboole_0)=A_125)), inference(resolution, [status(thm)], [c_276, c_698])).
% 7.10/2.54  tff(c_34, plain, (![C_20]: (r2_hidden(C_20, k1_tarski(C_20)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.10/2.54  tff(c_502, plain, (![C_20, B_93]: (r2_hidden(C_20, B_93) | ~r1_tarski(k1_tarski(C_20), B_93))), inference(resolution, [status(thm)], [c_34, c_496])).
% 7.10/2.54  tff(c_731, plain, (![A_129, A_130]: (r2_hidden(A_129, A_130) | '#skF_1'(k1_tarski(A_129), k1_xboole_0)=A_129)), inference(resolution, [status(thm)], [c_713, c_502])).
% 7.10/2.54  tff(c_781, plain, (![A_16, A_129]: (A_16=A_129 | '#skF_1'(k1_tarski(A_129), k1_xboole_0)=A_129)), inference(resolution, [status(thm)], [c_731, c_32])).
% 7.10/2.54  tff(c_8811, plain, (![A_2873]: ('#skF_1'(k1_tarski(A_2873), k1_xboole_0)=A_2873)), inference(factorization, [status(thm), theory('equality')], [c_781])).
% 7.10/2.54  tff(c_8887, plain, (![A_2878]: (~r2_hidden(A_2878, k1_xboole_0) | r1_tarski(k1_tarski(A_2878), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8811, c_4])).
% 7.10/2.54  tff(c_694, plain, (![A_120, A_122]: (~r1_tarski(A_120, k1_xboole_0) | r1_tarski(A_120, A_122))), inference(resolution, [status(thm)], [c_663, c_4])).
% 7.10/2.54  tff(c_8895, plain, (![A_2879, A_2880]: (r1_tarski(k1_tarski(A_2879), A_2880) | ~r2_hidden(A_2879, k1_xboole_0))), inference(resolution, [status(thm)], [c_8887, c_694])).
% 7.10/2.54  tff(c_471, plain, (![A_86, B_87]: (k2_relat_1('#skF_7'(A_86, B_87))=k1_tarski(B_87) | k1_xboole_0=A_86)), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.10/2.54  tff(c_72, plain, (![C_39]: (~r1_tarski(k2_relat_1(C_39), '#skF_8') | k1_relat_1(C_39)!='#skF_9' | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.10/2.54  tff(c_477, plain, (![B_87, A_86]: (~r1_tarski(k1_tarski(B_87), '#skF_8') | k1_relat_1('#skF_7'(A_86, B_87))!='#skF_9' | ~v1_funct_1('#skF_7'(A_86, B_87)) | ~v1_relat_1('#skF_7'(A_86, B_87)) | k1_xboole_0=A_86)), inference(superposition, [status(thm), theory('equality')], [c_471, c_72])).
% 7.10/2.54  tff(c_9018, plain, (![A_2887, A_2888]: (k1_relat_1('#skF_7'(A_2887, A_2888))!='#skF_9' | ~v1_funct_1('#skF_7'(A_2887, A_2888)) | ~v1_relat_1('#skF_7'(A_2887, A_2888)) | k1_xboole_0=A_2887 | ~r2_hidden(A_2888, k1_xboole_0))), inference(resolution, [status(thm)], [c_8895, c_477])).
% 7.10/2.54  tff(c_9330, plain, (![A_2914, B_2915]: (k1_relat_1('#skF_7'(A_2914, B_2915))!='#skF_9' | ~v1_funct_1('#skF_7'(A_2914, B_2915)) | ~r2_hidden(B_2915, k1_xboole_0) | k1_xboole_0=A_2914)), inference(resolution, [status(thm)], [c_70, c_9018])).
% 7.10/2.54  tff(c_9335, plain, (![A_2916, B_2917]: (k1_relat_1('#skF_7'(A_2916, B_2917))!='#skF_9' | ~r2_hidden(B_2917, k1_xboole_0) | k1_xboole_0=A_2916)), inference(resolution, [status(thm)], [c_68, c_9330])).
% 7.10/2.54  tff(c_9338, plain, (![A_32, B_36]: (A_32!='#skF_9' | ~r2_hidden(B_36, k1_xboole_0) | k1_xboole_0=A_32 | k1_xboole_0=A_32)), inference(superposition, [status(thm), theory('equality')], [c_66, c_9335])).
% 7.10/2.54  tff(c_9340, plain, (![B_2918]: (~r2_hidden(B_2918, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_9338])).
% 7.10/2.54  tff(c_9358, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, k1_xboole_0, C_8), C_8) | k3_xboole_0(A_6, k1_xboole_0)=C_8)), inference(resolution, [status(thm)], [c_22, c_9340])).
% 7.10/2.54  tff(c_9384, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, k1_xboole_0, C_8), C_8) | k1_xboole_0=C_8)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_9358])).
% 7.10/2.54  tff(c_539, plain, (![A_100, B_101]: ('#skF_1'(k1_tarski(A_100), B_101)=A_100 | r1_tarski(k1_tarski(A_100), B_101))), inference(resolution, [status(thm)], [c_271, c_32])).
% 7.10/2.54  tff(c_578, plain, (![A_106, A_107]: (k1_relat_1('#skF_7'(A_106, A_107))!='#skF_9' | ~v1_funct_1('#skF_7'(A_106, A_107)) | ~v1_relat_1('#skF_7'(A_106, A_107)) | k1_xboole_0=A_106 | '#skF_1'(k1_tarski(A_107), '#skF_8')=A_107)), inference(resolution, [status(thm)], [c_539, c_477])).
% 7.10/2.54  tff(c_9547, plain, (![A_2929, B_2930]: (k1_relat_1('#skF_7'(A_2929, B_2930))!='#skF_9' | ~v1_funct_1('#skF_7'(A_2929, B_2930)) | '#skF_1'(k1_tarski(B_2930), '#skF_8')=B_2930 | k1_xboole_0=A_2929)), inference(resolution, [status(thm)], [c_70, c_578])).
% 7.10/2.54  tff(c_10245, plain, (![A_2975, B_2976]: (k1_relat_1('#skF_7'(A_2975, B_2976))!='#skF_9' | '#skF_1'(k1_tarski(B_2976), '#skF_8')=B_2976 | k1_xboole_0=A_2975)), inference(resolution, [status(thm)], [c_68, c_9547])).
% 7.10/2.54  tff(c_10248, plain, (![A_32, B_36]: (A_32!='#skF_9' | '#skF_1'(k1_tarski(B_36), '#skF_8')=B_36 | k1_xboole_0=A_32 | k1_xboole_0=A_32)), inference(superposition, [status(thm), theory('equality')], [c_66, c_10245])).
% 7.10/2.55  tff(c_10250, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_10248])).
% 7.10/2.55  tff(c_48, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.10/2.55  tff(c_28, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.10/2.55  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.10/2.55  tff(c_95, plain, (![C_45]: (~r1_tarski(k2_relat_1(C_45), '#skF_8') | k1_relat_1(C_45)!='#skF_9' | ~v1_funct_1(C_45) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.10/2.55  tff(c_98, plain, (~r1_tarski(k1_xboole_0, '#skF_8') | k1_relat_1(k1_xboole_0)!='#skF_9' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_95])).
% 7.10/2.55  tff(c_100, plain, (k1_xboole_0!='#skF_9' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_28, c_98])).
% 7.10/2.55  tff(c_166, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_100])).
% 7.10/2.55  tff(c_56, plain, (![A_24]: (k1_relat_1('#skF_6'(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.10/2.55  tff(c_60, plain, (![A_24]: (v1_relat_1('#skF_6'(A_24)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.10/2.55  tff(c_186, plain, (![A_60]: (k1_relat_1(A_60)!=k1_xboole_0 | k1_xboole_0=A_60 | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.10/2.55  tff(c_192, plain, (![A_24]: (k1_relat_1('#skF_6'(A_24))!=k1_xboole_0 | '#skF_6'(A_24)=k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_186])).
% 7.10/2.55  tff(c_197, plain, (![A_61]: (k1_xboole_0!=A_61 | '#skF_6'(A_61)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_192])).
% 7.10/2.55  tff(c_207, plain, (![A_61]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_61)), inference(superposition, [status(thm), theory('equality')], [c_197, c_60])).
% 7.10/2.55  tff(c_213, plain, (![A_61]: (k1_xboole_0!=A_61)), inference(negUnitSimplification, [status(thm)], [c_166, c_207])).
% 7.10/2.55  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_213, c_26])).
% 7.10/2.55  tff(c_225, plain, (~v1_funct_1(k1_xboole_0) | k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_100])).
% 7.10/2.55  tff(c_227, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_225])).
% 7.10/2.55  tff(c_10296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10250, c_227])).
% 7.10/2.55  tff(c_10300, plain, (![B_2977]: ('#skF_1'(k1_tarski(B_2977), '#skF_8')=B_2977)), inference(splitRight, [status(thm)], [c_10248])).
% 7.10/2.55  tff(c_10334, plain, (![B_2978]: (~r2_hidden(B_2978, '#skF_8') | r1_tarski(k1_tarski(B_2978), '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_10300, c_4])).
% 7.10/2.55  tff(c_10399, plain, (![A_2981, B_2982]: (k1_relat_1('#skF_7'(A_2981, B_2982))!='#skF_9' | ~v1_funct_1('#skF_7'(A_2981, B_2982)) | ~v1_relat_1('#skF_7'(A_2981, B_2982)) | k1_xboole_0=A_2981 | ~r2_hidden(B_2982, '#skF_8'))), inference(resolution, [status(thm)], [c_10334, c_477])).
% 7.10/2.55  tff(c_10623, plain, (![A_2998, B_2999]: (k1_relat_1('#skF_7'(A_2998, B_2999))!='#skF_9' | ~v1_funct_1('#skF_7'(A_2998, B_2999)) | ~r2_hidden(B_2999, '#skF_8') | k1_xboole_0=A_2998)), inference(resolution, [status(thm)], [c_70, c_10399])).
% 7.10/2.55  tff(c_10628, plain, (![A_3000, B_3001]: (k1_relat_1('#skF_7'(A_3000, B_3001))!='#skF_9' | ~r2_hidden(B_3001, '#skF_8') | k1_xboole_0=A_3000)), inference(resolution, [status(thm)], [c_68, c_10623])).
% 7.10/2.55  tff(c_10631, plain, (![A_32, B_36]: (A_32!='#skF_9' | ~r2_hidden(B_36, '#skF_8') | k1_xboole_0=A_32 | k1_xboole_0=A_32)), inference(superposition, [status(thm), theory('equality')], [c_66, c_10628])).
% 7.10/2.55  tff(c_10633, plain, (![B_3002]: (~r2_hidden(B_3002, '#skF_8'))), inference(splitLeft, [status(thm)], [c_10631])).
% 7.10/2.55  tff(c_10661, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_9384, c_10633])).
% 7.10/2.55  tff(c_10715, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_10661])).
% 7.10/2.55  tff(c_10717, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_10631])).
% 7.10/2.55  tff(c_10766, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10717, c_227])).
% 7.10/2.55  tff(c_10768, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_9338])).
% 7.10/2.55  tff(c_10806, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10768, c_227])).
% 7.10/2.55  tff(c_10808, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_225])).
% 7.10/2.55  tff(c_10807, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_225])).
% 7.10/2.55  tff(c_10825, plain, (~v1_funct_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_10808, c_10807])).
% 7.10/2.55  tff(c_52, plain, (![A_23]: (k1_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.10/2.55  tff(c_10861, plain, (![A_3006]: (k1_relat_1(A_3006)!='#skF_9' | A_3006='#skF_9' | ~v1_relat_1(A_3006))), inference(demodulation, [status(thm), theory('equality')], [c_10808, c_10808, c_52])).
% 7.10/2.55  tff(c_10867, plain, (![A_24]: (k1_relat_1('#skF_6'(A_24))!='#skF_9' | '#skF_6'(A_24)='#skF_9')), inference(resolution, [status(thm)], [c_60, c_10861])).
% 7.10/2.55  tff(c_10875, plain, (![A_3007]: (A_3007!='#skF_9' | '#skF_6'(A_3007)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_10867])).
% 7.10/2.55  tff(c_58, plain, (![A_24]: (v1_funct_1('#skF_6'(A_24)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.10/2.55  tff(c_10883, plain, (![A_3007]: (v1_funct_1('#skF_9') | A_3007!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_10875, c_58])).
% 7.10/2.55  tff(c_10891, plain, (![A_3007]: (A_3007!='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_10825, c_10883])).
% 7.10/2.55  tff(c_10830, plain, (![A_12]: (k3_xboole_0(A_12, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_10808, c_10808, c_26])).
% 7.10/2.55  tff(c_10900, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10891, c_10830])).
% 7.10/2.55  tff(c_10902, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_74])).
% 7.10/2.55  tff(c_10901, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_74])).
% 7.10/2.55  tff(c_10911, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_10902, c_10901])).
% 7.10/2.55  tff(c_10905, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_10901, c_10901, c_48])).
% 7.10/2.55  tff(c_10921, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_10911, c_10911, c_10905])).
% 7.10/2.55  tff(c_10904, plain, (![A_13]: (r1_tarski('#skF_9', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_10901, c_28])).
% 7.10/2.55  tff(c_10926, plain, (![A_13]: (r1_tarski('#skF_8', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_10911, c_10904])).
% 7.10/2.55  tff(c_10903, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_10901, c_10901, c_46])).
% 7.10/2.55  tff(c_10928, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_10911, c_10911, c_10903])).
% 7.10/2.55  tff(c_10984, plain, (![C_3015]: (~r1_tarski(k2_relat_1(C_3015), '#skF_8') | k1_relat_1(C_3015)!='#skF_8' | ~v1_funct_1(C_3015) | ~v1_relat_1(C_3015))), inference(demodulation, [status(thm), theory('equality')], [c_10911, c_72])).
% 7.10/2.55  tff(c_10987, plain, (~r1_tarski('#skF_8', '#skF_8') | k1_relat_1('#skF_8')!='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_10928, c_10984])).
% 7.10/2.55  tff(c_10989, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_10921, c_10926, c_10987])).
% 7.10/2.55  tff(c_10990, plain, (~v1_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_10989])).
% 7.10/2.55  tff(c_11038, plain, (![A_3027]: (k1_relat_1(A_3027)!='#skF_8' | A_3027='#skF_8' | ~v1_relat_1(A_3027))), inference(demodulation, [status(thm), theory('equality')], [c_10902, c_10902, c_52])).
% 7.10/2.55  tff(c_11044, plain, (![A_24]: (k1_relat_1('#skF_6'(A_24))!='#skF_8' | '#skF_6'(A_24)='#skF_8')), inference(resolution, [status(thm)], [c_60, c_11038])).
% 7.10/2.55  tff(c_11050, plain, (![A_3030]: (A_3030!='#skF_8' | '#skF_6'(A_3030)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_11044])).
% 7.10/2.55  tff(c_11060, plain, (![A_3030]: (v1_relat_1('#skF_8') | A_3030!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_11050, c_60])).
% 7.10/2.55  tff(c_11066, plain, (![A_3030]: (A_3030!='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_10990, c_11060])).
% 7.10/2.55  tff(c_10942, plain, (![A_12]: (k3_xboole_0(A_12, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_10902, c_10902, c_26])).
% 7.10/2.55  tff(c_11079, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11066, c_10942])).
% 7.10/2.55  tff(c_11080, plain, (~v1_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_10989])).
% 7.10/2.55  tff(c_11110, plain, (![A_3038]: (k1_relat_1(A_3038)!='#skF_8' | A_3038='#skF_8' | ~v1_relat_1(A_3038))), inference(demodulation, [status(thm), theory('equality')], [c_10902, c_10902, c_52])).
% 7.10/2.55  tff(c_11119, plain, (![A_24]: (k1_relat_1('#skF_6'(A_24))!='#skF_8' | '#skF_6'(A_24)='#skF_8')), inference(resolution, [status(thm)], [c_60, c_11110])).
% 7.10/2.55  tff(c_11143, plain, (![A_3041]: (A_3041!='#skF_8' | '#skF_6'(A_3041)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_11119])).
% 7.10/2.55  tff(c_11151, plain, (![A_3041]: (v1_funct_1('#skF_8') | A_3041!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_11143, c_58])).
% 7.10/2.55  tff(c_11159, plain, (![A_3041]: (A_3041!='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_11080, c_11151])).
% 7.10/2.55  tff(c_11172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11159, c_10942])).
% 7.10/2.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.10/2.55  
% 7.10/2.55  Inference rules
% 7.10/2.55  ----------------------
% 7.10/2.55  #Ref     : 1
% 7.10/2.55  #Sup     : 1902
% 7.10/2.55  #Fact    : 2
% 7.10/2.55  #Define  : 0
% 7.10/2.55  #Split   : 10
% 7.10/2.55  #Chain   : 0
% 7.10/2.55  #Close   : 0
% 7.10/2.55  
% 7.10/2.55  Ordering : KBO
% 7.10/2.55  
% 7.10/2.55  Simplification rules
% 7.10/2.55  ----------------------
% 7.10/2.55  #Subsume      : 561
% 7.10/2.55  #Demod        : 746
% 7.10/2.55  #Tautology    : 377
% 7.10/2.55  #SimpNegUnit  : 105
% 7.10/2.55  #BackRed      : 173
% 7.10/2.55  
% 7.10/2.55  #Partial instantiations: 1836
% 7.10/2.55  #Strategies tried      : 1
% 7.10/2.55  
% 7.10/2.55  Timing (in seconds)
% 7.10/2.55  ----------------------
% 7.10/2.55  Preprocessing        : 0.35
% 7.10/2.55  Parsing              : 0.18
% 7.10/2.55  CNF conversion       : 0.03
% 7.10/2.55  Main loop            : 1.36
% 7.10/2.55  Inferencing          : 0.44
% 7.10/2.55  Reduction            : 0.43
% 7.10/2.55  Demodulation         : 0.31
% 7.10/2.55  BG Simplification    : 0.07
% 7.10/2.55  Subsumption          : 0.29
% 7.10/2.55  Abstraction          : 0.08
% 7.10/2.55  MUC search           : 0.00
% 7.10/2.55  Cooper               : 0.00
% 7.10/2.55  Total                : 1.76
% 7.10/2.55  Index Insertion      : 0.00
% 7.10/2.55  Index Deletion       : 0.00
% 7.10/2.55  Index Matching       : 0.00
% 7.10/2.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
