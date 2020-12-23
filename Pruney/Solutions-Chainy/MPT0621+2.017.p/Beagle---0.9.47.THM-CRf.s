%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:01 EST 2020

% Result     : Theorem 17.41s
% Output     : CNFRefutation 17.87s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 305 expanded)
%              Number of leaves         :   32 ( 121 expanded)
%              Depth                    :   15
%              Number of atoms          :  185 ( 906 expanded)
%              Number of equality atoms :   94 ( 428 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_1 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_2 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_93,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ! [A_31,B_32] : k1_relat_1('#skF_8'(A_31,B_32)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ! [A_31,B_32] : v1_funct_1('#skF_8'(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    ! [A_31,B_32] : v1_relat_1('#skF_8'(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42,plain,(
    ! [A_38] : v1_funct_1('#skF_9'(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_40,plain,(
    ! [A_38] : k1_relat_1('#skF_9'(A_38)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_44,plain,(
    ! [A_38] : v1_relat_1('#skF_9'(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_69,plain,(
    ! [C_60,B_61] :
      ( C_60 = B_61
      | k1_relat_1(C_60) != '#skF_10'
      | k1_relat_1(B_61) != '#skF_10'
      | ~ v1_funct_1(C_60)
      | ~ v1_relat_1(C_60)
      | ~ v1_funct_1(B_61)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_73,plain,(
    ! [B_61,A_38] :
      ( B_61 = '#skF_9'(A_38)
      | k1_relat_1('#skF_9'(A_38)) != '#skF_10'
      | k1_relat_1(B_61) != '#skF_10'
      | ~ v1_funct_1('#skF_9'(A_38))
      | ~ v1_funct_1(B_61)
      | ~ v1_relat_1(B_61) ) ),
    inference(resolution,[status(thm)],[c_44,c_69])).

tff(c_167,plain,(
    ! [B_79,A_80] :
      ( B_79 = '#skF_9'(A_80)
      | A_80 != '#skF_10'
      | k1_relat_1(B_79) != '#skF_10'
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_73])).

tff(c_169,plain,(
    ! [A_80,A_31,B_32] :
      ( '#skF_9'(A_80) = '#skF_8'(A_31,B_32)
      | A_80 != '#skF_10'
      | k1_relat_1('#skF_8'(A_31,B_32)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_31,B_32)) ) ),
    inference(resolution,[status(thm)],[c_36,c_167])).

tff(c_174,plain,(
    ! [A_80,A_31,B_32] :
      ( '#skF_9'(A_80) = '#skF_8'(A_31,B_32)
      | A_80 != '#skF_10'
      | A_31 != '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_169])).

tff(c_467,plain,(
    ! [C_101,A_102] :
      ( r2_hidden(k4_tarski(C_101,'#skF_5'(A_102,k1_relat_1(A_102),C_101)),A_102)
      | ~ r2_hidden(C_101,k1_relat_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_486,plain,(
    ! [C_101,A_38] :
      ( r2_hidden(k4_tarski(C_101,'#skF_5'('#skF_9'(A_38),A_38,C_101)),'#skF_9'(A_38))
      | ~ r2_hidden(C_101,k1_relat_1('#skF_9'(A_38))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_467])).

tff(c_2564,plain,(
    ! [C_212,A_213] :
      ( r2_hidden(k4_tarski(C_212,'#skF_5'('#skF_9'(A_213),A_213,C_212)),'#skF_9'(A_213))
      | ~ r2_hidden(C_212,A_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_486])).

tff(c_51651,plain,(
    ! [C_879,A_880,A_881,B_882] :
      ( r2_hidden(k4_tarski(C_879,'#skF_5'('#skF_9'(A_880),A_880,C_879)),'#skF_8'(A_881,B_882))
      | ~ r2_hidden(C_879,A_880)
      | A_880 != '#skF_10'
      | A_881 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_2564])).

tff(c_12,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k1_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(C_21,D_24),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_51676,plain,(
    ! [C_879,A_881,B_882,A_880] :
      ( r2_hidden(C_879,k1_relat_1('#skF_8'(A_881,B_882)))
      | ~ r2_hidden(C_879,A_880)
      | A_880 != '#skF_10'
      | A_881 != '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_51651,c_12])).

tff(c_53845,plain,(
    ! [C_907,A_908,A_909] :
      ( r2_hidden(C_907,A_908)
      | ~ r2_hidden(C_907,A_909)
      | A_909 != '#skF_10'
      | A_908 != '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_51676])).

tff(c_54034,plain,(
    ! [A_1,A_908] :
      ( r2_hidden('#skF_1'(A_1),A_908)
      | A_1 != '#skF_10'
      | A_908 != '#skF_10'
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_53845])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_655,plain,(
    ! [A_123,A_124,B_125] :
      ( '#skF_9'(A_123) = '#skF_8'(A_124,B_125)
      | A_123 != '#skF_10'
      | A_124 != '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_169])).

tff(c_94,plain,(
    ! [A_65] :
      ( k7_relat_1(A_65,k1_relat_1(A_65)) = A_65
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_103,plain,(
    ! [A_31,B_32] :
      ( k7_relat_1('#skF_8'(A_31,B_32),A_31) = '#skF_8'(A_31,B_32)
      | ~ v1_relat_1('#skF_8'(A_31,B_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_94])).

tff(c_110,plain,(
    ! [A_31,B_32] : k7_relat_1('#skF_8'(A_31,B_32),A_31) = '#skF_8'(A_31,B_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_103])).

tff(c_12555,plain,(
    ! [A_396,A_397,B_398] :
      ( k7_relat_1('#skF_9'(A_396),A_397) = '#skF_8'(A_397,B_398)
      | A_396 != '#skF_10'
      | A_397 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_655,c_110])).

tff(c_28,plain,(
    ! [A_30] :
      ( k7_relat_1(A_30,k1_relat_1(A_30)) = A_30
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12741,plain,(
    ! [A_396,B_398] :
      ( '#skF_8'(k1_relat_1('#skF_9'(A_396)),B_398) = '#skF_9'(A_396)
      | ~ v1_relat_1('#skF_9'(A_396))
      | A_396 != '#skF_10'
      | k1_relat_1('#skF_9'(A_396)) != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12555,c_28])).

tff(c_12837,plain,(
    ! [A_399,B_400] :
      ( '#skF_9'(A_399) = '#skF_8'(A_399,B_400)
      | A_399 != '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_40,c_12741])).

tff(c_30,plain,(
    ! [A_31,B_32,D_37] :
      ( k1_funct_1('#skF_8'(A_31,B_32),D_37) = B_32
      | ~ r2_hidden(D_37,A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_57710,plain,(
    ! [A_956,D_957] :
      ( k1_funct_1('#skF_9'(A_956),D_957) = '#skF_10'
      | ~ r2_hidden(D_957,A_956)
      | A_956 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12837,c_30])).

tff(c_38,plain,(
    ! [A_38,C_43] :
      ( k1_funct_1('#skF_9'(A_38),C_43) = k1_xboole_0
      | ~ r2_hidden(C_43,A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_57713,plain,(
    ! [D_957,A_956] :
      ( k1_xboole_0 = '#skF_10'
      | ~ r2_hidden(D_957,A_956)
      | ~ r2_hidden(D_957,A_956)
      | A_956 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57710,c_38])).

tff(c_57910,plain,(
    ! [D_11293,A_11294] :
      ( ~ r2_hidden(D_11293,A_11294)
      | ~ r2_hidden(D_11293,A_11294)
      | A_11294 != '#skF_10' ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_57713])).

tff(c_58119,plain,(
    ! [A_11317] :
      ( ~ r2_hidden('#skF_1'(A_11317),A_11317)
      | A_11317 != '#skF_10'
      | v1_xboole_0(A_11317) ) ),
    inference(resolution,[status(thm)],[c_4,c_57910])).

tff(c_58132,plain,(
    ! [A_11340] :
      ( A_11340 != '#skF_10'
      | v1_xboole_0(A_11340) ) ),
    inference(resolution,[status(thm)],[c_54034,c_58119])).

tff(c_423,plain,(
    ! [A_97] :
      ( k1_xboole_0 = A_97
      | r2_hidden(k4_tarski('#skF_6'(A_97),'#skF_7'(A_97)),A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1349,plain,(
    ! [A_160] :
      ( r2_hidden('#skF_6'(A_160),k1_relat_1(A_160))
      | k1_xboole_0 = A_160
      | ~ v1_relat_1(A_160) ) ),
    inference(resolution,[status(thm)],[c_423,c_12])).

tff(c_1378,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_6'('#skF_8'(A_31,B_32)),A_31)
      | '#skF_8'(A_31,B_32) = k1_xboole_0
      | ~ v1_relat_1('#skF_8'(A_31,B_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1349])).

tff(c_4815,plain,(
    ! [A_264,B_265] :
      ( r2_hidden('#skF_6'('#skF_8'(A_264,B_265)),A_264)
      | '#skF_8'(A_264,B_265) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1378])).

tff(c_35346,plain,(
    ! [A_749,A_750,B_751] :
      ( r2_hidden('#skF_6'('#skF_9'(A_749)),A_750)
      | '#skF_8'(A_750,B_751) = k1_xboole_0
      | A_749 != '#skF_10'
      | A_750 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_4815])).

tff(c_106,plain,(
    ! [A_38] :
      ( k7_relat_1('#skF_9'(A_38),A_38) = '#skF_9'(A_38)
      | ~ v1_relat_1('#skF_9'(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_94])).

tff(c_112,plain,(
    ! [A_38] : k7_relat_1('#skF_9'(A_38),A_38) = '#skF_9'(A_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_106])).

tff(c_150,plain,(
    ! [B_77,A_78] :
      ( r1_xboole_0(k1_relat_1(B_77),A_78)
      | k7_relat_1(B_77,A_78) != k1_xboole_0
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_160,plain,(
    ! [A_38,A_78] :
      ( r1_xboole_0(A_38,A_78)
      | k7_relat_1('#skF_9'(A_38),A_78) != k1_xboole_0
      | ~ v1_relat_1('#skF_9'(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_150])).

tff(c_178,plain,(
    ! [A_81,A_82] :
      ( r1_xboole_0(A_81,A_82)
      | k7_relat_1('#skF_9'(A_81),A_82) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_160])).

tff(c_188,plain,(
    ! [A_83] :
      ( r1_xboole_0(A_83,A_83)
      | '#skF_9'(A_83) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_178])).

tff(c_8,plain,(
    ! [A_5] :
      ( ~ r1_xboole_0(A_5,A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_192,plain,(
    ! [A_83] :
      ( k1_xboole_0 = A_83
      | '#skF_9'(A_83) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_188,c_8])).

tff(c_692,plain,(
    ! [A_123,A_124,B_125] :
      ( k1_xboole_0 = A_123
      | '#skF_8'(A_124,B_125) != k1_xboole_0
      | A_123 != '#skF_10'
      | A_124 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_655,c_192])).

tff(c_5171,plain,(
    ! [A_124,B_125] :
      ( '#skF_8'(A_124,B_125) != k1_xboole_0
      | A_124 != '#skF_10' ) ),
    inference(splitLeft,[status(thm)],[c_692])).

tff(c_36013,plain,(
    ! [A_752,A_753] :
      ( r2_hidden('#skF_6'('#skF_9'(A_752)),A_753)
      | A_752 != '#skF_10'
      | A_753 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35346,c_5171])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36168,plain,(
    ! [A_753,A_752] :
      ( ~ v1_xboole_0(A_753)
      | A_752 != '#skF_10'
      | A_753 != '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_36013,c_2])).

tff(c_36169,plain,(
    ! [A_753] :
      ( ~ v1_xboole_0(A_753)
      | A_753 != '#skF_10' ) ),
    inference(splitLeft,[status(thm)],[c_36168])).

tff(c_58464,plain,(
    ! [A_11340] : A_11340 != '#skF_10' ),
    inference(resolution,[status(thm)],[c_58132,c_36169])).

tff(c_58570,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_58464])).

tff(c_58571,plain,(
    ! [A_752] : A_752 != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_36168])).

tff(c_58575,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_58571])).

tff(c_58577,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_692])).

tff(c_58643,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58577,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:25:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.41/9.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.41/9.33  
% 17.41/9.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.41/9.33  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_1 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_2 > #skF_6 > #skF_4
% 17.41/9.33  
% 17.41/9.33  %Foreground sorts:
% 17.41/9.33  
% 17.41/9.33  
% 17.41/9.33  %Background operators:
% 17.41/9.33  
% 17.41/9.33  
% 17.41/9.33  %Foreground operators:
% 17.41/9.33  tff('#skF_9', type, '#skF_9': $i > $i).
% 17.41/9.33  tff('#skF_7', type, '#skF_7': $i > $i).
% 17.41/9.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 17.41/9.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.41/9.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.41/9.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 17.41/9.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 17.41/9.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 17.41/9.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.41/9.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 17.41/9.33  tff('#skF_10', type, '#skF_10': $i).
% 17.41/9.33  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 17.41/9.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 17.41/9.33  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 17.41/9.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 17.41/9.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.41/9.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 17.41/9.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.41/9.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 17.41/9.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 17.41/9.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 17.41/9.33  tff('#skF_6', type, '#skF_6': $i > $i).
% 17.41/9.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 17.41/9.33  
% 17.87/9.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 17.87/9.35  tff(f_81, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 17.87/9.35  tff(f_93, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 17.87/9.35  tff(f_112, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 17.87/9.35  tff(f_51, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 17.87/9.35  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 17.87/9.35  tff(f_59, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 17.87/9.35  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 17.87/9.35  tff(f_43, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 17.87/9.35  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.87/9.35  tff(c_32, plain, (![A_31, B_32]: (k1_relat_1('#skF_8'(A_31, B_32))=A_31)), inference(cnfTransformation, [status(thm)], [f_81])).
% 17.87/9.35  tff(c_34, plain, (![A_31, B_32]: (v1_funct_1('#skF_8'(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 17.87/9.35  tff(c_36, plain, (![A_31, B_32]: (v1_relat_1('#skF_8'(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 17.87/9.35  tff(c_42, plain, (![A_38]: (v1_funct_1('#skF_9'(A_38)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 17.87/9.35  tff(c_40, plain, (![A_38]: (k1_relat_1('#skF_9'(A_38))=A_38)), inference(cnfTransformation, [status(thm)], [f_93])).
% 17.87/9.35  tff(c_44, plain, (![A_38]: (v1_relat_1('#skF_9'(A_38)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 17.87/9.35  tff(c_69, plain, (![C_60, B_61]: (C_60=B_61 | k1_relat_1(C_60)!='#skF_10' | k1_relat_1(B_61)!='#skF_10' | ~v1_funct_1(C_60) | ~v1_relat_1(C_60) | ~v1_funct_1(B_61) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_112])).
% 17.87/9.35  tff(c_73, plain, (![B_61, A_38]: (B_61='#skF_9'(A_38) | k1_relat_1('#skF_9'(A_38))!='#skF_10' | k1_relat_1(B_61)!='#skF_10' | ~v1_funct_1('#skF_9'(A_38)) | ~v1_funct_1(B_61) | ~v1_relat_1(B_61))), inference(resolution, [status(thm)], [c_44, c_69])).
% 17.87/9.35  tff(c_167, plain, (![B_79, A_80]: (B_79='#skF_9'(A_80) | A_80!='#skF_10' | k1_relat_1(B_79)!='#skF_10' | ~v1_funct_1(B_79) | ~v1_relat_1(B_79))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_73])).
% 17.87/9.35  tff(c_169, plain, (![A_80, A_31, B_32]: ('#skF_9'(A_80)='#skF_8'(A_31, B_32) | A_80!='#skF_10' | k1_relat_1('#skF_8'(A_31, B_32))!='#skF_10' | ~v1_funct_1('#skF_8'(A_31, B_32)))), inference(resolution, [status(thm)], [c_36, c_167])).
% 17.87/9.35  tff(c_174, plain, (![A_80, A_31, B_32]: ('#skF_9'(A_80)='#skF_8'(A_31, B_32) | A_80!='#skF_10' | A_31!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_169])).
% 17.87/9.35  tff(c_467, plain, (![C_101, A_102]: (r2_hidden(k4_tarski(C_101, '#skF_5'(A_102, k1_relat_1(A_102), C_101)), A_102) | ~r2_hidden(C_101, k1_relat_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.87/9.35  tff(c_486, plain, (![C_101, A_38]: (r2_hidden(k4_tarski(C_101, '#skF_5'('#skF_9'(A_38), A_38, C_101)), '#skF_9'(A_38)) | ~r2_hidden(C_101, k1_relat_1('#skF_9'(A_38))))), inference(superposition, [status(thm), theory('equality')], [c_40, c_467])).
% 17.87/9.35  tff(c_2564, plain, (![C_212, A_213]: (r2_hidden(k4_tarski(C_212, '#skF_5'('#skF_9'(A_213), A_213, C_212)), '#skF_9'(A_213)) | ~r2_hidden(C_212, A_213))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_486])).
% 17.87/9.35  tff(c_51651, plain, (![C_879, A_880, A_881, B_882]: (r2_hidden(k4_tarski(C_879, '#skF_5'('#skF_9'(A_880), A_880, C_879)), '#skF_8'(A_881, B_882)) | ~r2_hidden(C_879, A_880) | A_880!='#skF_10' | A_881!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_174, c_2564])).
% 17.87/9.35  tff(c_12, plain, (![C_21, A_6, D_24]: (r2_hidden(C_21, k1_relat_1(A_6)) | ~r2_hidden(k4_tarski(C_21, D_24), A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.87/9.35  tff(c_51676, plain, (![C_879, A_881, B_882, A_880]: (r2_hidden(C_879, k1_relat_1('#skF_8'(A_881, B_882))) | ~r2_hidden(C_879, A_880) | A_880!='#skF_10' | A_881!='#skF_10')), inference(resolution, [status(thm)], [c_51651, c_12])).
% 17.87/9.35  tff(c_53845, plain, (![C_907, A_908, A_909]: (r2_hidden(C_907, A_908) | ~r2_hidden(C_907, A_909) | A_909!='#skF_10' | A_908!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_51676])).
% 17.87/9.35  tff(c_54034, plain, (![A_1, A_908]: (r2_hidden('#skF_1'(A_1), A_908) | A_1!='#skF_10' | A_908!='#skF_10' | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_53845])).
% 17.87/9.35  tff(c_46, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_112])).
% 17.87/9.35  tff(c_655, plain, (![A_123, A_124, B_125]: ('#skF_9'(A_123)='#skF_8'(A_124, B_125) | A_123!='#skF_10' | A_124!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_169])).
% 17.87/9.35  tff(c_94, plain, (![A_65]: (k7_relat_1(A_65, k1_relat_1(A_65))=A_65 | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_69])).
% 17.87/9.35  tff(c_103, plain, (![A_31, B_32]: (k7_relat_1('#skF_8'(A_31, B_32), A_31)='#skF_8'(A_31, B_32) | ~v1_relat_1('#skF_8'(A_31, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_94])).
% 17.87/9.35  tff(c_110, plain, (![A_31, B_32]: (k7_relat_1('#skF_8'(A_31, B_32), A_31)='#skF_8'(A_31, B_32))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_103])).
% 17.87/9.35  tff(c_12555, plain, (![A_396, A_397, B_398]: (k7_relat_1('#skF_9'(A_396), A_397)='#skF_8'(A_397, B_398) | A_396!='#skF_10' | A_397!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_655, c_110])).
% 17.87/9.35  tff(c_28, plain, (![A_30]: (k7_relat_1(A_30, k1_relat_1(A_30))=A_30 | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_69])).
% 17.87/9.35  tff(c_12741, plain, (![A_396, B_398]: ('#skF_8'(k1_relat_1('#skF_9'(A_396)), B_398)='#skF_9'(A_396) | ~v1_relat_1('#skF_9'(A_396)) | A_396!='#skF_10' | k1_relat_1('#skF_9'(A_396))!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_12555, c_28])).
% 17.87/9.35  tff(c_12837, plain, (![A_399, B_400]: ('#skF_9'(A_399)='#skF_8'(A_399, B_400) | A_399!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_40, c_12741])).
% 17.87/9.35  tff(c_30, plain, (![A_31, B_32, D_37]: (k1_funct_1('#skF_8'(A_31, B_32), D_37)=B_32 | ~r2_hidden(D_37, A_31))), inference(cnfTransformation, [status(thm)], [f_81])).
% 17.87/9.35  tff(c_57710, plain, (![A_956, D_957]: (k1_funct_1('#skF_9'(A_956), D_957)='#skF_10' | ~r2_hidden(D_957, A_956) | A_956!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_12837, c_30])).
% 17.87/9.35  tff(c_38, plain, (![A_38, C_43]: (k1_funct_1('#skF_9'(A_38), C_43)=k1_xboole_0 | ~r2_hidden(C_43, A_38))), inference(cnfTransformation, [status(thm)], [f_93])).
% 17.87/9.35  tff(c_57713, plain, (![D_957, A_956]: (k1_xboole_0='#skF_10' | ~r2_hidden(D_957, A_956) | ~r2_hidden(D_957, A_956) | A_956!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_57710, c_38])).
% 17.87/9.35  tff(c_57910, plain, (![D_11293, A_11294]: (~r2_hidden(D_11293, A_11294) | ~r2_hidden(D_11293, A_11294) | A_11294!='#skF_10')), inference(negUnitSimplification, [status(thm)], [c_46, c_57713])).
% 17.87/9.35  tff(c_58119, plain, (![A_11317]: (~r2_hidden('#skF_1'(A_11317), A_11317) | A_11317!='#skF_10' | v1_xboole_0(A_11317))), inference(resolution, [status(thm)], [c_4, c_57910])).
% 17.87/9.35  tff(c_58132, plain, (![A_11340]: (A_11340!='#skF_10' | v1_xboole_0(A_11340))), inference(resolution, [status(thm)], [c_54034, c_58119])).
% 17.87/9.35  tff(c_423, plain, (![A_97]: (k1_xboole_0=A_97 | r2_hidden(k4_tarski('#skF_6'(A_97), '#skF_7'(A_97)), A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_59])).
% 17.87/9.35  tff(c_1349, plain, (![A_160]: (r2_hidden('#skF_6'(A_160), k1_relat_1(A_160)) | k1_xboole_0=A_160 | ~v1_relat_1(A_160))), inference(resolution, [status(thm)], [c_423, c_12])).
% 17.87/9.35  tff(c_1378, plain, (![A_31, B_32]: (r2_hidden('#skF_6'('#skF_8'(A_31, B_32)), A_31) | '#skF_8'(A_31, B_32)=k1_xboole_0 | ~v1_relat_1('#skF_8'(A_31, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1349])).
% 17.87/9.35  tff(c_4815, plain, (![A_264, B_265]: (r2_hidden('#skF_6'('#skF_8'(A_264, B_265)), A_264) | '#skF_8'(A_264, B_265)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1378])).
% 17.87/9.35  tff(c_35346, plain, (![A_749, A_750, B_751]: (r2_hidden('#skF_6'('#skF_9'(A_749)), A_750) | '#skF_8'(A_750, B_751)=k1_xboole_0 | A_749!='#skF_10' | A_750!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_174, c_4815])).
% 17.87/9.35  tff(c_106, plain, (![A_38]: (k7_relat_1('#skF_9'(A_38), A_38)='#skF_9'(A_38) | ~v1_relat_1('#skF_9'(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_94])).
% 17.87/9.35  tff(c_112, plain, (![A_38]: (k7_relat_1('#skF_9'(A_38), A_38)='#skF_9'(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_106])).
% 17.87/9.35  tff(c_150, plain, (![B_77, A_78]: (r1_xboole_0(k1_relat_1(B_77), A_78) | k7_relat_1(B_77, A_78)!=k1_xboole_0 | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_65])).
% 17.87/9.35  tff(c_160, plain, (![A_38, A_78]: (r1_xboole_0(A_38, A_78) | k7_relat_1('#skF_9'(A_38), A_78)!=k1_xboole_0 | ~v1_relat_1('#skF_9'(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_150])).
% 17.87/9.35  tff(c_178, plain, (![A_81, A_82]: (r1_xboole_0(A_81, A_82) | k7_relat_1('#skF_9'(A_81), A_82)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_160])).
% 17.87/9.35  tff(c_188, plain, (![A_83]: (r1_xboole_0(A_83, A_83) | '#skF_9'(A_83)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_112, c_178])).
% 17.87/9.35  tff(c_8, plain, (![A_5]: (~r1_xboole_0(A_5, A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.87/9.35  tff(c_192, plain, (![A_83]: (k1_xboole_0=A_83 | '#skF_9'(A_83)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_188, c_8])).
% 17.87/9.35  tff(c_692, plain, (![A_123, A_124, B_125]: (k1_xboole_0=A_123 | '#skF_8'(A_124, B_125)!=k1_xboole_0 | A_123!='#skF_10' | A_124!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_655, c_192])).
% 17.87/9.35  tff(c_5171, plain, (![A_124, B_125]: ('#skF_8'(A_124, B_125)!=k1_xboole_0 | A_124!='#skF_10')), inference(splitLeft, [status(thm)], [c_692])).
% 17.87/9.35  tff(c_36013, plain, (![A_752, A_753]: (r2_hidden('#skF_6'('#skF_9'(A_752)), A_753) | A_752!='#skF_10' | A_753!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_35346, c_5171])).
% 17.87/9.35  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.87/9.35  tff(c_36168, plain, (![A_753, A_752]: (~v1_xboole_0(A_753) | A_752!='#skF_10' | A_753!='#skF_10')), inference(resolution, [status(thm)], [c_36013, c_2])).
% 17.87/9.35  tff(c_36169, plain, (![A_753]: (~v1_xboole_0(A_753) | A_753!='#skF_10')), inference(splitLeft, [status(thm)], [c_36168])).
% 17.87/9.35  tff(c_58464, plain, (![A_11340]: (A_11340!='#skF_10')), inference(resolution, [status(thm)], [c_58132, c_36169])).
% 17.87/9.35  tff(c_58570, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_58464])).
% 17.87/9.35  tff(c_58571, plain, (![A_752]: (A_752!='#skF_10')), inference(splitRight, [status(thm)], [c_36168])).
% 17.87/9.35  tff(c_58575, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_58571])).
% 17.87/9.35  tff(c_58577, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_692])).
% 17.87/9.35  tff(c_58643, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58577, c_46])).
% 17.87/9.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.87/9.35  
% 17.87/9.35  Inference rules
% 17.87/9.35  ----------------------
% 17.87/9.35  #Ref     : 3
% 17.87/9.35  #Sup     : 16152
% 17.87/9.35  #Fact    : 0
% 17.87/9.35  #Define  : 0
% 17.87/9.35  #Split   : 9
% 17.87/9.35  #Chain   : 0
% 17.87/9.35  #Close   : 0
% 17.87/9.35  
% 17.87/9.35  Ordering : KBO
% 17.87/9.35  
% 17.87/9.35  Simplification rules
% 17.87/9.35  ----------------------
% 17.87/9.35  #Subsume      : 7609
% 17.87/9.35  #Demod        : 9680
% 17.87/9.35  #Tautology    : 3050
% 17.87/9.35  #SimpNegUnit  : 288
% 17.87/9.35  #BackRed      : 64
% 17.87/9.35  
% 17.87/9.35  #Partial instantiations: 7065
% 17.87/9.35  #Strategies tried      : 1
% 17.87/9.35  
% 17.87/9.35  Timing (in seconds)
% 17.87/9.35  ----------------------
% 17.87/9.35  Preprocessing        : 0.33
% 17.87/9.36  Parsing              : 0.18
% 17.87/9.36  CNF conversion       : 0.03
% 17.87/9.36  Main loop            : 8.20
% 17.87/9.36  Inferencing          : 1.23
% 17.87/9.36  Reduction            : 2.07
% 17.87/9.36  Demodulation         : 1.45
% 17.87/9.36  BG Simplification    : 0.14
% 17.87/9.36  Subsumption          : 4.14
% 17.87/9.36  Abstraction          : 0.21
% 17.87/9.36  MUC search           : 0.00
% 17.87/9.36  Cooper               : 0.00
% 17.87/9.36  Total                : 8.57
% 17.87/9.36  Index Insertion      : 0.00
% 17.87/9.36  Index Deletion       : 0.00
% 17.87/9.36  Index Matching       : 0.00
% 17.87/9.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
