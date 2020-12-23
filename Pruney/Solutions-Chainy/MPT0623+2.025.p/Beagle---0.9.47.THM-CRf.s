%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:09 EST 2020

% Result     : Theorem 20.51s
% Output     : CNFRefutation 20.78s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 499 expanded)
%              Number of leaves         :   39 ( 172 expanded)
%              Depth                    :   15
%              Number of atoms          :  225 (1253 expanded)
%              Number of equality atoms :  123 ( 725 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_8 > #skF_7 > #skF_2 > #skF_1 > #skF_9 > #skF_5 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_87,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

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

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_63,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_75,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_60,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_74,plain,
    ( k1_xboole_0 = '#skF_11'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_104,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_58,plain,(
    ! [A_38,B_39] : k1_relat_1('#skF_8'(A_38,B_39)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3611,plain,(
    ! [A_6415,B_6416] :
      ( r2_hidden(k4_tarski('#skF_4'(A_6415,B_6416),'#skF_5'(A_6415,B_6416)),A_6415)
      | r2_hidden('#skF_6'(A_6415,B_6416),B_6416)
      | k1_relat_1(A_6415) = B_6416 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32,plain,(
    ! [C_31,A_16,D_34] :
      ( r2_hidden(C_31,k1_relat_1(A_16))
      | ~ r2_hidden(k4_tarski(C_31,D_34),A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_7899,plain,(
    ! [A_16181,B_16182] :
      ( r2_hidden('#skF_4'(A_16181,B_16182),k1_relat_1(A_16181))
      | r2_hidden('#skF_6'(A_16181,B_16182),B_16182)
      | k1_relat_1(A_16181) = B_16182 ) ),
    inference(resolution,[status(thm)],[c_3611,c_32])).

tff(c_7935,plain,(
    ! [A_38,B_39,B_16182] :
      ( r2_hidden('#skF_4'('#skF_8'(A_38,B_39),B_16182),A_38)
      | r2_hidden('#skF_6'('#skF_8'(A_38,B_39),B_16182),B_16182)
      | k1_relat_1('#skF_8'(A_38,B_39)) = B_16182 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_7899])).

tff(c_23964,plain,(
    ! [A_24432,B_24433,B_24434] :
      ( r2_hidden('#skF_4'('#skF_8'(A_24432,B_24433),B_24434),A_24432)
      | r2_hidden('#skF_6'('#skF_8'(A_24432,B_24433),B_24434),B_24434)
      | B_24434 = A_24432 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_7935])).

tff(c_24,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_138,plain,(
    ! [A_66,B_67] : ~ r2_hidden(A_66,k2_zfmisc_1(A_66,B_67)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_144,plain,(
    ! [A_12] : ~ r2_hidden(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_138])).

tff(c_24203,plain,(
    ! [A_24432,B_24433] :
      ( r2_hidden('#skF_4'('#skF_8'(A_24432,B_24433),k1_xboole_0),A_24432)
      | k1_xboole_0 = A_24432 ) ),
    inference(resolution,[status(thm)],[c_23964,c_144])).

tff(c_66,plain,(
    ! [A_45,B_49] :
      ( k1_relat_1('#skF_9'(A_45,B_49)) = A_45
      | k1_xboole_0 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_68,plain,(
    ! [A_45,B_49] :
      ( v1_funct_1('#skF_9'(A_45,B_49))
      | k1_xboole_0 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_70,plain,(
    ! [A_45,B_49] :
      ( v1_relat_1('#skF_9'(A_45,B_49))
      | k1_xboole_0 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_375,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_1'(A_95,B_96),A_95)
      | r1_tarski(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_447,plain,(
    ! [A_117,B_118] :
      ( '#skF_1'(k1_tarski(A_117),B_118) = A_117
      | r1_tarski(k1_tarski(A_117),B_118) ) ),
    inference(resolution,[status(thm)],[c_375,c_10])).

tff(c_352,plain,(
    ! [A_91,B_92] :
      ( k2_relat_1('#skF_9'(A_91,B_92)) = k1_tarski(B_92)
      | k1_xboole_0 = A_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_72,plain,(
    ! [C_52] :
      ( ~ r1_tarski(k2_relat_1(C_52),'#skF_10')
      | k1_relat_1(C_52) != '#skF_11'
      | ~ v1_funct_1(C_52)
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_358,plain,(
    ! [B_92,A_91] :
      ( ~ r1_tarski(k1_tarski(B_92),'#skF_10')
      | k1_relat_1('#skF_9'(A_91,B_92)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_91,B_92))
      | ~ v1_relat_1('#skF_9'(A_91,B_92))
      | k1_xboole_0 = A_91 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_72])).

tff(c_477,plain,(
    ! [A_121,A_122] :
      ( k1_relat_1('#skF_9'(A_121,A_122)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_121,A_122))
      | ~ v1_relat_1('#skF_9'(A_121,A_122))
      | k1_xboole_0 = A_121
      | '#skF_1'(k1_tarski(A_122),'#skF_10') = A_122 ) ),
    inference(resolution,[status(thm)],[c_447,c_358])).

tff(c_30039,plain,(
    ! [A_26224,B_26225] :
      ( k1_relat_1('#skF_9'(A_26224,B_26225)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_26224,B_26225))
      | '#skF_1'(k1_tarski(B_26225),'#skF_10') = B_26225
      | k1_xboole_0 = A_26224 ) ),
    inference(resolution,[status(thm)],[c_70,c_477])).

tff(c_48254,plain,(
    ! [A_30185,B_30186] :
      ( k1_relat_1('#skF_9'(A_30185,B_30186)) != '#skF_11'
      | '#skF_1'(k1_tarski(B_30186),'#skF_10') = B_30186
      | k1_xboole_0 = A_30185 ) ),
    inference(resolution,[status(thm)],[c_68,c_30039])).

tff(c_48305,plain,(
    ! [A_45,B_49] :
      ( A_45 != '#skF_11'
      | '#skF_1'(k1_tarski(B_49),'#skF_10') = B_49
      | k1_xboole_0 = A_45
      | k1_xboole_0 = A_45 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_48254])).

tff(c_67793,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_48305])).

tff(c_46,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_44,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_148,plain,(
    ! [C_73] :
      ( ~ r1_tarski(k2_relat_1(C_73),'#skF_10')
      | k1_relat_1(C_73) != '#skF_11'
      | ~ v1_funct_1(C_73)
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_154,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_10')
    | k1_relat_1(k1_xboole_0) != '#skF_11'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_148])).

tff(c_158,plain,
    ( k1_xboole_0 != '#skF_11'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8,c_154])).

tff(c_165,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_52,plain,(
    ! [A_37] : k1_relat_1(k6_relat_1(A_37)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_42,plain,(
    ! [A_35] : v1_relat_1(k6_relat_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_166,plain,(
    ! [A_76] :
      ( k1_relat_1(A_76) != k1_xboole_0
      | k1_xboole_0 = A_76
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_175,plain,(
    ! [A_35] :
      ( k1_relat_1(k6_relat_1(A_35)) != k1_xboole_0
      | k6_relat_1(A_35) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_166])).

tff(c_182,plain,(
    ! [A_77] :
      ( k1_xboole_0 != A_77
      | k6_relat_1(A_77) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_175])).

tff(c_193,plain,(
    ! [A_77] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_77 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_42])).

tff(c_200,plain,(
    ! [A_77] : k1_xboole_0 != A_77 ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_193])).

tff(c_26,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_26])).

tff(c_222,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != '#skF_11' ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_224,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_68235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67793,c_224])).

tff(c_68238,plain,(
    ! [B_34092] : '#skF_1'(k1_tarski(B_34092),'#skF_10') = B_34092 ),
    inference(splitRight,[status(thm)],[c_48305])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_68289,plain,(
    ! [B_34093] :
      ( ~ r2_hidden(B_34093,'#skF_10')
      | r1_tarski(k1_tarski(B_34093),'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68238,c_4])).

tff(c_68701,plain,(
    ! [A_34104,B_34105] :
      ( k1_relat_1('#skF_9'(A_34104,B_34105)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_34104,B_34105))
      | ~ v1_relat_1('#skF_9'(A_34104,B_34105))
      | k1_xboole_0 = A_34104
      | ~ r2_hidden(B_34105,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_68289,c_358])).

tff(c_69460,plain,(
    ! [A_34128,B_34129] :
      ( k1_relat_1('#skF_9'(A_34128,B_34129)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_34128,B_34129))
      | ~ r2_hidden(B_34129,'#skF_10')
      | k1_xboole_0 = A_34128 ) ),
    inference(resolution,[status(thm)],[c_70,c_68701])).

tff(c_69539,plain,(
    ! [A_34133,B_34134] :
      ( k1_relat_1('#skF_9'(A_34133,B_34134)) != '#skF_11'
      | ~ r2_hidden(B_34134,'#skF_10')
      | k1_xboole_0 = A_34133 ) ),
    inference(resolution,[status(thm)],[c_68,c_69460])).

tff(c_69569,plain,(
    ! [A_45,B_49] :
      ( A_45 != '#skF_11'
      | ~ r2_hidden(B_49,'#skF_10')
      | k1_xboole_0 = A_45
      | k1_xboole_0 = A_45 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_69539])).

tff(c_69571,plain,(
    ! [B_34135] : ~ r2_hidden(B_34135,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_69569])).

tff(c_69681,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_24203,c_69571])).

tff(c_69783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_69681])).

tff(c_70152,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_69569])).

tff(c_70603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70152,c_224])).

tff(c_70605,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_70604,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_70606,plain,(
    ~ v1_funct_1('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70605,c_70604])).

tff(c_62,plain,(
    ! [A_38,B_39] : v1_relat_1('#skF_8'(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_50,plain,(
    ! [A_36] :
      ( k1_relat_1(A_36) != k1_xboole_0
      | k1_xboole_0 = A_36
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_70714,plain,(
    ! [A_34150] :
      ( k1_relat_1(A_34150) != '#skF_11'
      | A_34150 = '#skF_11'
      | ~ v1_relat_1(A_34150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70605,c_70605,c_50])).

tff(c_70723,plain,(
    ! [A_38,B_39] :
      ( k1_relat_1('#skF_8'(A_38,B_39)) != '#skF_11'
      | '#skF_8'(A_38,B_39) = '#skF_11' ) ),
    inference(resolution,[status(thm)],[c_62,c_70714])).

tff(c_70737,plain,(
    ! [A_34151,B_34152] :
      ( A_34151 != '#skF_11'
      | '#skF_8'(A_34151,B_34152) = '#skF_11' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_70723])).

tff(c_60,plain,(
    ! [A_38,B_39] : v1_funct_1('#skF_8'(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_70747,plain,(
    ! [A_34151] :
      ( v1_funct_1('#skF_11')
      | A_34151 != '#skF_11' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70737,c_60])).

tff(c_70754,plain,(
    ! [A_34151] : A_34151 != '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_70606,c_70747])).

tff(c_70613,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70605,c_70605,c_24])).

tff(c_70779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70754,c_70613])).

tff(c_70781,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_70780,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_70790,plain,(
    '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70781,c_70780])).

tff(c_70785,plain,(
    k1_relat_1('#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70780,c_70780,c_46])).

tff(c_70813,plain,(
    k1_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70790,c_70790,c_70785])).

tff(c_70783,plain,(
    ! [A_6] : r1_tarski('#skF_11',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70780,c_8])).

tff(c_70811,plain,(
    ! [A_6] : r1_tarski('#skF_10',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70790,c_70783])).

tff(c_70784,plain,(
    k2_relat_1('#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70780,c_70780,c_44])).

tff(c_70806,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70790,c_70790,c_70784])).

tff(c_70867,plain,(
    ! [C_34164] :
      ( ~ r1_tarski(k2_relat_1(C_34164),'#skF_10')
      | k1_relat_1(C_34164) != '#skF_10'
      | ~ v1_funct_1(C_34164)
      | ~ v1_relat_1(C_34164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70790,c_72])).

tff(c_70870,plain,
    ( ~ r1_tarski('#skF_10','#skF_10')
    | k1_relat_1('#skF_10') != '#skF_10'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_70806,c_70867])).

tff(c_70875,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70813,c_70811,c_70870])).

tff(c_70879,plain,(
    ~ v1_relat_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_70875])).

tff(c_70902,plain,(
    ! [A_34174] :
      ( k1_relat_1(A_34174) != '#skF_10'
      | A_34174 = '#skF_10'
      | ~ v1_relat_1(A_34174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70781,c_70781,c_50])).

tff(c_70911,plain,(
    ! [A_35] :
      ( k1_relat_1(k6_relat_1(A_35)) != '#skF_10'
      | k6_relat_1(A_35) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_42,c_70902])).

tff(c_70921,plain,(
    ! [A_34176] :
      ( A_34176 != '#skF_10'
      | k6_relat_1(A_34176) = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_70911])).

tff(c_70935,plain,(
    ! [A_34176] :
      ( v1_relat_1('#skF_10')
      | A_34176 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70921,c_42])).

tff(c_70942,plain,(
    ! [A_34176] : A_34176 != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_70879,c_70935])).

tff(c_70835,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_10',B_13) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70781,c_70781,c_26])).

tff(c_70955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70942,c_70835])).

tff(c_70956,plain,(
    ~ v1_funct_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_70875])).

tff(c_70980,plain,(
    ! [A_34185] :
      ( k1_relat_1(A_34185) != '#skF_10'
      | A_34185 = '#skF_10'
      | ~ v1_relat_1(A_34185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70781,c_70781,c_50])).

tff(c_70989,plain,(
    ! [A_38,B_39] :
      ( k1_relat_1('#skF_8'(A_38,B_39)) != '#skF_10'
      | '#skF_8'(A_38,B_39) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_62,c_70980])).

tff(c_71030,plain,(
    ! [A_34188,B_34189] :
      ( A_34188 != '#skF_10'
      | '#skF_8'(A_34188,B_34189) = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_70989])).

tff(c_71040,plain,(
    ! [A_34188] :
      ( v1_funct_1('#skF_10')
      | A_34188 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71030,c_60])).

tff(c_71047,plain,(
    ! [A_34188] : A_34188 != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_70956,c_71040])).

tff(c_71061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71047,c_70835])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:02:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.51/11.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.51/11.91  
% 20.51/11.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.51/11.91  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_8 > #skF_7 > #skF_2 > #skF_1 > #skF_9 > #skF_5 > #skF_4
% 20.51/11.91  
% 20.51/11.91  %Foreground sorts:
% 20.51/11.91  
% 20.51/11.91  
% 20.51/11.91  %Background operators:
% 20.51/11.91  
% 20.51/11.91  
% 20.51/11.91  %Foreground operators:
% 20.51/11.91  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 20.51/11.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 20.51/11.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.51/11.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.51/11.91  tff('#skF_11', type, '#skF_11': $i).
% 20.51/11.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 20.51/11.91  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 20.51/11.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.51/11.91  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 20.51/11.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.51/11.91  tff('#skF_10', type, '#skF_10': $i).
% 20.51/11.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 20.51/11.91  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 20.51/11.91  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 20.51/11.91  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 20.51/11.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.51/11.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 20.51/11.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 20.51/11.91  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 20.51/11.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.51/11.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 20.51/11.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 20.51/11.91  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 20.51/11.91  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 20.51/11.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 20.51/11.91  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 20.51/11.91  
% 20.78/11.93  tff(f_118, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 20.78/11.93  tff(f_87, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 20.78/11.93  tff(f_58, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 20.78/11.93  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 20.78/11.93  tff(f_50, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 20.78/11.93  tff(f_100, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 20.78/11.93  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 20.78/11.93  tff(f_41, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 20.78/11.93  tff(f_63, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 20.78/11.93  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 20.78/11.93  tff(f_75, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 20.78/11.93  tff(f_60, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 20.78/11.93  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 20.78/11.93  tff(c_74, plain, (k1_xboole_0='#skF_11' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_118])).
% 20.78/11.93  tff(c_104, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_74])).
% 20.78/11.93  tff(c_58, plain, (![A_38, B_39]: (k1_relat_1('#skF_8'(A_38, B_39))=A_38)), inference(cnfTransformation, [status(thm)], [f_87])).
% 20.78/11.93  tff(c_3611, plain, (![A_6415, B_6416]: (r2_hidden(k4_tarski('#skF_4'(A_6415, B_6416), '#skF_5'(A_6415, B_6416)), A_6415) | r2_hidden('#skF_6'(A_6415, B_6416), B_6416) | k1_relat_1(A_6415)=B_6416)), inference(cnfTransformation, [status(thm)], [f_58])).
% 20.78/11.93  tff(c_32, plain, (![C_31, A_16, D_34]: (r2_hidden(C_31, k1_relat_1(A_16)) | ~r2_hidden(k4_tarski(C_31, D_34), A_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 20.78/11.93  tff(c_7899, plain, (![A_16181, B_16182]: (r2_hidden('#skF_4'(A_16181, B_16182), k1_relat_1(A_16181)) | r2_hidden('#skF_6'(A_16181, B_16182), B_16182) | k1_relat_1(A_16181)=B_16182)), inference(resolution, [status(thm)], [c_3611, c_32])).
% 20.78/11.93  tff(c_7935, plain, (![A_38, B_39, B_16182]: (r2_hidden('#skF_4'('#skF_8'(A_38, B_39), B_16182), A_38) | r2_hidden('#skF_6'('#skF_8'(A_38, B_39), B_16182), B_16182) | k1_relat_1('#skF_8'(A_38, B_39))=B_16182)), inference(superposition, [status(thm), theory('equality')], [c_58, c_7899])).
% 20.78/11.93  tff(c_23964, plain, (![A_24432, B_24433, B_24434]: (r2_hidden('#skF_4'('#skF_8'(A_24432, B_24433), B_24434), A_24432) | r2_hidden('#skF_6'('#skF_8'(A_24432, B_24433), B_24434), B_24434) | B_24434=A_24432)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_7935])).
% 20.78/11.93  tff(c_24, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 20.78/11.93  tff(c_138, plain, (![A_66, B_67]: (~r2_hidden(A_66, k2_zfmisc_1(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 20.78/11.93  tff(c_144, plain, (![A_12]: (~r2_hidden(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_138])).
% 20.78/11.93  tff(c_24203, plain, (![A_24432, B_24433]: (r2_hidden('#skF_4'('#skF_8'(A_24432, B_24433), k1_xboole_0), A_24432) | k1_xboole_0=A_24432)), inference(resolution, [status(thm)], [c_23964, c_144])).
% 20.78/11.93  tff(c_66, plain, (![A_45, B_49]: (k1_relat_1('#skF_9'(A_45, B_49))=A_45 | k1_xboole_0=A_45)), inference(cnfTransformation, [status(thm)], [f_100])).
% 20.78/11.93  tff(c_68, plain, (![A_45, B_49]: (v1_funct_1('#skF_9'(A_45, B_49)) | k1_xboole_0=A_45)), inference(cnfTransformation, [status(thm)], [f_100])).
% 20.78/11.93  tff(c_70, plain, (![A_45, B_49]: (v1_relat_1('#skF_9'(A_45, B_49)) | k1_xboole_0=A_45)), inference(cnfTransformation, [status(thm)], [f_100])).
% 20.78/11.93  tff(c_375, plain, (![A_95, B_96]: (r2_hidden('#skF_1'(A_95, B_96), A_95) | r1_tarski(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.78/11.93  tff(c_10, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 20.78/11.93  tff(c_447, plain, (![A_117, B_118]: ('#skF_1'(k1_tarski(A_117), B_118)=A_117 | r1_tarski(k1_tarski(A_117), B_118))), inference(resolution, [status(thm)], [c_375, c_10])).
% 20.78/11.93  tff(c_352, plain, (![A_91, B_92]: (k2_relat_1('#skF_9'(A_91, B_92))=k1_tarski(B_92) | k1_xboole_0=A_91)), inference(cnfTransformation, [status(thm)], [f_100])).
% 20.78/11.93  tff(c_72, plain, (![C_52]: (~r1_tarski(k2_relat_1(C_52), '#skF_10') | k1_relat_1(C_52)!='#skF_11' | ~v1_funct_1(C_52) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_118])).
% 20.78/11.93  tff(c_358, plain, (![B_92, A_91]: (~r1_tarski(k1_tarski(B_92), '#skF_10') | k1_relat_1('#skF_9'(A_91, B_92))!='#skF_11' | ~v1_funct_1('#skF_9'(A_91, B_92)) | ~v1_relat_1('#skF_9'(A_91, B_92)) | k1_xboole_0=A_91)), inference(superposition, [status(thm), theory('equality')], [c_352, c_72])).
% 20.78/11.93  tff(c_477, plain, (![A_121, A_122]: (k1_relat_1('#skF_9'(A_121, A_122))!='#skF_11' | ~v1_funct_1('#skF_9'(A_121, A_122)) | ~v1_relat_1('#skF_9'(A_121, A_122)) | k1_xboole_0=A_121 | '#skF_1'(k1_tarski(A_122), '#skF_10')=A_122)), inference(resolution, [status(thm)], [c_447, c_358])).
% 20.78/11.93  tff(c_30039, plain, (![A_26224, B_26225]: (k1_relat_1('#skF_9'(A_26224, B_26225))!='#skF_11' | ~v1_funct_1('#skF_9'(A_26224, B_26225)) | '#skF_1'(k1_tarski(B_26225), '#skF_10')=B_26225 | k1_xboole_0=A_26224)), inference(resolution, [status(thm)], [c_70, c_477])).
% 20.78/11.93  tff(c_48254, plain, (![A_30185, B_30186]: (k1_relat_1('#skF_9'(A_30185, B_30186))!='#skF_11' | '#skF_1'(k1_tarski(B_30186), '#skF_10')=B_30186 | k1_xboole_0=A_30185)), inference(resolution, [status(thm)], [c_68, c_30039])).
% 20.78/11.93  tff(c_48305, plain, (![A_45, B_49]: (A_45!='#skF_11' | '#skF_1'(k1_tarski(B_49), '#skF_10')=B_49 | k1_xboole_0=A_45 | k1_xboole_0=A_45)), inference(superposition, [status(thm), theory('equality')], [c_66, c_48254])).
% 20.78/11.93  tff(c_67793, plain, (k1_xboole_0='#skF_11'), inference(splitLeft, [status(thm)], [c_48305])).
% 20.78/11.93  tff(c_46, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 20.78/11.93  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 20.78/11.93  tff(c_44, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 20.78/11.93  tff(c_148, plain, (![C_73]: (~r1_tarski(k2_relat_1(C_73), '#skF_10') | k1_relat_1(C_73)!='#skF_11' | ~v1_funct_1(C_73) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_118])).
% 20.78/11.93  tff(c_154, plain, (~r1_tarski(k1_xboole_0, '#skF_10') | k1_relat_1(k1_xboole_0)!='#skF_11' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_148])).
% 20.78/11.93  tff(c_158, plain, (k1_xboole_0!='#skF_11' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8, c_154])).
% 20.78/11.93  tff(c_165, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_158])).
% 20.78/11.93  tff(c_52, plain, (![A_37]: (k1_relat_1(k6_relat_1(A_37))=A_37)), inference(cnfTransformation, [status(thm)], [f_75])).
% 20.78/11.93  tff(c_42, plain, (![A_35]: (v1_relat_1(k6_relat_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 20.78/11.93  tff(c_166, plain, (![A_76]: (k1_relat_1(A_76)!=k1_xboole_0 | k1_xboole_0=A_76 | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_71])).
% 20.78/11.93  tff(c_175, plain, (![A_35]: (k1_relat_1(k6_relat_1(A_35))!=k1_xboole_0 | k6_relat_1(A_35)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_166])).
% 20.78/11.93  tff(c_182, plain, (![A_77]: (k1_xboole_0!=A_77 | k6_relat_1(A_77)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_175])).
% 20.78/11.93  tff(c_193, plain, (![A_77]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_77)), inference(superposition, [status(thm), theory('equality')], [c_182, c_42])).
% 20.78/11.93  tff(c_200, plain, (![A_77]: (k1_xboole_0!=A_77)), inference(negUnitSimplification, [status(thm)], [c_165, c_193])).
% 20.78/11.93  tff(c_26, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 20.78/11.93  tff(c_221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_200, c_26])).
% 20.78/11.93  tff(c_222, plain, (~v1_funct_1(k1_xboole_0) | k1_xboole_0!='#skF_11'), inference(splitRight, [status(thm)], [c_158])).
% 20.78/11.93  tff(c_224, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_222])).
% 20.78/11.93  tff(c_68235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67793, c_224])).
% 20.78/11.93  tff(c_68238, plain, (![B_34092]: ('#skF_1'(k1_tarski(B_34092), '#skF_10')=B_34092)), inference(splitRight, [status(thm)], [c_48305])).
% 20.78/11.93  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.78/11.93  tff(c_68289, plain, (![B_34093]: (~r2_hidden(B_34093, '#skF_10') | r1_tarski(k1_tarski(B_34093), '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_68238, c_4])).
% 20.78/11.93  tff(c_68701, plain, (![A_34104, B_34105]: (k1_relat_1('#skF_9'(A_34104, B_34105))!='#skF_11' | ~v1_funct_1('#skF_9'(A_34104, B_34105)) | ~v1_relat_1('#skF_9'(A_34104, B_34105)) | k1_xboole_0=A_34104 | ~r2_hidden(B_34105, '#skF_10'))), inference(resolution, [status(thm)], [c_68289, c_358])).
% 20.78/11.93  tff(c_69460, plain, (![A_34128, B_34129]: (k1_relat_1('#skF_9'(A_34128, B_34129))!='#skF_11' | ~v1_funct_1('#skF_9'(A_34128, B_34129)) | ~r2_hidden(B_34129, '#skF_10') | k1_xboole_0=A_34128)), inference(resolution, [status(thm)], [c_70, c_68701])).
% 20.78/11.93  tff(c_69539, plain, (![A_34133, B_34134]: (k1_relat_1('#skF_9'(A_34133, B_34134))!='#skF_11' | ~r2_hidden(B_34134, '#skF_10') | k1_xboole_0=A_34133)), inference(resolution, [status(thm)], [c_68, c_69460])).
% 20.78/11.93  tff(c_69569, plain, (![A_45, B_49]: (A_45!='#skF_11' | ~r2_hidden(B_49, '#skF_10') | k1_xboole_0=A_45 | k1_xboole_0=A_45)), inference(superposition, [status(thm), theory('equality')], [c_66, c_69539])).
% 20.78/11.93  tff(c_69571, plain, (![B_34135]: (~r2_hidden(B_34135, '#skF_10'))), inference(splitLeft, [status(thm)], [c_69569])).
% 20.78/11.93  tff(c_69681, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_24203, c_69571])).
% 20.78/11.93  tff(c_69783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_69681])).
% 20.78/11.93  tff(c_70152, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_69569])).
% 20.78/11.93  tff(c_70603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70152, c_224])).
% 20.78/11.93  tff(c_70605, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_222])).
% 20.78/11.93  tff(c_70604, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_222])).
% 20.78/11.93  tff(c_70606, plain, (~v1_funct_1('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_70605, c_70604])).
% 20.78/11.93  tff(c_62, plain, (![A_38, B_39]: (v1_relat_1('#skF_8'(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 20.78/11.93  tff(c_50, plain, (![A_36]: (k1_relat_1(A_36)!=k1_xboole_0 | k1_xboole_0=A_36 | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_71])).
% 20.78/11.93  tff(c_70714, plain, (![A_34150]: (k1_relat_1(A_34150)!='#skF_11' | A_34150='#skF_11' | ~v1_relat_1(A_34150))), inference(demodulation, [status(thm), theory('equality')], [c_70605, c_70605, c_50])).
% 20.78/11.93  tff(c_70723, plain, (![A_38, B_39]: (k1_relat_1('#skF_8'(A_38, B_39))!='#skF_11' | '#skF_8'(A_38, B_39)='#skF_11')), inference(resolution, [status(thm)], [c_62, c_70714])).
% 20.78/11.93  tff(c_70737, plain, (![A_34151, B_34152]: (A_34151!='#skF_11' | '#skF_8'(A_34151, B_34152)='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_70723])).
% 20.78/11.93  tff(c_60, plain, (![A_38, B_39]: (v1_funct_1('#skF_8'(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 20.78/11.93  tff(c_70747, plain, (![A_34151]: (v1_funct_1('#skF_11') | A_34151!='#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_70737, c_60])).
% 20.78/11.93  tff(c_70754, plain, (![A_34151]: (A_34151!='#skF_11')), inference(negUnitSimplification, [status(thm)], [c_70606, c_70747])).
% 20.78/11.93  tff(c_70613, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_11')='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_70605, c_70605, c_24])).
% 20.78/11.93  tff(c_70779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70754, c_70613])).
% 20.78/11.93  tff(c_70781, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_74])).
% 20.78/11.93  tff(c_70780, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_74])).
% 20.78/11.93  tff(c_70790, plain, ('#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_70781, c_70780])).
% 20.78/11.93  tff(c_70785, plain, (k1_relat_1('#skF_11')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_70780, c_70780, c_46])).
% 20.78/11.93  tff(c_70813, plain, (k1_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_70790, c_70790, c_70785])).
% 20.78/11.93  tff(c_70783, plain, (![A_6]: (r1_tarski('#skF_11', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_70780, c_8])).
% 20.78/11.93  tff(c_70811, plain, (![A_6]: (r1_tarski('#skF_10', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_70790, c_70783])).
% 20.78/11.93  tff(c_70784, plain, (k2_relat_1('#skF_11')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_70780, c_70780, c_44])).
% 20.78/11.93  tff(c_70806, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_70790, c_70790, c_70784])).
% 20.78/11.93  tff(c_70867, plain, (![C_34164]: (~r1_tarski(k2_relat_1(C_34164), '#skF_10') | k1_relat_1(C_34164)!='#skF_10' | ~v1_funct_1(C_34164) | ~v1_relat_1(C_34164))), inference(demodulation, [status(thm), theory('equality')], [c_70790, c_72])).
% 20.78/11.93  tff(c_70870, plain, (~r1_tarski('#skF_10', '#skF_10') | k1_relat_1('#skF_10')!='#skF_10' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_70806, c_70867])).
% 20.78/11.93  tff(c_70875, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_70813, c_70811, c_70870])).
% 20.78/11.93  tff(c_70879, plain, (~v1_relat_1('#skF_10')), inference(splitLeft, [status(thm)], [c_70875])).
% 20.78/11.93  tff(c_70902, plain, (![A_34174]: (k1_relat_1(A_34174)!='#skF_10' | A_34174='#skF_10' | ~v1_relat_1(A_34174))), inference(demodulation, [status(thm), theory('equality')], [c_70781, c_70781, c_50])).
% 20.78/11.93  tff(c_70911, plain, (![A_35]: (k1_relat_1(k6_relat_1(A_35))!='#skF_10' | k6_relat_1(A_35)='#skF_10')), inference(resolution, [status(thm)], [c_42, c_70902])).
% 20.78/11.93  tff(c_70921, plain, (![A_34176]: (A_34176!='#skF_10' | k6_relat_1(A_34176)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_70911])).
% 20.78/11.93  tff(c_70935, plain, (![A_34176]: (v1_relat_1('#skF_10') | A_34176!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_70921, c_42])).
% 20.78/11.93  tff(c_70942, plain, (![A_34176]: (A_34176!='#skF_10')), inference(negUnitSimplification, [status(thm)], [c_70879, c_70935])).
% 20.78/11.93  tff(c_70835, plain, (![B_13]: (k2_zfmisc_1('#skF_10', B_13)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_70781, c_70781, c_26])).
% 20.78/11.93  tff(c_70955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70942, c_70835])).
% 20.78/11.93  tff(c_70956, plain, (~v1_funct_1('#skF_10')), inference(splitRight, [status(thm)], [c_70875])).
% 20.78/11.93  tff(c_70980, plain, (![A_34185]: (k1_relat_1(A_34185)!='#skF_10' | A_34185='#skF_10' | ~v1_relat_1(A_34185))), inference(demodulation, [status(thm), theory('equality')], [c_70781, c_70781, c_50])).
% 20.78/11.93  tff(c_70989, plain, (![A_38, B_39]: (k1_relat_1('#skF_8'(A_38, B_39))!='#skF_10' | '#skF_8'(A_38, B_39)='#skF_10')), inference(resolution, [status(thm)], [c_62, c_70980])).
% 20.78/11.93  tff(c_71030, plain, (![A_34188, B_34189]: (A_34188!='#skF_10' | '#skF_8'(A_34188, B_34189)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_70989])).
% 20.78/11.93  tff(c_71040, plain, (![A_34188]: (v1_funct_1('#skF_10') | A_34188!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_71030, c_60])).
% 20.78/11.93  tff(c_71047, plain, (![A_34188]: (A_34188!='#skF_10')), inference(negUnitSimplification, [status(thm)], [c_70956, c_71040])).
% 20.78/11.93  tff(c_71061, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71047, c_70835])).
% 20.78/11.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.78/11.93  
% 20.78/11.93  Inference rules
% 20.78/11.93  ----------------------
% 20.78/11.93  #Ref     : 26
% 20.78/11.93  #Sup     : 17774
% 20.78/11.93  #Fact    : 0
% 20.78/11.93  #Define  : 0
% 20.78/11.93  #Split   : 16
% 20.78/11.93  #Chain   : 0
% 20.78/11.93  #Close   : 0
% 20.78/11.93  
% 20.78/11.93  Ordering : KBO
% 20.78/11.93  
% 20.78/11.93  Simplification rules
% 20.78/11.93  ----------------------
% 20.78/11.93  #Subsume      : 9454
% 20.78/11.93  #Demod        : 6372
% 20.78/11.93  #Tautology    : 3151
% 20.78/11.93  #SimpNegUnit  : 382
% 20.78/11.93  #BackRed      : 947
% 20.78/11.93  
% 20.78/11.93  #Partial instantiations: 21337
% 20.78/11.93  #Strategies tried      : 1
% 20.78/11.93  
% 20.78/11.93  Timing (in seconds)
% 20.78/11.93  ----------------------
% 20.78/11.94  Preprocessing        : 0.32
% 20.78/11.94  Parsing              : 0.16
% 20.78/11.94  CNF conversion       : 0.03
% 20.78/11.94  Main loop            : 10.78
% 20.78/11.94  Inferencing          : 1.69
% 20.78/11.94  Reduction            : 2.78
% 20.78/11.94  Demodulation         : 1.94
% 20.78/11.94  BG Simplification    : 0.15
% 20.78/11.94  Subsumption          : 5.66
% 20.78/11.94  Abstraction          : 0.25
% 20.78/11.94  MUC search           : 0.00
% 20.78/11.94  Cooper               : 0.00
% 20.78/11.94  Total                : 11.14
% 20.78/11.94  Index Insertion      : 0.00
% 20.78/11.94  Index Deletion       : 0.00
% 20.78/11.94  Index Matching       : 0.00
% 20.78/11.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
