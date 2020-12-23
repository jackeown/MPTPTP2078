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
% DateTime   : Thu Dec  3 10:02:55 EST 2020

% Result     : Theorem 6.99s
% Output     : CNFRefutation 7.05s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 310 expanded)
%              Number of leaves         :   32 ( 116 expanded)
%              Depth                    :   21
%              Number of atoms          :  202 ( 732 expanded)
%              Number of equality atoms :  112 ( 431 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_1 > #skF_5 > #skF_4

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_70,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_119,plain,(
    ! [A_79] :
      ( k2_relat_1(A_79) != k1_xboole_0
      | k1_xboole_0 = A_79
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_123,plain,
    ( k2_relat_1('#skF_9') != k1_xboole_0
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_70,c_119])).

tff(c_130,plain,(
    k2_relat_1('#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_36,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_3'(A_18,B_19),A_18)
      | k1_xboole_0 = A_18
      | k1_tarski(B_19) = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_68,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_50,plain,(
    ! [A_23,C_59] :
      ( r2_hidden('#skF_7'(A_23,k2_relat_1(A_23),C_59),k1_relat_1(A_23))
      | ~ r2_hidden(C_59,k2_relat_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_46,plain,(
    ! [A_23,D_62] :
      ( r2_hidden(k1_funct_1(A_23,D_62),k2_relat_1(A_23))
      | ~ r2_hidden(D_62,k1_relat_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1744,plain,(
    ! [A_3064,C_3065] :
      ( r2_hidden('#skF_7'(A_3064,k2_relat_1(A_3064),C_3065),k1_relat_1(A_3064))
      | ~ r2_hidden(C_3065,k2_relat_1(A_3064))
      | ~ v1_funct_1(A_3064)
      | ~ v1_relat_1(A_3064) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_66,plain,(
    k1_tarski('#skF_8') = k1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_26,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_163,plain,(
    ! [E_95,C_96,B_97,A_98] :
      ( E_95 = C_96
      | E_95 = B_97
      | E_95 = A_98
      | ~ r2_hidden(E_95,k1_enumset1(A_98,B_97,C_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_187,plain,(
    ! [E_99,B_100,A_101] :
      ( E_99 = B_100
      | E_99 = A_101
      | E_99 = A_101
      | ~ r2_hidden(E_99,k2_tarski(A_101,B_100)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_163])).

tff(c_206,plain,(
    ! [E_102,A_103] :
      ( E_102 = A_103
      | E_102 = A_103
      | E_102 = A_103
      | ~ r2_hidden(E_102,k1_tarski(A_103)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_187])).

tff(c_216,plain,(
    ! [E_102] :
      ( E_102 = '#skF_8'
      | E_102 = '#skF_8'
      | E_102 = '#skF_8'
      | ~ r2_hidden(E_102,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_206])).

tff(c_1751,plain,(
    ! [C_3065] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_3065) = '#skF_8'
      | ~ r2_hidden(C_3065,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1744,c_216])).

tff(c_2001,plain,(
    ! [C_3219] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_3219) = '#skF_8'
      | ~ r2_hidden(C_3219,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1751])).

tff(c_2005,plain,(
    ! [D_62] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_62)) = '#skF_8'
      | ~ r2_hidden(D_62,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_46,c_2001])).

tff(c_2012,plain,(
    ! [D_62] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_62)) = '#skF_8'
      | ~ r2_hidden(D_62,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_2005])).

tff(c_3232,plain,(
    ! [A_5431,C_5432] :
      ( k1_funct_1(A_5431,'#skF_7'(A_5431,k2_relat_1(A_5431),C_5432)) = C_5432
      | ~ r2_hidden(C_5432,k2_relat_1(A_5431))
      | ~ v1_funct_1(A_5431)
      | ~ v1_relat_1(A_5431) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3260,plain,(
    ! [D_62] :
      ( k1_funct_1('#skF_9',D_62) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_62),k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_62,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2012,c_3232])).

tff(c_7265,plain,(
    ! [D_11227] :
      ( k1_funct_1('#skF_9',D_11227) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_11227),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_11227,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_3260])).

tff(c_7288,plain,(
    ! [D_62] :
      ( k1_funct_1('#skF_9',D_62) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(D_62,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_46,c_7265])).

tff(c_7294,plain,(
    ! [D_11418] :
      ( k1_funct_1('#skF_9',D_11418) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(D_11418,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_7288])).

tff(c_7302,plain,(
    ! [C_59] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_59)) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(C_59,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_50,c_7294])).

tff(c_8506,plain,(
    ! [C_13908] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_13908)) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(C_13908,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_7302])).

tff(c_48,plain,(
    ! [A_23,C_59] :
      ( k1_funct_1(A_23,'#skF_7'(A_23,k2_relat_1(A_23),C_59)) = C_59
      | ~ r2_hidden(C_59,k2_relat_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8536,plain,(
    ! [C_13908] :
      ( k1_funct_1('#skF_9','#skF_8') = C_13908
      | ~ r2_hidden(C_13908,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_13908,k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8506,c_48])).

tff(c_8614,plain,(
    ! [C_14099] :
      ( k1_funct_1('#skF_9','#skF_8') = C_14099
      | ~ r2_hidden(C_14099,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_8536])).

tff(c_8629,plain,(
    ! [B_19] :
      ( '#skF_3'(k2_relat_1('#skF_9'),B_19) = k1_funct_1('#skF_9','#skF_8')
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_19) ) ),
    inference(resolution,[status(thm)],[c_36,c_8614])).

tff(c_8638,plain,(
    ! [B_14290] :
      ( '#skF_3'(k2_relat_1('#skF_9'),B_14290) = k1_funct_1('#skF_9','#skF_8')
      | k2_relat_1('#skF_9') = k1_tarski(B_14290) ) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_8629])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( '#skF_3'(A_18,B_19) != B_19
      | k1_xboole_0 = A_18
      | k1_tarski(B_19) = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8649,plain,(
    ! [B_14290] :
      ( k1_funct_1('#skF_9','#skF_8') != B_14290
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_14290)
      | k2_relat_1('#skF_9') = k1_tarski(B_14290) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8638,c_34])).

tff(c_8948,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) = k2_relat_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_8649])).

tff(c_64,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) != k2_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_8952,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8948,c_64])).

tff(c_8953,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_87,plain,(
    ! [A_73] :
      ( k1_relat_1(A_73) != k1_xboole_0
      | k1_xboole_0 = A_73
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_91,plain,
    ( k1_relat_1('#skF_9') != k1_xboole_0
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_70,c_87])).

tff(c_92,plain,(
    k1_relat_1('#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_8956,plain,(
    k1_relat_1('#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8953,c_92])).

tff(c_8954,plain,(
    k2_relat_1('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_8962,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8953,c_8954])).

tff(c_42,plain,(
    ! [A_22] :
      ( k1_relat_1(A_22) = k1_xboole_0
      | k2_relat_1(A_22) != k1_xboole_0
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8989,plain,(
    ! [A_14867] :
      ( k1_relat_1(A_14867) = '#skF_9'
      | k2_relat_1(A_14867) != '#skF_9'
      | ~ v1_relat_1(A_14867) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8953,c_8953,c_42])).

tff(c_8992,plain,
    ( k1_relat_1('#skF_9') = '#skF_9'
    | k2_relat_1('#skF_9') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_70,c_8989])).

tff(c_8995,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8962,c_8992])).

tff(c_8997,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8956,c_8995])).

tff(c_8998,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_8999,plain,(
    k1_relat_1('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_9005,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8998,c_8999])).

tff(c_9006,plain,(
    k1_tarski('#skF_8') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9005,c_66])).

tff(c_9022,plain,(
    ! [A_14869,B_14870] : k1_enumset1(A_14869,A_14869,B_14870) = k2_tarski(A_14869,B_14870) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [E_7,A_1,C_3] : r2_hidden(E_7,k1_enumset1(A_1,E_7,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_9040,plain,(
    ! [A_14871,B_14872] : r2_hidden(A_14871,k2_tarski(A_14871,B_14872)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9022,c_6])).

tff(c_9044,plain,(
    ! [A_14873] : r2_hidden(A_14873,k1_tarski(A_14873)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_9040])).

tff(c_9047,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_9006,c_9044])).

tff(c_44,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) = k1_xboole_0
      | k1_relat_1(A_22) != k1_xboole_0
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_9070,plain,(
    ! [A_14878] :
      ( k2_relat_1(A_14878) = '#skF_9'
      | k1_relat_1(A_14878) != '#skF_9'
      | ~ v1_relat_1(A_14878) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8998,c_8998,c_44])).

tff(c_9073,plain,
    ( k2_relat_1('#skF_9') = '#skF_9'
    | k1_relat_1('#skF_9') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_70,c_9070])).

tff(c_9076,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9005,c_9073])).

tff(c_9173,plain,(
    ! [A_14900,D_14901] :
      ( r2_hidden(k1_funct_1(A_14900,D_14901),k2_relat_1(A_14900))
      | ~ r2_hidden(D_14901,k1_relat_1(A_14900))
      | ~ v1_funct_1(A_14900)
      | ~ v1_relat_1(A_14900) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_9176,plain,(
    ! [D_14901] :
      ( r2_hidden(k1_funct_1('#skF_9',D_14901),'#skF_9')
      | ~ r2_hidden(D_14901,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9076,c_9173])).

tff(c_9179,plain,(
    ! [D_14902] :
      ( r2_hidden(k1_funct_1('#skF_9',D_14902),'#skF_9')
      | ~ r2_hidden(D_14902,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_9005,c_9176])).

tff(c_9104,plain,(
    ! [E_14890,C_14891,B_14892,A_14893] :
      ( E_14890 = C_14891
      | E_14890 = B_14892
      | E_14890 = A_14893
      | ~ r2_hidden(E_14890,k1_enumset1(A_14893,B_14892,C_14891)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_9128,plain,(
    ! [E_14894,B_14895,A_14896] :
      ( E_14894 = B_14895
      | E_14894 = A_14896
      | E_14894 = A_14896
      | ~ r2_hidden(E_14894,k2_tarski(A_14896,B_14895)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_9104])).

tff(c_9147,plain,(
    ! [E_14897,A_14898] :
      ( E_14897 = A_14898
      | E_14897 = A_14898
      | E_14897 = A_14898
      | ~ r2_hidden(E_14897,k1_tarski(A_14898)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_9128])).

tff(c_9157,plain,(
    ! [E_14897] :
      ( E_14897 = '#skF_8'
      | E_14897 = '#skF_8'
      | E_14897 = '#skF_8'
      | ~ r2_hidden(E_14897,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9006,c_9147])).

tff(c_9184,plain,(
    ! [D_14903] :
      ( k1_funct_1('#skF_9',D_14903) = '#skF_8'
      | ~ r2_hidden(D_14903,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_9179,c_9157])).

tff(c_9198,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_9047,c_9184])).

tff(c_9077,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9076,c_64])).

tff(c_9199,plain,(
    k1_tarski('#skF_8') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9198,c_9077])).

tff(c_9202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9006,c_9199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.99/2.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/2.37  
% 7.05/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/2.37  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 7.05/2.37  
% 7.05/2.37  %Foreground sorts:
% 7.05/2.37  
% 7.05/2.37  
% 7.05/2.37  %Background operators:
% 7.05/2.37  
% 7.05/2.37  
% 7.05/2.37  %Foreground operators:
% 7.05/2.37  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.05/2.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.05/2.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.05/2.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.05/2.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.05/2.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.05/2.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.05/2.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.05/2.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.05/2.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.05/2.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.05/2.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.05/2.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.05/2.37  tff('#skF_9', type, '#skF_9': $i).
% 7.05/2.37  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 7.05/2.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.05/2.37  tff('#skF_8', type, '#skF_8': $i).
% 7.05/2.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.05/2.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.05/2.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.05/2.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 7.05/2.37  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.05/2.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.05/2.37  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.05/2.37  
% 7.05/2.39  tff(f_100, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 7.05/2.39  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 7.05/2.39  tff(f_62, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 7.05/2.39  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 7.05/2.39  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.05/2.39  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.05/2.39  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 7.05/2.39  tff(f_76, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 7.05/2.39  tff(c_70, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.05/2.39  tff(c_119, plain, (![A_79]: (k2_relat_1(A_79)!=k1_xboole_0 | k1_xboole_0=A_79 | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.05/2.39  tff(c_123, plain, (k2_relat_1('#skF_9')!=k1_xboole_0 | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_70, c_119])).
% 7.05/2.39  tff(c_130, plain, (k2_relat_1('#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_123])).
% 7.05/2.39  tff(c_36, plain, (![A_18, B_19]: (r2_hidden('#skF_3'(A_18, B_19), A_18) | k1_xboole_0=A_18 | k1_tarski(B_19)=A_18)), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.05/2.39  tff(c_68, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.05/2.39  tff(c_50, plain, (![A_23, C_59]: (r2_hidden('#skF_7'(A_23, k2_relat_1(A_23), C_59), k1_relat_1(A_23)) | ~r2_hidden(C_59, k2_relat_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.05/2.39  tff(c_46, plain, (![A_23, D_62]: (r2_hidden(k1_funct_1(A_23, D_62), k2_relat_1(A_23)) | ~r2_hidden(D_62, k1_relat_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.05/2.39  tff(c_1744, plain, (![A_3064, C_3065]: (r2_hidden('#skF_7'(A_3064, k2_relat_1(A_3064), C_3065), k1_relat_1(A_3064)) | ~r2_hidden(C_3065, k2_relat_1(A_3064)) | ~v1_funct_1(A_3064) | ~v1_relat_1(A_3064))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.05/2.39  tff(c_66, plain, (k1_tarski('#skF_8')=k1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.05/2.39  tff(c_26, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.05/2.39  tff(c_28, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.05/2.39  tff(c_163, plain, (![E_95, C_96, B_97, A_98]: (E_95=C_96 | E_95=B_97 | E_95=A_98 | ~r2_hidden(E_95, k1_enumset1(A_98, B_97, C_96)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.05/2.39  tff(c_187, plain, (![E_99, B_100, A_101]: (E_99=B_100 | E_99=A_101 | E_99=A_101 | ~r2_hidden(E_99, k2_tarski(A_101, B_100)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_163])).
% 7.05/2.39  tff(c_206, plain, (![E_102, A_103]: (E_102=A_103 | E_102=A_103 | E_102=A_103 | ~r2_hidden(E_102, k1_tarski(A_103)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_187])).
% 7.05/2.39  tff(c_216, plain, (![E_102]: (E_102='#skF_8' | E_102='#skF_8' | E_102='#skF_8' | ~r2_hidden(E_102, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_66, c_206])).
% 7.05/2.39  tff(c_1751, plain, (![C_3065]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_3065)='#skF_8' | ~r2_hidden(C_3065, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1744, c_216])).
% 7.05/2.39  tff(c_2001, plain, (![C_3219]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_3219)='#skF_8' | ~r2_hidden(C_3219, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1751])).
% 7.05/2.39  tff(c_2005, plain, (![D_62]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_62))='#skF_8' | ~r2_hidden(D_62, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_46, c_2001])).
% 7.05/2.39  tff(c_2012, plain, (![D_62]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_62))='#skF_8' | ~r2_hidden(D_62, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_2005])).
% 7.05/2.39  tff(c_3232, plain, (![A_5431, C_5432]: (k1_funct_1(A_5431, '#skF_7'(A_5431, k2_relat_1(A_5431), C_5432))=C_5432 | ~r2_hidden(C_5432, k2_relat_1(A_5431)) | ~v1_funct_1(A_5431) | ~v1_relat_1(A_5431))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.05/2.39  tff(c_3260, plain, (![D_62]: (k1_funct_1('#skF_9', D_62)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', D_62), k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_62, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_2012, c_3232])).
% 7.05/2.39  tff(c_7265, plain, (![D_11227]: (k1_funct_1('#skF_9', D_11227)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', D_11227), k2_relat_1('#skF_9')) | ~r2_hidden(D_11227, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_3260])).
% 7.05/2.39  tff(c_7288, plain, (![D_62]: (k1_funct_1('#skF_9', D_62)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(D_62, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_46, c_7265])).
% 7.05/2.39  tff(c_7294, plain, (![D_11418]: (k1_funct_1('#skF_9', D_11418)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(D_11418, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_7288])).
% 7.05/2.39  tff(c_7302, plain, (![C_59]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_59))=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(C_59, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_50, c_7294])).
% 7.05/2.39  tff(c_8506, plain, (![C_13908]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_13908))=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(C_13908, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_7302])).
% 7.05/2.39  tff(c_48, plain, (![A_23, C_59]: (k1_funct_1(A_23, '#skF_7'(A_23, k2_relat_1(A_23), C_59))=C_59 | ~r2_hidden(C_59, k2_relat_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.05/2.39  tff(c_8536, plain, (![C_13908]: (k1_funct_1('#skF_9', '#skF_8')=C_13908 | ~r2_hidden(C_13908, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_13908, k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_8506, c_48])).
% 7.05/2.39  tff(c_8614, plain, (![C_14099]: (k1_funct_1('#skF_9', '#skF_8')=C_14099 | ~r2_hidden(C_14099, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_8536])).
% 7.05/2.39  tff(c_8629, plain, (![B_19]: ('#skF_3'(k2_relat_1('#skF_9'), B_19)=k1_funct_1('#skF_9', '#skF_8') | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_19))), inference(resolution, [status(thm)], [c_36, c_8614])).
% 7.05/2.39  tff(c_8638, plain, (![B_14290]: ('#skF_3'(k2_relat_1('#skF_9'), B_14290)=k1_funct_1('#skF_9', '#skF_8') | k2_relat_1('#skF_9')=k1_tarski(B_14290))), inference(negUnitSimplification, [status(thm)], [c_130, c_8629])).
% 7.05/2.39  tff(c_34, plain, (![A_18, B_19]: ('#skF_3'(A_18, B_19)!=B_19 | k1_xboole_0=A_18 | k1_tarski(B_19)=A_18)), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.05/2.39  tff(c_8649, plain, (![B_14290]: (k1_funct_1('#skF_9', '#skF_8')!=B_14290 | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_14290) | k2_relat_1('#skF_9')=k1_tarski(B_14290))), inference(superposition, [status(thm), theory('equality')], [c_8638, c_34])).
% 7.05/2.39  tff(c_8948, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))=k2_relat_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_130, c_8649])).
% 7.05/2.39  tff(c_64, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))!=k2_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.05/2.39  tff(c_8952, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8948, c_64])).
% 7.05/2.39  tff(c_8953, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_123])).
% 7.05/2.39  tff(c_87, plain, (![A_73]: (k1_relat_1(A_73)!=k1_xboole_0 | k1_xboole_0=A_73 | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.05/2.39  tff(c_91, plain, (k1_relat_1('#skF_9')!=k1_xboole_0 | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_70, c_87])).
% 7.05/2.39  tff(c_92, plain, (k1_relat_1('#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_91])).
% 7.05/2.39  tff(c_8956, plain, (k1_relat_1('#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_8953, c_92])).
% 7.05/2.39  tff(c_8954, plain, (k2_relat_1('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_123])).
% 7.05/2.39  tff(c_8962, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_8953, c_8954])).
% 7.05/2.39  tff(c_42, plain, (![A_22]: (k1_relat_1(A_22)=k1_xboole_0 | k2_relat_1(A_22)!=k1_xboole_0 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.05/2.39  tff(c_8989, plain, (![A_14867]: (k1_relat_1(A_14867)='#skF_9' | k2_relat_1(A_14867)!='#skF_9' | ~v1_relat_1(A_14867))), inference(demodulation, [status(thm), theory('equality')], [c_8953, c_8953, c_42])).
% 7.05/2.39  tff(c_8992, plain, (k1_relat_1('#skF_9')='#skF_9' | k2_relat_1('#skF_9')!='#skF_9'), inference(resolution, [status(thm)], [c_70, c_8989])).
% 7.05/2.39  tff(c_8995, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_8962, c_8992])).
% 7.05/2.39  tff(c_8997, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8956, c_8995])).
% 7.05/2.39  tff(c_8998, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_91])).
% 7.05/2.39  tff(c_8999, plain, (k1_relat_1('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_91])).
% 7.05/2.39  tff(c_9005, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_8998, c_8999])).
% 7.05/2.39  tff(c_9006, plain, (k1_tarski('#skF_8')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9005, c_66])).
% 7.05/2.39  tff(c_9022, plain, (![A_14869, B_14870]: (k1_enumset1(A_14869, A_14869, B_14870)=k2_tarski(A_14869, B_14870))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.05/2.39  tff(c_6, plain, (![E_7, A_1, C_3]: (r2_hidden(E_7, k1_enumset1(A_1, E_7, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.05/2.39  tff(c_9040, plain, (![A_14871, B_14872]: (r2_hidden(A_14871, k2_tarski(A_14871, B_14872)))), inference(superposition, [status(thm), theory('equality')], [c_9022, c_6])).
% 7.05/2.39  tff(c_9044, plain, (![A_14873]: (r2_hidden(A_14873, k1_tarski(A_14873)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_9040])).
% 7.05/2.39  tff(c_9047, plain, (r2_hidden('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_9006, c_9044])).
% 7.05/2.39  tff(c_44, plain, (![A_22]: (k2_relat_1(A_22)=k1_xboole_0 | k1_relat_1(A_22)!=k1_xboole_0 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.05/2.39  tff(c_9070, plain, (![A_14878]: (k2_relat_1(A_14878)='#skF_9' | k1_relat_1(A_14878)!='#skF_9' | ~v1_relat_1(A_14878))), inference(demodulation, [status(thm), theory('equality')], [c_8998, c_8998, c_44])).
% 7.05/2.39  tff(c_9073, plain, (k2_relat_1('#skF_9')='#skF_9' | k1_relat_1('#skF_9')!='#skF_9'), inference(resolution, [status(thm)], [c_70, c_9070])).
% 7.05/2.39  tff(c_9076, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9005, c_9073])).
% 7.05/2.39  tff(c_9173, plain, (![A_14900, D_14901]: (r2_hidden(k1_funct_1(A_14900, D_14901), k2_relat_1(A_14900)) | ~r2_hidden(D_14901, k1_relat_1(A_14900)) | ~v1_funct_1(A_14900) | ~v1_relat_1(A_14900))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.05/2.39  tff(c_9176, plain, (![D_14901]: (r2_hidden(k1_funct_1('#skF_9', D_14901), '#skF_9') | ~r2_hidden(D_14901, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_9076, c_9173])).
% 7.05/2.39  tff(c_9179, plain, (![D_14902]: (r2_hidden(k1_funct_1('#skF_9', D_14902), '#skF_9') | ~r2_hidden(D_14902, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_9005, c_9176])).
% 7.05/2.39  tff(c_9104, plain, (![E_14890, C_14891, B_14892, A_14893]: (E_14890=C_14891 | E_14890=B_14892 | E_14890=A_14893 | ~r2_hidden(E_14890, k1_enumset1(A_14893, B_14892, C_14891)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.05/2.39  tff(c_9128, plain, (![E_14894, B_14895, A_14896]: (E_14894=B_14895 | E_14894=A_14896 | E_14894=A_14896 | ~r2_hidden(E_14894, k2_tarski(A_14896, B_14895)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_9104])).
% 7.05/2.39  tff(c_9147, plain, (![E_14897, A_14898]: (E_14897=A_14898 | E_14897=A_14898 | E_14897=A_14898 | ~r2_hidden(E_14897, k1_tarski(A_14898)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_9128])).
% 7.05/2.39  tff(c_9157, plain, (![E_14897]: (E_14897='#skF_8' | E_14897='#skF_8' | E_14897='#skF_8' | ~r2_hidden(E_14897, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_9006, c_9147])).
% 7.05/2.39  tff(c_9184, plain, (![D_14903]: (k1_funct_1('#skF_9', D_14903)='#skF_8' | ~r2_hidden(D_14903, '#skF_9'))), inference(resolution, [status(thm)], [c_9179, c_9157])).
% 7.05/2.39  tff(c_9198, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_9047, c_9184])).
% 7.05/2.39  tff(c_9077, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9076, c_64])).
% 7.05/2.39  tff(c_9199, plain, (k1_tarski('#skF_8')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9198, c_9077])).
% 7.05/2.39  tff(c_9202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9006, c_9199])).
% 7.05/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/2.39  
% 7.05/2.39  Inference rules
% 7.05/2.39  ----------------------
% 7.05/2.39  #Ref     : 5
% 7.05/2.39  #Sup     : 1795
% 7.05/2.39  #Fact    : 5
% 7.05/2.39  #Define  : 0
% 7.05/2.39  #Split   : 4
% 7.05/2.39  #Chain   : 0
% 7.05/2.39  #Close   : 0
% 7.05/2.39  
% 7.05/2.39  Ordering : KBO
% 7.05/2.39  
% 7.05/2.39  Simplification rules
% 7.05/2.39  ----------------------
% 7.05/2.39  #Subsume      : 909
% 7.05/2.39  #Demod        : 242
% 7.05/2.39  #Tautology    : 454
% 7.05/2.39  #SimpNegUnit  : 147
% 7.05/2.39  #BackRed      : 10
% 7.05/2.39  
% 7.05/2.39  #Partial instantiations: 6930
% 7.05/2.39  #Strategies tried      : 1
% 7.05/2.39  
% 7.05/2.39  Timing (in seconds)
% 7.05/2.39  ----------------------
% 7.05/2.39  Preprocessing        : 0.34
% 7.05/2.39  Parsing              : 0.17
% 7.05/2.39  CNF conversion       : 0.03
% 7.05/2.39  Main loop            : 1.28
% 7.05/2.39  Inferencing          : 0.48
% 7.05/2.39  Reduction            : 0.37
% 7.05/2.39  Demodulation         : 0.26
% 7.05/2.39  BG Simplification    : 0.05
% 7.05/2.39  Subsumption          : 0.32
% 7.05/2.39  Abstraction          : 0.06
% 7.05/2.39  MUC search           : 0.00
% 7.05/2.39  Cooper               : 0.00
% 7.05/2.39  Total                : 1.65
% 7.05/2.39  Index Insertion      : 0.00
% 7.05/2.39  Index Deletion       : 0.00
% 7.05/2.39  Index Matching       : 0.00
% 7.05/2.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
