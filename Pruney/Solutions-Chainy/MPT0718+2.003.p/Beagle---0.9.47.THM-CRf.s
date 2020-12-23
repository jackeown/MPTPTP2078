%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:42 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 146 expanded)
%              Number of leaves         :   44 (  70 expanded)
%              Depth                    :   17
%              Number of atoms          :  165 ( 330 expanded)
%              Number of equality atoms :   38 (  76 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > r1_tarski > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v2_relat_1,type,(
    v2_relat_1: $i > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v5_funct_1(A,B)
                & k1_relat_1(A) = k1_relat_1(B) )
             => v2_relat_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_relat_1(A)
      <=> ! [B] :
            ~ ( r2_hidden(B,k1_relat_1(A))
              & v1_xboole_0(k1_funct_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_65,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_56,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k8_relat_1(A,B))
        & v1_funct_1(k8_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).

tff(f_62,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_50,plain,(
    ~ v2_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_58,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_54,plain,(
    v5_funct_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_36,plain,(
    ! [A_19] :
      ( r2_hidden('#skF_1'(A_19),k1_relat_1(A_19))
      | v2_relat_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_62,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_52,plain,(
    k1_relat_1('#skF_3') = k1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_90,plain,(
    ! [A_41] :
      ( k8_relat_1(k1_xboole_0,A_41) = k1_xboole_0
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_98,plain,(
    k8_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_90])).

tff(c_107,plain,(
    ! [A_42,B_43] :
      ( v1_relat_1(k8_relat_1(A_42,B_43))
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_113,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_107])).

tff(c_119,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_113])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    ! [A_14] : k7_relat_1(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_235,plain,(
    ! [B_61,A_62] :
      ( k3_xboole_0(k1_relat_1(B_61),A_62) = k1_relat_1(k7_relat_1(B_61,A_62))
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_255,plain,(
    ! [A_62] :
      ( k1_relat_1(k7_relat_1(k1_xboole_0,A_62)) = k3_xboole_0(k1_xboole_0,A_62)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_235])).

tff(c_261,plain,(
    ! [A_62] : k3_xboole_0(k1_xboole_0,A_62) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_28,c_20,c_255])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_144,plain,(
    ! [A_51,B_52] :
      ( v1_funct_1(k8_relat_1(A_51,B_52))
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_150,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_144])).

tff(c_157,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_150])).

tff(c_24,plain,(
    ! [A_16] : k9_relat_1(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_368,plain,(
    ! [B_70,A_71] :
      ( r1_tarski(k9_relat_1(B_70,k10_relat_1(B_70,A_71)),A_71)
      | ~ v1_funct_1(B_70)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_375,plain,(
    ! [A_71] :
      ( r1_tarski(k1_xboole_0,A_71)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_368])).

tff(c_379,plain,(
    ! [A_72] : r1_tarski(k1_xboole_0,A_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_157,c_375])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_384,plain,(
    ! [A_73] : k2_xboole_0(k1_xboole_0,A_73) = A_73 ),
    inference(resolution,[status(thm)],[c_379,c_8])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(k2_xboole_0(A_6,B_7),B_7) = A_6
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_396,plain,(
    ! [A_74] :
      ( k4_xboole_0(A_74,A_74) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_10])).

tff(c_399,plain,(
    ! [B_2] :
      ( k4_xboole_0(B_2,B_2) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_396])).

tff(c_402,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_399])).

tff(c_14,plain,(
    ! [B_11] : k4_xboole_0(k1_tarski(B_11),k1_tarski(B_11)) != k1_tarski(B_11) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_404,plain,(
    ! [B_11] : k1_tarski(B_11) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_14])).

tff(c_262,plain,(
    ! [A_63] : k3_xboole_0(k1_xboole_0,A_63) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_28,c_20,c_255])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k3_xboole_0(B_9,k1_tarski(A_8)) = k1_tarski(A_8)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_268,plain,(
    ! [A_8] :
      ( k1_tarski(A_8) = k1_xboole_0
      | ~ r2_hidden(A_8,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_12])).

tff(c_439,plain,(
    ! [A_8] : ~ r2_hidden(A_8,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_268])).

tff(c_306,plain,(
    ! [A_66] :
      ( v1_xboole_0(k1_funct_1(A_66,'#skF_1'(A_66)))
      | v2_relat_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_310,plain,(
    ! [A_66] :
      ( k1_funct_1(A_66,'#skF_1'(A_66)) = k1_xboole_0
      | v2_relat_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(resolution,[status(thm)],[c_306,c_6])).

tff(c_627,plain,(
    ! [B_91,C_92,A_93] :
      ( r2_hidden(k1_funct_1(B_91,C_92),k1_funct_1(A_93,C_92))
      | ~ r2_hidden(C_92,k1_relat_1(B_91))
      | ~ v5_funct_1(B_91,A_93)
      | ~ v1_funct_1(B_91)
      | ~ v1_relat_1(B_91)
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_633,plain,(
    ! [B_91,A_66] :
      ( r2_hidden(k1_funct_1(B_91,'#skF_1'(A_66)),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_66),k1_relat_1(B_91))
      | ~ v5_funct_1(B_91,A_66)
      | ~ v1_funct_1(B_91)
      | ~ v1_relat_1(B_91)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66)
      | v2_relat_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_627])).

tff(c_923,plain,(
    ! [A_118,B_119] :
      ( ~ r2_hidden('#skF_1'(A_118),k1_relat_1(B_119))
      | ~ v5_funct_1(B_119,A_118)
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118)
      | v2_relat_1(A_118)
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(negUnitSimplification,[status(thm)],[c_439,c_633])).

tff(c_956,plain,(
    ! [A_118] :
      ( ~ r2_hidden('#skF_1'(A_118),k1_relat_1('#skF_4'))
      | ~ v5_funct_1('#skF_3',A_118)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118)
      | v2_relat_1(A_118)
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_923])).

tff(c_1002,plain,(
    ! [A_123] :
      ( ~ r2_hidden('#skF_1'(A_123),k1_relat_1('#skF_4'))
      | ~ v5_funct_1('#skF_3',A_123)
      | v2_relat_1(A_123)
      | ~ v1_funct_1(A_123)
      | ~ v1_relat_1(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_956])).

tff(c_1006,plain,
    ( ~ v5_funct_1('#skF_3','#skF_4')
    | v2_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1002])).

tff(c_1009,plain,(
    v2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1006])).

tff(c_1011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1009])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:45:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.47  
% 3.27/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.47  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > r1_tarski > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.27/1.47  
% 3.27/1.47  %Foreground sorts:
% 3.27/1.47  
% 3.27/1.47  
% 3.27/1.47  %Background operators:
% 3.27/1.47  
% 3.27/1.47  
% 3.27/1.47  %Foreground operators:
% 3.27/1.47  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.27/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.27/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.47  tff(v2_relat_1, type, v2_relat_1: $i > $o).
% 3.27/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.27/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.27/1.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.27/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.27/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.27/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.47  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 3.27/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.27/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.27/1.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.27/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.27/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.47  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.27/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.27/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.27/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.27/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.27/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.27/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.27/1.47  
% 3.27/1.49  tff(f_127, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v5_funct_1(A, B) & (k1_relat_1(A) = k1_relat_1(B))) => v2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_funct_1)).
% 3.27/1.49  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_relat_1(A) <=> (![B]: ~(r2_hidden(B, k1_relat_1(A)) & v1_xboole_0(k1_funct_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_funct_1)).
% 3.27/1.49  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 3.27/1.49  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 3.27/1.49  tff(f_65, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.27/1.49  tff(f_56, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 3.27/1.49  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.27/1.49  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.27/1.49  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v1_relat_1(k8_relat_1(A, B)) & v1_funct_1(k8_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_funct_1)).
% 3.27/1.49  tff(f_62, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 3.27/1.49  tff(f_111, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 3.27/1.49  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.27/1.49  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 3.27/1.49  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.27/1.49  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 3.27/1.49  tff(f_33, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.27/1.49  tff(f_97, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 3.27/1.49  tff(c_50, plain, (~v2_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.27/1.49  tff(c_58, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.27/1.49  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.27/1.49  tff(c_54, plain, (v5_funct_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.27/1.49  tff(c_36, plain, (![A_19]: (r2_hidden('#skF_1'(A_19), k1_relat_1(A_19)) | v2_relat_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.27/1.49  tff(c_62, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.27/1.49  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.27/1.49  tff(c_52, plain, (k1_relat_1('#skF_3')=k1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.27/1.49  tff(c_90, plain, (![A_41]: (k8_relat_1(k1_xboole_0, A_41)=k1_xboole_0 | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.27/1.49  tff(c_98, plain, (k8_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_90])).
% 3.27/1.49  tff(c_107, plain, (![A_42, B_43]: (v1_relat_1(k8_relat_1(A_42, B_43)) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.27/1.49  tff(c_113, plain, (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_98, c_107])).
% 3.27/1.49  tff(c_119, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_113])).
% 3.27/1.49  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.27/1.49  tff(c_20, plain, (![A_14]: (k7_relat_1(k1_xboole_0, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.27/1.49  tff(c_235, plain, (![B_61, A_62]: (k3_xboole_0(k1_relat_1(B_61), A_62)=k1_relat_1(k7_relat_1(B_61, A_62)) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.27/1.49  tff(c_255, plain, (![A_62]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_62))=k3_xboole_0(k1_xboole_0, A_62) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_235])).
% 3.27/1.49  tff(c_261, plain, (![A_62]: (k3_xboole_0(k1_xboole_0, A_62)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_119, c_28, c_20, c_255])).
% 3.27/1.49  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.27/1.49  tff(c_144, plain, (![A_51, B_52]: (v1_funct_1(k8_relat_1(A_51, B_52)) | ~v1_funct_1(B_52) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.27/1.49  tff(c_150, plain, (v1_funct_1(k1_xboole_0) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_98, c_144])).
% 3.27/1.49  tff(c_157, plain, (v1_funct_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_150])).
% 3.27/1.49  tff(c_24, plain, (![A_16]: (k9_relat_1(k1_xboole_0, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.27/1.49  tff(c_368, plain, (![B_70, A_71]: (r1_tarski(k9_relat_1(B_70, k10_relat_1(B_70, A_71)), A_71) | ~v1_funct_1(B_70) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.27/1.49  tff(c_375, plain, (![A_71]: (r1_tarski(k1_xboole_0, A_71) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_368])).
% 3.27/1.49  tff(c_379, plain, (![A_72]: (r1_tarski(k1_xboole_0, A_72))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_157, c_375])).
% 3.27/1.49  tff(c_8, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.27/1.49  tff(c_384, plain, (![A_73]: (k2_xboole_0(k1_xboole_0, A_73)=A_73)), inference(resolution, [status(thm)], [c_379, c_8])).
% 3.27/1.49  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(k2_xboole_0(A_6, B_7), B_7)=A_6 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.27/1.49  tff(c_396, plain, (![A_74]: (k4_xboole_0(A_74, A_74)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_74))), inference(superposition, [status(thm), theory('equality')], [c_384, c_10])).
% 3.27/1.49  tff(c_399, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_396])).
% 3.27/1.49  tff(c_402, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_261, c_399])).
% 3.27/1.49  tff(c_14, plain, (![B_11]: (k4_xboole_0(k1_tarski(B_11), k1_tarski(B_11))!=k1_tarski(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.27/1.49  tff(c_404, plain, (![B_11]: (k1_tarski(B_11)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_402, c_14])).
% 3.27/1.49  tff(c_262, plain, (![A_63]: (k3_xboole_0(k1_xboole_0, A_63)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_119, c_28, c_20, c_255])).
% 3.27/1.49  tff(c_12, plain, (![B_9, A_8]: (k3_xboole_0(B_9, k1_tarski(A_8))=k1_tarski(A_8) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.27/1.49  tff(c_268, plain, (![A_8]: (k1_tarski(A_8)=k1_xboole_0 | ~r2_hidden(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_262, c_12])).
% 3.27/1.49  tff(c_439, plain, (![A_8]: (~r2_hidden(A_8, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_404, c_268])).
% 3.27/1.49  tff(c_306, plain, (![A_66]: (v1_xboole_0(k1_funct_1(A_66, '#skF_1'(A_66))) | v2_relat_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.27/1.49  tff(c_6, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.27/1.49  tff(c_310, plain, (![A_66]: (k1_funct_1(A_66, '#skF_1'(A_66))=k1_xboole_0 | v2_relat_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(resolution, [status(thm)], [c_306, c_6])).
% 3.27/1.49  tff(c_627, plain, (![B_91, C_92, A_93]: (r2_hidden(k1_funct_1(B_91, C_92), k1_funct_1(A_93, C_92)) | ~r2_hidden(C_92, k1_relat_1(B_91)) | ~v5_funct_1(B_91, A_93) | ~v1_funct_1(B_91) | ~v1_relat_1(B_91) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.27/1.49  tff(c_633, plain, (![B_91, A_66]: (r2_hidden(k1_funct_1(B_91, '#skF_1'(A_66)), k1_xboole_0) | ~r2_hidden('#skF_1'(A_66), k1_relat_1(B_91)) | ~v5_funct_1(B_91, A_66) | ~v1_funct_1(B_91) | ~v1_relat_1(B_91) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66) | v2_relat_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(superposition, [status(thm), theory('equality')], [c_310, c_627])).
% 3.27/1.49  tff(c_923, plain, (![A_118, B_119]: (~r2_hidden('#skF_1'(A_118), k1_relat_1(B_119)) | ~v5_funct_1(B_119, A_118) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118) | v2_relat_1(A_118) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(negUnitSimplification, [status(thm)], [c_439, c_633])).
% 3.27/1.49  tff(c_956, plain, (![A_118]: (~r2_hidden('#skF_1'(A_118), k1_relat_1('#skF_4')) | ~v5_funct_1('#skF_3', A_118) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(A_118) | ~v1_relat_1(A_118) | v2_relat_1(A_118) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(superposition, [status(thm), theory('equality')], [c_52, c_923])).
% 3.27/1.49  tff(c_1002, plain, (![A_123]: (~r2_hidden('#skF_1'(A_123), k1_relat_1('#skF_4')) | ~v5_funct_1('#skF_3', A_123) | v2_relat_1(A_123) | ~v1_funct_1(A_123) | ~v1_relat_1(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_956])).
% 3.27/1.49  tff(c_1006, plain, (~v5_funct_1('#skF_3', '#skF_4') | v2_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1002])).
% 3.27/1.49  tff(c_1009, plain, (v2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1006])).
% 3.27/1.49  tff(c_1011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1009])).
% 3.27/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.49  
% 3.27/1.49  Inference rules
% 3.27/1.49  ----------------------
% 3.27/1.49  #Ref     : 0
% 3.27/1.49  #Sup     : 218
% 3.27/1.49  #Fact    : 0
% 3.27/1.49  #Define  : 0
% 3.27/1.49  #Split   : 2
% 3.27/1.49  #Chain   : 0
% 3.27/1.49  #Close   : 0
% 3.27/1.49  
% 3.27/1.49  Ordering : KBO
% 3.27/1.49  
% 3.27/1.49  Simplification rules
% 3.27/1.49  ----------------------
% 3.27/1.49  #Subsume      : 26
% 3.27/1.49  #Demod        : 126
% 3.27/1.49  #Tautology    : 93
% 3.27/1.49  #SimpNegUnit  : 7
% 3.27/1.49  #BackRed      : 3
% 3.27/1.49  
% 3.27/1.49  #Partial instantiations: 0
% 3.27/1.49  #Strategies tried      : 1
% 3.27/1.49  
% 3.27/1.49  Timing (in seconds)
% 3.27/1.49  ----------------------
% 3.27/1.49  Preprocessing        : 0.33
% 3.27/1.49  Parsing              : 0.17
% 3.27/1.49  CNF conversion       : 0.02
% 3.27/1.49  Main loop            : 0.40
% 3.27/1.49  Inferencing          : 0.15
% 3.27/1.49  Reduction            : 0.13
% 3.27/1.49  Demodulation         : 0.09
% 3.27/1.49  BG Simplification    : 0.02
% 3.27/1.49  Subsumption          : 0.07
% 3.27/1.49  Abstraction          : 0.02
% 3.27/1.49  MUC search           : 0.00
% 3.27/1.49  Cooper               : 0.00
% 3.27/1.49  Total                : 0.76
% 3.27/1.49  Index Insertion      : 0.00
% 3.27/1.49  Index Deletion       : 0.00
% 3.27/1.49  Index Matching       : 0.00
% 3.27/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
