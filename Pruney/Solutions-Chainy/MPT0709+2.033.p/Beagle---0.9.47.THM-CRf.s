%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:28 EST 2020

% Result     : Theorem 9.69s
% Output     : CNFRefutation 9.69s
% Verified   : 
% Statistics : Number of formulae       :  125 (1059 expanded)
%              Number of leaves         :   40 ( 378 expanded)
%              Depth                    :   25
%              Number of atoms          :  257 (2721 expanded)
%              Number of equality atoms :   36 ( 327 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_133,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_67,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_122,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_112,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_44,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_52,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_50,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_46,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_34,plain,(
    ! [B_30,A_29] :
      ( k10_relat_1(k2_funct_1(B_30),A_29) = k9_relat_1(B_30,A_29)
      | ~ v2_funct_1(B_30)
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    ! [A_26] :
      ( v1_funct_1(k2_funct_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    ! [A_26] :
      ( v1_relat_1(k2_funct_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    ! [A_20] :
      ( k9_relat_1(A_20,k1_relat_1(A_20)) = k2_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_430,plain,(
    ! [B_112,A_113] :
      ( k9_relat_1(k2_funct_1(B_112),A_113) = k10_relat_1(B_112,A_113)
      | ~ v2_funct_1(B_112)
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1245,plain,(
    ! [B_204] :
      ( k10_relat_1(B_204,k1_relat_1(k2_funct_1(B_204))) = k2_relat_1(k2_funct_1(B_204))
      | ~ v2_funct_1(B_204)
      | ~ v1_funct_1(B_204)
      | ~ v1_relat_1(B_204)
      | ~ v1_relat_1(k2_funct_1(B_204)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_430])).

tff(c_20,plain,(
    ! [A_21] :
      ( k10_relat_1(A_21,k2_relat_1(A_21)) = k1_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_203,plain,(
    ! [C_73,A_74,B_75] :
      ( r1_tarski(k10_relat_1(C_73,A_74),k10_relat_1(C_73,B_75))
      | ~ r1_tarski(A_74,B_75)
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_706,plain,(
    ! [A_170,B_171] :
      ( r1_tarski(k1_relat_1(A_170),k10_relat_1(A_170,B_171))
      | ~ r1_tarski(k2_relat_1(A_170),B_171)
      | ~ v1_relat_1(A_170)
      | ~ v1_relat_1(A_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_203])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_138,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_tarski(A_55,C_56)
      | ~ r1_tarski(B_57,C_56)
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_190,plain,(
    ! [A_69,C_70,B_71,A_72] :
      ( r1_tarski(A_69,k2_xboole_0(C_70,B_71))
      | ~ r1_tarski(A_69,A_72)
      | ~ r1_tarski(A_72,B_71) ) ),
    inference(resolution,[status(thm)],[c_4,c_138])).

tff(c_219,plain,(
    ! [C_76,B_77] :
      ( r1_tarski('#skF_1',k2_xboole_0(C_76,B_77))
      | ~ r1_tarski(k1_relat_1('#skF_2'),B_77) ) ),
    inference(resolution,[status(thm)],[c_48,c_190])).

tff(c_227,plain,(
    ! [C_76,C_5,B_4] :
      ( r1_tarski('#skF_1',k2_xboole_0(C_76,k2_xboole_0(C_5,B_4)))
      | ~ r1_tarski(k1_relat_1('#skF_2'),B_4) ) ),
    inference(resolution,[status(thm)],[c_4,c_219])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_tarski(k4_xboole_0(A_10,B_11),C_12)
      | ~ r1_tarski(A_10,k2_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_158,plain,(
    ! [A_62,B_63,C_64] :
      ( r1_tarski(k4_xboole_0(A_62,B_63),C_64)
      | ~ r1_tarski(A_62,k2_xboole_0(B_63,C_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_165,plain,(
    ! [A_65,C_66] :
      ( r1_tarski(A_65,C_66)
      | ~ r1_tarski(A_65,k2_xboole_0(k1_xboole_0,C_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_158])).

tff(c_245,plain,(
    ! [A_81,B_82,C_83] :
      ( r1_tarski(k4_xboole_0(A_81,B_82),C_83)
      | ~ r1_tarski(A_81,k2_xboole_0(B_82,k2_xboole_0(k1_xboole_0,C_83))) ) ),
    inference(resolution,[status(thm)],[c_10,c_165])).

tff(c_261,plain,(
    ! [C_84,B_85] :
      ( r1_tarski(k4_xboole_0('#skF_1',C_84),B_85)
      | ~ r1_tarski(k1_relat_1('#skF_2'),B_85) ) ),
    inference(resolution,[status(thm)],[c_227,c_245])).

tff(c_145,plain,(
    ! [A_58] :
      ( r1_tarski(A_58,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_58,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_138])).

tff(c_6,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_148,plain,(
    ! [A_6,A_58] :
      ( r1_tarski(A_6,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_6,A_58)
      | ~ r1_tarski(A_58,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_145,c_6])).

tff(c_282,plain,(
    ! [C_84,B_85] :
      ( r1_tarski(k4_xboole_0('#skF_1',C_84),k1_relat_1('#skF_2'))
      | ~ r1_tarski(B_85,'#skF_1')
      | ~ r1_tarski(k1_relat_1('#skF_2'),B_85) ) ),
    inference(resolution,[status(thm)],[c_261,c_148])).

tff(c_379,plain,(
    ! [B_85] :
      ( ~ r1_tarski(B_85,'#skF_1')
      | ~ r1_tarski(k1_relat_1('#skF_2'),B_85) ) ),
    inference(splitLeft,[status(thm)],[c_282])).

tff(c_716,plain,(
    ! [B_171] :
      ( ~ r1_tarski(k10_relat_1('#skF_2',B_171),'#skF_1')
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_171)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_706,c_379])).

tff(c_747,plain,(
    ! [B_171] :
      ( ~ r1_tarski(k10_relat_1('#skF_2',B_171),'#skF_1')
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_716])).

tff(c_1262,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),'#skF_1')
    | ~ r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1245,c_747])).

tff(c_1292,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),'#skF_1')
    | ~ r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_1262])).

tff(c_1839,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1292])).

tff(c_1842,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1839])).

tff(c_1846,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1842])).

tff(c_1848,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1292])).

tff(c_444,plain,(
    ! [B_112] :
      ( k10_relat_1(B_112,k1_relat_1(k2_funct_1(B_112))) = k2_relat_1(k2_funct_1(B_112))
      | ~ v2_funct_1(B_112)
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112)
      | ~ v1_relat_1(k2_funct_1(B_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_430])).

tff(c_24,plain,(
    ! [A_25] : k1_relat_1(k6_relat_1(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_42,plain,(
    ! [A_36] :
      ( k5_relat_1(A_36,k2_funct_1(A_36)) = k6_relat_1(k1_relat_1(A_36))
      | ~ v2_funct_1(A_36)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_38,plain,(
    ! [B_35,A_33] :
      ( r1_tarski(k2_relat_1(B_35),k1_relat_1(A_33))
      | k1_relat_1(k5_relat_1(B_35,A_33)) != k1_relat_1(B_35)
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_212,plain,(
    ! [A_21,B_75] :
      ( r1_tarski(k1_relat_1(A_21),k10_relat_1(A_21,B_75))
      | ~ r1_tarski(k2_relat_1(A_21),B_75)
      | ~ v1_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_203])).

tff(c_2473,plain,(
    ! [C_284,C_288,B_285,B_286,A_287] :
      ( r1_tarski(k4_xboole_0(A_287,B_285),k2_xboole_0(C_284,B_286))
      | ~ r1_tarski(C_288,B_286)
      | ~ r1_tarski(A_287,k2_xboole_0(B_285,C_288)) ) ),
    inference(resolution,[status(thm)],[c_10,c_190])).

tff(c_2540,plain,(
    ! [A_289,B_290,C_291] :
      ( r1_tarski(k4_xboole_0(A_289,B_290),k2_xboole_0(C_291,k1_relat_1('#skF_2')))
      | ~ r1_tarski(A_289,k2_xboole_0(B_290,'#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_48,c_2473])).

tff(c_2666,plain,(
    ! [A_295,C_296] :
      ( r1_tarski(A_295,k2_xboole_0(C_296,k1_relat_1('#skF_2')))
      | ~ r1_tarski(A_295,k2_xboole_0(k1_xboole_0,'#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2540])).

tff(c_258,plain,(
    ! [C_76,B_4] :
      ( r1_tarski(k4_xboole_0('#skF_1',C_76),B_4)
      | ~ r1_tarski(k1_relat_1('#skF_2'),B_4) ) ),
    inference(resolution,[status(thm)],[c_227,c_245])).

tff(c_456,plain,(
    ! [A_115,C_116,A_117,B_118] :
      ( r1_tarski(A_115,C_116)
      | ~ r1_tarski(A_115,k4_xboole_0(A_117,B_118))
      | ~ r1_tarski(A_117,k2_xboole_0(B_118,C_116)) ) ),
    inference(resolution,[status(thm)],[c_158,c_6])).

tff(c_471,plain,(
    ! [A_119,C_120,A_121] :
      ( r1_tarski(A_119,C_120)
      | ~ r1_tarski(A_119,A_121)
      | ~ r1_tarski(A_121,k2_xboole_0(k1_xboole_0,C_120)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_456])).

tff(c_489,plain,(
    ! [C_76,C_120,B_4] :
      ( r1_tarski(k4_xboole_0('#skF_1',C_76),C_120)
      | ~ r1_tarski(B_4,k2_xboole_0(k1_xboole_0,C_120))
      | ~ r1_tarski(k1_relat_1('#skF_2'),B_4) ) ),
    inference(resolution,[status(thm)],[c_258,c_471])).

tff(c_2796,plain,(
    ! [C_76,A_295] :
      ( r1_tarski(k4_xboole_0('#skF_1',C_76),k1_relat_1('#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_295)
      | ~ r1_tarski(A_295,k2_xboole_0(k1_xboole_0,'#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_2666,c_489])).

tff(c_6706,plain,(
    ! [A_478] :
      ( ~ r1_tarski(k1_relat_1('#skF_2'),A_478)
      | ~ r1_tarski(A_478,k2_xboole_0(k1_xboole_0,'#skF_1')) ) ),
    inference(splitLeft,[status(thm)],[c_2796])).

tff(c_6736,plain,(
    ! [B_75] :
      ( ~ r1_tarski(k10_relat_1('#skF_2',B_75),k2_xboole_0(k1_xboole_0,'#skF_1'))
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_75)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_212,c_6706])).

tff(c_6759,plain,(
    ! [B_479] :
      ( ~ r1_tarski(k10_relat_1('#skF_2',B_479),k2_xboole_0(k1_xboole_0,'#skF_1'))
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_479) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6736])).

tff(c_6763,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),k2_xboole_0(k1_xboole_0,'#skF_1'))
    | ~ r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_6759])).

tff(c_6772,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),k2_xboole_0(k1_xboole_0,'#skF_1'))
    | ~ r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1848,c_52,c_50,c_46,c_6763])).

tff(c_6844,plain,(
    ~ r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_6772])).

tff(c_6847,plain,
    ( k1_relat_1(k5_relat_1('#skF_2',k2_funct_1('#skF_2'))) != k1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_6844])).

tff(c_6850,plain,
    ( k1_relat_1(k5_relat_1('#skF_2',k2_funct_1('#skF_2'))) != k1_relat_1('#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1848,c_52,c_50,c_6847])).

tff(c_6993,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_6850])).

tff(c_6996,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_6993])).

tff(c_7000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_6996])).

tff(c_7001,plain,(
    k1_relat_1(k5_relat_1('#skF_2',k2_funct_1('#skF_2'))) != k1_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_6850])).

tff(c_7005,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) != k1_relat_1('#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_7001])).

tff(c_7008,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_24,c_7005])).

tff(c_7010,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_6772])).

tff(c_279,plain,(
    ! [B_85] :
      ( r1_tarski('#skF_1',B_85)
      | ~ r1_tarski(k1_relat_1('#skF_2'),B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_261])).

tff(c_723,plain,(
    ! [B_171] :
      ( r1_tarski('#skF_1',k10_relat_1('#skF_2',B_171))
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_171)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_706,c_279])).

tff(c_753,plain,(
    ! [B_171] :
      ( r1_tarski('#skF_1',k10_relat_1('#skF_2',B_171))
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_723])).

tff(c_7099,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k1_relat_1(k2_funct_1('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_7010,c_753])).

tff(c_7164,plain,
    ( r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_7099])).

tff(c_7200,plain,(
    r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1848,c_52,c_50,c_46,c_7164])).

tff(c_32,plain,(
    ! [B_28,A_27] :
      ( k9_relat_1(B_28,k10_relat_1(B_28,A_27)) = A_27
      | ~ r1_tarski(A_27,k2_relat_1(B_28))
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_7281,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),k10_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = '#skF_1'
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_7200,c_32])).

tff(c_7325,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),k10_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = '#skF_1'
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1848,c_7281])).

tff(c_9459,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_7325])).

tff(c_9462,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_9459])).

tff(c_9466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_9462])).

tff(c_9467,plain,(
    k9_relat_1(k2_funct_1('#skF_2'),k10_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7325])).

tff(c_36,plain,(
    ! [B_32,A_31] :
      ( k9_relat_1(k2_funct_1(B_32),A_31) = k10_relat_1(B_32,A_31)
      | ~ v2_funct_1(B_32)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_9478,plain,
    ( k10_relat_1('#skF_2',k10_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9467,c_36])).

tff(c_9492,plain,(
    k10_relat_1('#skF_2',k10_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_9478])).

tff(c_9589,plain,
    ( k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_9492])).

tff(c_9618,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_9589])).

tff(c_9620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_9618])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:38:39 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.69/3.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.69/3.61  
% 9.69/3.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.69/3.61  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 9.69/3.61  
% 9.69/3.61  %Foreground sorts:
% 9.69/3.61  
% 9.69/3.61  
% 9.69/3.61  %Background operators:
% 9.69/3.61  
% 9.69/3.61  
% 9.69/3.61  %Foreground operators:
% 9.69/3.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.69/3.61  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.69/3.61  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.69/3.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.69/3.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.69/3.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.69/3.61  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.69/3.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.69/3.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.69/3.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.69/3.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.69/3.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.69/3.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.69/3.61  tff('#skF_2', type, '#skF_2': $i).
% 9.69/3.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.69/3.61  tff('#skF_1', type, '#skF_1': $i).
% 9.69/3.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.69/3.61  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.69/3.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.69/3.61  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.69/3.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.69/3.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.69/3.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.69/3.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.69/3.61  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.69/3.61  
% 9.69/3.64  tff(f_133, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 9.69/3.64  tff(f_91, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 9.69/3.64  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.69/3.64  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 9.69/3.64  tff(f_99, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 9.69/3.64  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 9.69/3.64  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 9.69/3.64  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 9.69/3.64  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.69/3.64  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 9.69/3.64  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 9.69/3.64  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 9.69/3.64  tff(f_122, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 9.69/3.64  tff(f_112, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 9.69/3.64  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 9.69/3.64  tff(c_44, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.69/3.64  tff(c_52, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.69/3.64  tff(c_50, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.69/3.64  tff(c_46, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.69/3.64  tff(c_34, plain, (![B_30, A_29]: (k10_relat_1(k2_funct_1(B_30), A_29)=k9_relat_1(B_30, A_29) | ~v2_funct_1(B_30) | ~v1_funct_1(B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.69/3.64  tff(c_28, plain, (![A_26]: (v1_funct_1(k2_funct_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.69/3.64  tff(c_30, plain, (![A_26]: (v1_relat_1(k2_funct_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.69/3.64  tff(c_18, plain, (![A_20]: (k9_relat_1(A_20, k1_relat_1(A_20))=k2_relat_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.69/3.64  tff(c_430, plain, (![B_112, A_113]: (k9_relat_1(k2_funct_1(B_112), A_113)=k10_relat_1(B_112, A_113) | ~v2_funct_1(B_112) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.69/3.64  tff(c_1245, plain, (![B_204]: (k10_relat_1(B_204, k1_relat_1(k2_funct_1(B_204)))=k2_relat_1(k2_funct_1(B_204)) | ~v2_funct_1(B_204) | ~v1_funct_1(B_204) | ~v1_relat_1(B_204) | ~v1_relat_1(k2_funct_1(B_204)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_430])).
% 9.69/3.64  tff(c_20, plain, (![A_21]: (k10_relat_1(A_21, k2_relat_1(A_21))=k1_relat_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.69/3.64  tff(c_203, plain, (![C_73, A_74, B_75]: (r1_tarski(k10_relat_1(C_73, A_74), k10_relat_1(C_73, B_75)) | ~r1_tarski(A_74, B_75) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.69/3.64  tff(c_706, plain, (![A_170, B_171]: (r1_tarski(k1_relat_1(A_170), k10_relat_1(A_170, B_171)) | ~r1_tarski(k2_relat_1(A_170), B_171) | ~v1_relat_1(A_170) | ~v1_relat_1(A_170))), inference(superposition, [status(thm), theory('equality')], [c_20, c_203])).
% 9.69/3.64  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.69/3.64  tff(c_48, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.69/3.64  tff(c_138, plain, (![A_55, C_56, B_57]: (r1_tarski(A_55, C_56) | ~r1_tarski(B_57, C_56) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.69/3.64  tff(c_190, plain, (![A_69, C_70, B_71, A_72]: (r1_tarski(A_69, k2_xboole_0(C_70, B_71)) | ~r1_tarski(A_69, A_72) | ~r1_tarski(A_72, B_71))), inference(resolution, [status(thm)], [c_4, c_138])).
% 9.69/3.64  tff(c_219, plain, (![C_76, B_77]: (r1_tarski('#skF_1', k2_xboole_0(C_76, B_77)) | ~r1_tarski(k1_relat_1('#skF_2'), B_77))), inference(resolution, [status(thm)], [c_48, c_190])).
% 9.69/3.64  tff(c_227, plain, (![C_76, C_5, B_4]: (r1_tarski('#skF_1', k2_xboole_0(C_76, k2_xboole_0(C_5, B_4))) | ~r1_tarski(k1_relat_1('#skF_2'), B_4))), inference(resolution, [status(thm)], [c_4, c_219])).
% 9.69/3.64  tff(c_10, plain, (![A_10, B_11, C_12]: (r1_tarski(k4_xboole_0(A_10, B_11), C_12) | ~r1_tarski(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.69/3.64  tff(c_8, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.69/3.64  tff(c_158, plain, (![A_62, B_63, C_64]: (r1_tarski(k4_xboole_0(A_62, B_63), C_64) | ~r1_tarski(A_62, k2_xboole_0(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.69/3.64  tff(c_165, plain, (![A_65, C_66]: (r1_tarski(A_65, C_66) | ~r1_tarski(A_65, k2_xboole_0(k1_xboole_0, C_66)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_158])).
% 9.69/3.64  tff(c_245, plain, (![A_81, B_82, C_83]: (r1_tarski(k4_xboole_0(A_81, B_82), C_83) | ~r1_tarski(A_81, k2_xboole_0(B_82, k2_xboole_0(k1_xboole_0, C_83))))), inference(resolution, [status(thm)], [c_10, c_165])).
% 9.69/3.64  tff(c_261, plain, (![C_84, B_85]: (r1_tarski(k4_xboole_0('#skF_1', C_84), B_85) | ~r1_tarski(k1_relat_1('#skF_2'), B_85))), inference(resolution, [status(thm)], [c_227, c_245])).
% 9.69/3.64  tff(c_145, plain, (![A_58]: (r1_tarski(A_58, k1_relat_1('#skF_2')) | ~r1_tarski(A_58, '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_138])).
% 9.69/3.64  tff(c_6, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.69/3.64  tff(c_148, plain, (![A_6, A_58]: (r1_tarski(A_6, k1_relat_1('#skF_2')) | ~r1_tarski(A_6, A_58) | ~r1_tarski(A_58, '#skF_1'))), inference(resolution, [status(thm)], [c_145, c_6])).
% 9.69/3.64  tff(c_282, plain, (![C_84, B_85]: (r1_tarski(k4_xboole_0('#skF_1', C_84), k1_relat_1('#skF_2')) | ~r1_tarski(B_85, '#skF_1') | ~r1_tarski(k1_relat_1('#skF_2'), B_85))), inference(resolution, [status(thm)], [c_261, c_148])).
% 9.69/3.64  tff(c_379, plain, (![B_85]: (~r1_tarski(B_85, '#skF_1') | ~r1_tarski(k1_relat_1('#skF_2'), B_85))), inference(splitLeft, [status(thm)], [c_282])).
% 9.69/3.64  tff(c_716, plain, (![B_171]: (~r1_tarski(k10_relat_1('#skF_2', B_171), '#skF_1') | ~r1_tarski(k2_relat_1('#skF_2'), B_171) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_706, c_379])).
% 9.69/3.64  tff(c_747, plain, (![B_171]: (~r1_tarski(k10_relat_1('#skF_2', B_171), '#skF_1') | ~r1_tarski(k2_relat_1('#skF_2'), B_171))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_716])).
% 9.69/3.64  tff(c_1262, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), '#skF_1') | ~r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1245, c_747])).
% 9.69/3.64  tff(c_1292, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), '#skF_1') | ~r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_1262])).
% 9.69/3.64  tff(c_1839, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1292])).
% 9.69/3.64  tff(c_1842, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_1839])).
% 9.69/3.64  tff(c_1846, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1842])).
% 9.69/3.64  tff(c_1848, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1292])).
% 9.69/3.64  tff(c_444, plain, (![B_112]: (k10_relat_1(B_112, k1_relat_1(k2_funct_1(B_112)))=k2_relat_1(k2_funct_1(B_112)) | ~v2_funct_1(B_112) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112) | ~v1_relat_1(k2_funct_1(B_112)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_430])).
% 9.69/3.64  tff(c_24, plain, (![A_25]: (k1_relat_1(k6_relat_1(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.69/3.64  tff(c_42, plain, (![A_36]: (k5_relat_1(A_36, k2_funct_1(A_36))=k6_relat_1(k1_relat_1(A_36)) | ~v2_funct_1(A_36) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.69/3.64  tff(c_38, plain, (![B_35, A_33]: (r1_tarski(k2_relat_1(B_35), k1_relat_1(A_33)) | k1_relat_1(k5_relat_1(B_35, A_33))!=k1_relat_1(B_35) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.69/3.64  tff(c_212, plain, (![A_21, B_75]: (r1_tarski(k1_relat_1(A_21), k10_relat_1(A_21, B_75)) | ~r1_tarski(k2_relat_1(A_21), B_75) | ~v1_relat_1(A_21) | ~v1_relat_1(A_21))), inference(superposition, [status(thm), theory('equality')], [c_20, c_203])).
% 9.69/3.64  tff(c_2473, plain, (![C_284, C_288, B_285, B_286, A_287]: (r1_tarski(k4_xboole_0(A_287, B_285), k2_xboole_0(C_284, B_286)) | ~r1_tarski(C_288, B_286) | ~r1_tarski(A_287, k2_xboole_0(B_285, C_288)))), inference(resolution, [status(thm)], [c_10, c_190])).
% 9.69/3.64  tff(c_2540, plain, (![A_289, B_290, C_291]: (r1_tarski(k4_xboole_0(A_289, B_290), k2_xboole_0(C_291, k1_relat_1('#skF_2'))) | ~r1_tarski(A_289, k2_xboole_0(B_290, '#skF_1')))), inference(resolution, [status(thm)], [c_48, c_2473])).
% 9.69/3.64  tff(c_2666, plain, (![A_295, C_296]: (r1_tarski(A_295, k2_xboole_0(C_296, k1_relat_1('#skF_2'))) | ~r1_tarski(A_295, k2_xboole_0(k1_xboole_0, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2540])).
% 9.69/3.64  tff(c_258, plain, (![C_76, B_4]: (r1_tarski(k4_xboole_0('#skF_1', C_76), B_4) | ~r1_tarski(k1_relat_1('#skF_2'), B_4))), inference(resolution, [status(thm)], [c_227, c_245])).
% 9.69/3.64  tff(c_456, plain, (![A_115, C_116, A_117, B_118]: (r1_tarski(A_115, C_116) | ~r1_tarski(A_115, k4_xboole_0(A_117, B_118)) | ~r1_tarski(A_117, k2_xboole_0(B_118, C_116)))), inference(resolution, [status(thm)], [c_158, c_6])).
% 9.69/3.64  tff(c_471, plain, (![A_119, C_120, A_121]: (r1_tarski(A_119, C_120) | ~r1_tarski(A_119, A_121) | ~r1_tarski(A_121, k2_xboole_0(k1_xboole_0, C_120)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_456])).
% 9.69/3.64  tff(c_489, plain, (![C_76, C_120, B_4]: (r1_tarski(k4_xboole_0('#skF_1', C_76), C_120) | ~r1_tarski(B_4, k2_xboole_0(k1_xboole_0, C_120)) | ~r1_tarski(k1_relat_1('#skF_2'), B_4))), inference(resolution, [status(thm)], [c_258, c_471])).
% 9.69/3.64  tff(c_2796, plain, (![C_76, A_295]: (r1_tarski(k4_xboole_0('#skF_1', C_76), k1_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_2'), A_295) | ~r1_tarski(A_295, k2_xboole_0(k1_xboole_0, '#skF_1')))), inference(resolution, [status(thm)], [c_2666, c_489])).
% 9.69/3.64  tff(c_6706, plain, (![A_478]: (~r1_tarski(k1_relat_1('#skF_2'), A_478) | ~r1_tarski(A_478, k2_xboole_0(k1_xboole_0, '#skF_1')))), inference(splitLeft, [status(thm)], [c_2796])).
% 9.69/3.64  tff(c_6736, plain, (![B_75]: (~r1_tarski(k10_relat_1('#skF_2', B_75), k2_xboole_0(k1_xboole_0, '#skF_1')) | ~r1_tarski(k2_relat_1('#skF_2'), B_75) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_212, c_6706])).
% 9.69/3.64  tff(c_6759, plain, (![B_479]: (~r1_tarski(k10_relat_1('#skF_2', B_479), k2_xboole_0(k1_xboole_0, '#skF_1')) | ~r1_tarski(k2_relat_1('#skF_2'), B_479))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6736])).
% 9.69/3.64  tff(c_6763, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), k2_xboole_0(k1_xboole_0, '#skF_1')) | ~r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_444, c_6759])).
% 9.69/3.64  tff(c_6772, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), k2_xboole_0(k1_xboole_0, '#skF_1')) | ~r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1848, c_52, c_50, c_46, c_6763])).
% 9.69/3.64  tff(c_6844, plain, (~r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_6772])).
% 9.69/3.64  tff(c_6847, plain, (k1_relat_1(k5_relat_1('#skF_2', k2_funct_1('#skF_2')))!=k1_relat_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_6844])).
% 9.69/3.64  tff(c_6850, plain, (k1_relat_1(k5_relat_1('#skF_2', k2_funct_1('#skF_2')))!=k1_relat_1('#skF_2') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1848, c_52, c_50, c_6847])).
% 9.69/3.64  tff(c_6993, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_6850])).
% 9.69/3.64  tff(c_6996, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_6993])).
% 9.69/3.64  tff(c_7000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_6996])).
% 9.69/3.64  tff(c_7001, plain, (k1_relat_1(k5_relat_1('#skF_2', k2_funct_1('#skF_2')))!=k1_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_6850])).
% 9.69/3.64  tff(c_7005, plain, (k1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))!=k1_relat_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_42, c_7001])).
% 9.69/3.64  tff(c_7008, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_24, c_7005])).
% 9.69/3.64  tff(c_7010, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2')))), inference(splitRight, [status(thm)], [c_6772])).
% 9.69/3.64  tff(c_279, plain, (![B_85]: (r1_tarski('#skF_1', B_85) | ~r1_tarski(k1_relat_1('#skF_2'), B_85))), inference(superposition, [status(thm), theory('equality')], [c_8, c_261])).
% 9.69/3.64  tff(c_723, plain, (![B_171]: (r1_tarski('#skF_1', k10_relat_1('#skF_2', B_171)) | ~r1_tarski(k2_relat_1('#skF_2'), B_171) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_706, c_279])).
% 9.69/3.64  tff(c_753, plain, (![B_171]: (r1_tarski('#skF_1', k10_relat_1('#skF_2', B_171)) | ~r1_tarski(k2_relat_1('#skF_2'), B_171))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_723])).
% 9.69/3.64  tff(c_7099, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k1_relat_1(k2_funct_1('#skF_2'))))), inference(resolution, [status(thm)], [c_7010, c_753])).
% 9.69/3.64  tff(c_7164, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_444, c_7099])).
% 9.69/3.64  tff(c_7200, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1848, c_52, c_50, c_46, c_7164])).
% 9.69/3.64  tff(c_32, plain, (![B_28, A_27]: (k9_relat_1(B_28, k10_relat_1(B_28, A_27))=A_27 | ~r1_tarski(A_27, k2_relat_1(B_28)) | ~v1_funct_1(B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.69/3.64  tff(c_7281, plain, (k9_relat_1(k2_funct_1('#skF_2'), k10_relat_1(k2_funct_1('#skF_2'), '#skF_1'))='#skF_1' | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_7200, c_32])).
% 9.69/3.64  tff(c_7325, plain, (k9_relat_1(k2_funct_1('#skF_2'), k10_relat_1(k2_funct_1('#skF_2'), '#skF_1'))='#skF_1' | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1848, c_7281])).
% 9.69/3.64  tff(c_9459, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_7325])).
% 9.69/3.64  tff(c_9462, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_9459])).
% 9.69/3.64  tff(c_9466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_9462])).
% 9.69/3.64  tff(c_9467, plain, (k9_relat_1(k2_funct_1('#skF_2'), k10_relat_1(k2_funct_1('#skF_2'), '#skF_1'))='#skF_1'), inference(splitRight, [status(thm)], [c_7325])).
% 9.69/3.64  tff(c_36, plain, (![B_32, A_31]: (k9_relat_1(k2_funct_1(B_32), A_31)=k10_relat_1(B_32, A_31) | ~v2_funct_1(B_32) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.69/3.64  tff(c_9478, plain, (k10_relat_1('#skF_2', k10_relat_1(k2_funct_1('#skF_2'), '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9467, c_36])).
% 9.69/3.64  tff(c_9492, plain, (k10_relat_1('#skF_2', k10_relat_1(k2_funct_1('#skF_2'), '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_9478])).
% 9.69/3.64  tff(c_9589, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_34, c_9492])).
% 9.69/3.64  tff(c_9618, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_9589])).
% 9.69/3.64  tff(c_9620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_9618])).
% 9.69/3.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.69/3.64  
% 9.69/3.64  Inference rules
% 9.69/3.64  ----------------------
% 9.69/3.64  #Ref     : 0
% 9.69/3.64  #Sup     : 2573
% 9.69/3.64  #Fact    : 0
% 9.69/3.64  #Define  : 0
% 9.69/3.64  #Split   : 22
% 9.69/3.64  #Chain   : 0
% 9.69/3.64  #Close   : 0
% 9.69/3.64  
% 9.69/3.64  Ordering : KBO
% 9.69/3.64  
% 9.69/3.64  Simplification rules
% 9.69/3.64  ----------------------
% 9.69/3.64  #Subsume      : 637
% 9.69/3.64  #Demod        : 260
% 9.69/3.64  #Tautology    : 92
% 9.69/3.64  #SimpNegUnit  : 2
% 9.69/3.64  #BackRed      : 0
% 9.69/3.64  
% 9.69/3.64  #Partial instantiations: 0
% 9.69/3.64  #Strategies tried      : 1
% 9.69/3.64  
% 9.69/3.64  Timing (in seconds)
% 9.69/3.64  ----------------------
% 9.69/3.64  Preprocessing        : 0.40
% 9.69/3.65  Parsing              : 0.23
% 9.69/3.65  CNF conversion       : 0.03
% 9.69/3.65  Main loop            : 2.40
% 9.69/3.65  Inferencing          : 0.51
% 9.69/3.65  Reduction            : 0.56
% 9.69/3.65  Demodulation         : 0.36
% 9.69/3.65  BG Simplification    : 0.07
% 9.69/3.65  Subsumption          : 1.10
% 9.69/3.65  Abstraction          : 0.09
% 9.69/3.65  MUC search           : 0.00
% 9.69/3.65  Cooper               : 0.00
% 9.69/3.65  Total                : 2.86
% 9.69/3.65  Index Insertion      : 0.00
% 9.69/3.65  Index Deletion       : 0.00
% 9.69/3.65  Index Matching       : 0.00
% 9.69/3.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
