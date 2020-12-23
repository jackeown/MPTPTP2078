%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:46 EST 2020

% Result     : Theorem 10.55s
% Output     : CNFRefutation 10.55s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 367 expanded)
%              Number of leaves         :   20 ( 131 expanded)
%              Depth                    :   22
%              Number of atoms          :  202 (1153 expanded)
%              Number of equality atoms :   17 (  87 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( ( r1_tarski(B,C)
                    & r1_xboole_0(D,C) )
                 => r1_tarski(B,k3_subset_1(A,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,k3_subset_1(A,C))
          <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_64,plain,(
    ! [B_38,A_39,C_40] :
      ( r1_tarski(B_38,k3_subset_1(A_39,C_40))
      | ~ r1_xboole_0(B_38,C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(A_39))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_67,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_24])).

tff(c_70,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_67])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    ! [B_17,A_16,C_19] :
      ( r1_xboole_0(B_17,k3_subset_1(A_16,C_19))
      | ~ r1_tarski(B_17,C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k3_subset_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_8,C_11,B_9] :
      ( r1_tarski(k3_subset_1(A_8,C_11),k3_subset_1(A_8,B_9))
      | ~ r1_tarski(B_9,C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_128,plain,(
    ! [A_54,C_55,B_56] :
      ( r1_tarski(k3_subset_1(A_54,C_55),k3_subset_1(A_54,B_56))
      | ~ r1_tarski(B_56,C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(A_54))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [B_13,C_15,A_12] :
      ( r1_xboole_0(B_13,C_15)
      | ~ r1_tarski(B_13,k3_subset_1(A_12,C_15))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_284,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_xboole_0(k3_subset_1(A_71,C_72),B_73)
      | ~ m1_subset_1(k3_subset_1(A_71,C_72),k1_zfmisc_1(A_71))
      | ~ r1_tarski(B_73,C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(A_71))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_71)) ) ),
    inference(resolution,[status(thm)],[c_128,c_16])).

tff(c_375,plain,(
    ! [A_81,B_82,B_83] :
      ( r1_xboole_0(k3_subset_1(A_81,B_82),B_83)
      | ~ r1_tarski(B_83,B_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_81))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(resolution,[status(thm)],[c_10,c_284])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = A_4
      | ~ r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_437,plain,(
    ! [A_89,B_90,B_91] :
      ( k4_xboole_0(k3_subset_1(A_89,B_90),B_91) = k3_subset_1(A_89,B_90)
      | ~ r1_tarski(B_91,B_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_89))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(resolution,[status(thm)],[c_375,c_6])).

tff(c_1859,plain,(
    ! [A_222,B_223,B_224] :
      ( k4_xboole_0(k3_subset_1(A_222,B_223),k3_subset_1(A_222,B_224)) = k3_subset_1(A_222,B_223)
      | ~ r1_tarski(k3_subset_1(A_222,B_224),B_223)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(A_222))
      | ~ m1_subset_1(B_224,k1_zfmisc_1(A_222)) ) ),
    inference(resolution,[status(thm)],[c_10,c_437])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r1_xboole_0(A_4,B_5)
      | k4_xboole_0(A_4,B_5) != A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ! [B_41,C_42,A_43] :
      ( r1_tarski(B_41,C_42)
      | ~ r1_xboole_0(B_41,k3_subset_1(A_43,C_42))
      | ~ m1_subset_1(C_42,k1_zfmisc_1(A_43))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_95,plain,(
    ! [A_50,C_51,A_52] :
      ( r1_tarski(A_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_52))
      | ~ m1_subset_1(A_50,k1_zfmisc_1(A_52))
      | k4_xboole_0(A_50,k3_subset_1(A_52,C_51)) != A_50 ) ),
    inference(resolution,[status(thm)],[c_8,c_71])).

tff(c_134,plain,(
    ! [A_57] :
      ( r1_tarski(A_57,'#skF_3')
      | ~ m1_subset_1(A_57,k1_zfmisc_1('#skF_1'))
      | k4_xboole_0(A_57,k3_subset_1('#skF_1','#skF_3')) != A_57 ) ),
    inference(resolution,[status(thm)],[c_32,c_95])).

tff(c_148,plain,(
    ! [B_7] :
      ( r1_tarski(k3_subset_1('#skF_1',B_7),'#skF_3')
      | k4_xboole_0(k3_subset_1('#skF_1',B_7),k3_subset_1('#skF_1','#skF_3')) != k3_subset_1('#skF_1',B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_10,c_134])).

tff(c_1878,plain,(
    ! [B_223] :
      ( r1_tarski(k3_subset_1('#skF_1',B_223),'#skF_3')
      | ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),B_223)
      | ~ m1_subset_1(B_223,k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1859,c_148])).

tff(c_1988,plain,(
    ! [B_226] :
      ( r1_tarski(k3_subset_1('#skF_1',B_226),'#skF_3')
      | ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),B_226)
      | ~ m1_subset_1(B_226,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1878])).

tff(c_1994,plain,(
    ! [B_9] :
      ( r1_tarski(k3_subset_1('#skF_1',k3_subset_1('#skF_1',B_9)),'#skF_3')
      | ~ m1_subset_1(k3_subset_1('#skF_1',B_9),k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski(B_9,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_9,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_1988])).

tff(c_2391,plain,(
    ! [B_248] :
      ( r1_tarski(k3_subset_1('#skF_1',k3_subset_1('#skF_1',B_248)),'#skF_3')
      | ~ m1_subset_1(k3_subset_1('#skF_1',B_248),k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski(B_248,'#skF_3')
      | ~ m1_subset_1(B_248,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1994])).

tff(c_81,plain,(
    ! [B_44,A_45,C_46] :
      ( r1_xboole_0(B_44,k3_subset_1(A_45,C_46))
      | ~ r1_tarski(B_44,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_45))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_186,plain,(
    ! [B_62,A_63,C_64] :
      ( k4_xboole_0(B_62,k3_subset_1(A_63,C_64)) = B_62
      | ~ r1_tarski(B_62,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_63))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63)) ) ),
    inference(resolution,[status(thm)],[c_81,c_6])).

tff(c_260,plain,(
    ! [B_70] :
      ( k4_xboole_0(B_70,k3_subset_1('#skF_1','#skF_3')) = B_70
      | ~ r1_tarski(B_70,'#skF_3')
      | ~ m1_subset_1(B_70,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_32,c_186])).

tff(c_274,plain,(
    ! [B_7] :
      ( k4_xboole_0(k3_subset_1('#skF_1',B_7),k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',B_7)
      | ~ r1_tarski(k3_subset_1('#skF_1',B_7),'#skF_3')
      | ~ m1_subset_1(B_7,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_10,c_260])).

tff(c_18,plain,(
    ! [B_13,A_12,C_15] :
      ( r1_tarski(B_13,k3_subset_1(A_12,C_15))
      | ~ r1_xboole_0(B_13,C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_173,plain,(
    ! [B_59,C_60,A_61] :
      ( r1_tarski(B_59,C_60)
      | ~ r1_tarski(k3_subset_1(A_61,C_60),k3_subset_1(A_61,B_59))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(A_61))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_223,plain,(
    ! [C_66,C_67,A_68] :
      ( r1_tarski(C_66,C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(A_68))
      | ~ r1_xboole_0(k3_subset_1(A_68,C_67),C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(A_68))
      | ~ m1_subset_1(k3_subset_1(A_68,C_67),k1_zfmisc_1(A_68)) ) ),
    inference(resolution,[status(thm)],[c_18,c_173])).

tff(c_590,plain,(
    ! [B_102,C_103,A_104] :
      ( r1_tarski(B_102,C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(A_104))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_104))
      | ~ m1_subset_1(k3_subset_1(A_104,C_103),k1_zfmisc_1(A_104))
      | k4_xboole_0(k3_subset_1(A_104,C_103),B_102) != k3_subset_1(A_104,C_103) ) ),
    inference(resolution,[status(thm)],[c_8,c_223])).

tff(c_1491,plain,(
    ! [A_187,B_188,C_189] :
      ( r1_tarski(k3_subset_1(A_187,B_188),C_189)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(A_187))
      | ~ m1_subset_1(k3_subset_1(A_187,C_189),k1_zfmisc_1(A_187))
      | k4_xboole_0(k3_subset_1(A_187,C_189),k3_subset_1(A_187,B_188)) != k3_subset_1(A_187,C_189)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(A_187)) ) ),
    inference(resolution,[status(thm)],[c_10,c_590])).

tff(c_2125,plain,(
    ! [A_234,B_235,B_236] :
      ( r1_tarski(k3_subset_1(A_234,B_235),B_236)
      | k4_xboole_0(k3_subset_1(A_234,B_236),k3_subset_1(A_234,B_235)) != k3_subset_1(A_234,B_236)
      | ~ m1_subset_1(B_235,k1_zfmisc_1(A_234))
      | ~ m1_subset_1(B_236,k1_zfmisc_1(A_234)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1491])).

tff(c_2135,plain,(
    ! [B_7] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),B_7)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski(k3_subset_1('#skF_1',B_7),'#skF_3')
      | ~ m1_subset_1(B_7,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_2125])).

tff(c_2154,plain,(
    ! [B_7] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),B_7)
      | ~ r1_tarski(k3_subset_1('#skF_1',B_7),'#skF_3')
      | ~ m1_subset_1(B_7,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2135])).

tff(c_3161,plain,(
    ! [B_298] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1',B_298))
      | ~ m1_subset_1(k3_subset_1('#skF_1',B_298),k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski(B_298,'#skF_3')
      | ~ m1_subset_1(B_298,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_2391,c_2154])).

tff(c_3231,plain,(
    ! [B_298] :
      ( r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),B_298)
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(k3_subset_1('#skF_1',B_298),k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski(B_298,'#skF_3')
      | ~ m1_subset_1(B_298,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_3161,c_16])).

tff(c_14784,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_3231])).

tff(c_14787,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_14784])).

tff(c_14791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14787])).

tff(c_14793,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_3231])).

tff(c_26,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_447,plain,(
    ! [B_90] :
      ( k4_xboole_0(k3_subset_1('#skF_1',B_90),'#skF_4') = k3_subset_1('#skF_1',B_90)
      | ~ r1_tarski('#skF_4',B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_30,c_437])).

tff(c_15255,plain,
    ( k4_xboole_0(k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')),'#skF_4') = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_14793,c_447])).

tff(c_15793,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_15255])).

tff(c_15826,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_15793])).

tff(c_15860,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_26,c_15826])).

tff(c_15861,plain,(
    k4_xboole_0(k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')),'#skF_4') = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_15255])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_tarski(A_1,k4_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16131,plain,(
    ! [A_715] :
      ( r1_xboole_0(A_715,'#skF_4')
      | ~ r1_tarski(A_715,k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15861,c_2])).

tff(c_16223,plain,(
    ! [B_13] :
      ( r1_xboole_0(B_13,'#skF_4')
      | ~ r1_xboole_0(B_13,k3_subset_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_13,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_16131])).

tff(c_16414,plain,(
    ! [B_716] :
      ( r1_xboole_0(B_716,'#skF_4')
      | ~ r1_xboole_0(B_716,k3_subset_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(B_716,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14793,c_16223])).

tff(c_16485,plain,(
    ! [B_17] :
      ( r1_xboole_0(B_17,'#skF_4')
      | ~ r1_tarski(B_17,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_17,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_20,c_16414])).

tff(c_16579,plain,(
    ! [B_718] :
      ( r1_xboole_0(B_718,'#skF_4')
      | ~ r1_tarski(B_718,'#skF_3')
      | ~ m1_subset_1(B_718,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_16485])).

tff(c_16595,plain,
    ( r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_16579])).

tff(c_16607,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_16595])).

tff(c_16609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_16607])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:01:40 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.55/4.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.55/4.49  
% 10.55/4.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.55/4.49  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.55/4.49  
% 10.55/4.49  %Foreground sorts:
% 10.55/4.49  
% 10.55/4.49  
% 10.55/4.49  %Background operators:
% 10.55/4.49  
% 10.55/4.49  
% 10.55/4.49  %Foreground operators:
% 10.55/4.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.55/4.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.55/4.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.55/4.49  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.55/4.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.55/4.49  tff('#skF_2', type, '#skF_2': $i).
% 10.55/4.49  tff('#skF_3', type, '#skF_3': $i).
% 10.55/4.49  tff('#skF_1', type, '#skF_1': $i).
% 10.55/4.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.55/4.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.55/4.49  tff('#skF_4', type, '#skF_4': $i).
% 10.55/4.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.55/4.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.55/4.49  
% 10.55/4.51  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_subset_1)).
% 10.55/4.51  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 10.55/4.51  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 10.55/4.51  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 10.55/4.51  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 10.55/4.51  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 10.55/4.51  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 10.55/4.51  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.55/4.51  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.55/4.51  tff(c_64, plain, (![B_38, A_39, C_40]: (r1_tarski(B_38, k3_subset_1(A_39, C_40)) | ~r1_xboole_0(B_38, C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(A_39)) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.55/4.51  tff(c_24, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.55/4.51  tff(c_67, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_24])).
% 10.55/4.51  tff(c_70, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_67])).
% 10.55/4.51  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.55/4.51  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.55/4.51  tff(c_20, plain, (![B_17, A_16, C_19]: (r1_xboole_0(B_17, k3_subset_1(A_16, C_19)) | ~r1_tarski(B_17, C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.55/4.51  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(k3_subset_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.55/4.51  tff(c_14, plain, (![A_8, C_11, B_9]: (r1_tarski(k3_subset_1(A_8, C_11), k3_subset_1(A_8, B_9)) | ~r1_tarski(B_9, C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.55/4.51  tff(c_128, plain, (![A_54, C_55, B_56]: (r1_tarski(k3_subset_1(A_54, C_55), k3_subset_1(A_54, B_56)) | ~r1_tarski(B_56, C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(A_54)) | ~m1_subset_1(B_56, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.55/4.51  tff(c_16, plain, (![B_13, C_15, A_12]: (r1_xboole_0(B_13, C_15) | ~r1_tarski(B_13, k3_subset_1(A_12, C_15)) | ~m1_subset_1(C_15, k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.55/4.51  tff(c_284, plain, (![A_71, C_72, B_73]: (r1_xboole_0(k3_subset_1(A_71, C_72), B_73) | ~m1_subset_1(k3_subset_1(A_71, C_72), k1_zfmisc_1(A_71)) | ~r1_tarski(B_73, C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(A_71)) | ~m1_subset_1(B_73, k1_zfmisc_1(A_71)))), inference(resolution, [status(thm)], [c_128, c_16])).
% 10.55/4.51  tff(c_375, plain, (![A_81, B_82, B_83]: (r1_xboole_0(k3_subset_1(A_81, B_82), B_83) | ~r1_tarski(B_83, B_82) | ~m1_subset_1(B_83, k1_zfmisc_1(A_81)) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(resolution, [status(thm)], [c_10, c_284])).
% 10.55/4.51  tff(c_6, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=A_4 | ~r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.55/4.51  tff(c_437, plain, (![A_89, B_90, B_91]: (k4_xboole_0(k3_subset_1(A_89, B_90), B_91)=k3_subset_1(A_89, B_90) | ~r1_tarski(B_91, B_90) | ~m1_subset_1(B_91, k1_zfmisc_1(A_89)) | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(resolution, [status(thm)], [c_375, c_6])).
% 10.55/4.51  tff(c_1859, plain, (![A_222, B_223, B_224]: (k4_xboole_0(k3_subset_1(A_222, B_223), k3_subset_1(A_222, B_224))=k3_subset_1(A_222, B_223) | ~r1_tarski(k3_subset_1(A_222, B_224), B_223) | ~m1_subset_1(B_223, k1_zfmisc_1(A_222)) | ~m1_subset_1(B_224, k1_zfmisc_1(A_222)))), inference(resolution, [status(thm)], [c_10, c_437])).
% 10.55/4.51  tff(c_8, plain, (![A_4, B_5]: (r1_xboole_0(A_4, B_5) | k4_xboole_0(A_4, B_5)!=A_4)), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.55/4.51  tff(c_71, plain, (![B_41, C_42, A_43]: (r1_tarski(B_41, C_42) | ~r1_xboole_0(B_41, k3_subset_1(A_43, C_42)) | ~m1_subset_1(C_42, k1_zfmisc_1(A_43)) | ~m1_subset_1(B_41, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.55/4.51  tff(c_95, plain, (![A_50, C_51, A_52]: (r1_tarski(A_50, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(A_52)) | ~m1_subset_1(A_50, k1_zfmisc_1(A_52)) | k4_xboole_0(A_50, k3_subset_1(A_52, C_51))!=A_50)), inference(resolution, [status(thm)], [c_8, c_71])).
% 10.55/4.51  tff(c_134, plain, (![A_57]: (r1_tarski(A_57, '#skF_3') | ~m1_subset_1(A_57, k1_zfmisc_1('#skF_1')) | k4_xboole_0(A_57, k3_subset_1('#skF_1', '#skF_3'))!=A_57)), inference(resolution, [status(thm)], [c_32, c_95])).
% 10.55/4.51  tff(c_148, plain, (![B_7]: (r1_tarski(k3_subset_1('#skF_1', B_7), '#skF_3') | k4_xboole_0(k3_subset_1('#skF_1', B_7), k3_subset_1('#skF_1', '#skF_3'))!=k3_subset_1('#skF_1', B_7) | ~m1_subset_1(B_7, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_134])).
% 10.55/4.51  tff(c_1878, plain, (![B_223]: (r1_tarski(k3_subset_1('#skF_1', B_223), '#skF_3') | ~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), B_223) | ~m1_subset_1(B_223, k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1859, c_148])).
% 10.55/4.51  tff(c_1988, plain, (![B_226]: (r1_tarski(k3_subset_1('#skF_1', B_226), '#skF_3') | ~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), B_226) | ~m1_subset_1(B_226, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1878])).
% 10.55/4.51  tff(c_1994, plain, (![B_9]: (r1_tarski(k3_subset_1('#skF_1', k3_subset_1('#skF_1', B_9)), '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_1', B_9), k1_zfmisc_1('#skF_1')) | ~r1_tarski(B_9, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_9, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_1988])).
% 10.55/4.51  tff(c_2391, plain, (![B_248]: (r1_tarski(k3_subset_1('#skF_1', k3_subset_1('#skF_1', B_248)), '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_1', B_248), k1_zfmisc_1('#skF_1')) | ~r1_tarski(B_248, '#skF_3') | ~m1_subset_1(B_248, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1994])).
% 10.55/4.51  tff(c_81, plain, (![B_44, A_45, C_46]: (r1_xboole_0(B_44, k3_subset_1(A_45, C_46)) | ~r1_tarski(B_44, C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(A_45)) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.55/4.51  tff(c_186, plain, (![B_62, A_63, C_64]: (k4_xboole_0(B_62, k3_subset_1(A_63, C_64))=B_62 | ~r1_tarski(B_62, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(A_63)) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)))), inference(resolution, [status(thm)], [c_81, c_6])).
% 10.55/4.51  tff(c_260, plain, (![B_70]: (k4_xboole_0(B_70, k3_subset_1('#skF_1', '#skF_3'))=B_70 | ~r1_tarski(B_70, '#skF_3') | ~m1_subset_1(B_70, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_32, c_186])).
% 10.55/4.51  tff(c_274, plain, (![B_7]: (k4_xboole_0(k3_subset_1('#skF_1', B_7), k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', B_7) | ~r1_tarski(k3_subset_1('#skF_1', B_7), '#skF_3') | ~m1_subset_1(B_7, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_260])).
% 10.55/4.51  tff(c_18, plain, (![B_13, A_12, C_15]: (r1_tarski(B_13, k3_subset_1(A_12, C_15)) | ~r1_xboole_0(B_13, C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.55/4.51  tff(c_173, plain, (![B_59, C_60, A_61]: (r1_tarski(B_59, C_60) | ~r1_tarski(k3_subset_1(A_61, C_60), k3_subset_1(A_61, B_59)) | ~m1_subset_1(C_60, k1_zfmisc_1(A_61)) | ~m1_subset_1(B_59, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.55/4.51  tff(c_223, plain, (![C_66, C_67, A_68]: (r1_tarski(C_66, C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(A_68)) | ~r1_xboole_0(k3_subset_1(A_68, C_67), C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(A_68)) | ~m1_subset_1(k3_subset_1(A_68, C_67), k1_zfmisc_1(A_68)))), inference(resolution, [status(thm)], [c_18, c_173])).
% 10.55/4.51  tff(c_590, plain, (![B_102, C_103, A_104]: (r1_tarski(B_102, C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(A_104)) | ~m1_subset_1(B_102, k1_zfmisc_1(A_104)) | ~m1_subset_1(k3_subset_1(A_104, C_103), k1_zfmisc_1(A_104)) | k4_xboole_0(k3_subset_1(A_104, C_103), B_102)!=k3_subset_1(A_104, C_103))), inference(resolution, [status(thm)], [c_8, c_223])).
% 10.55/4.51  tff(c_1491, plain, (![A_187, B_188, C_189]: (r1_tarski(k3_subset_1(A_187, B_188), C_189) | ~m1_subset_1(C_189, k1_zfmisc_1(A_187)) | ~m1_subset_1(k3_subset_1(A_187, C_189), k1_zfmisc_1(A_187)) | k4_xboole_0(k3_subset_1(A_187, C_189), k3_subset_1(A_187, B_188))!=k3_subset_1(A_187, C_189) | ~m1_subset_1(B_188, k1_zfmisc_1(A_187)))), inference(resolution, [status(thm)], [c_10, c_590])).
% 10.55/4.51  tff(c_2125, plain, (![A_234, B_235, B_236]: (r1_tarski(k3_subset_1(A_234, B_235), B_236) | k4_xboole_0(k3_subset_1(A_234, B_236), k3_subset_1(A_234, B_235))!=k3_subset_1(A_234, B_236) | ~m1_subset_1(B_235, k1_zfmisc_1(A_234)) | ~m1_subset_1(B_236, k1_zfmisc_1(A_234)))), inference(resolution, [status(thm)], [c_10, c_1491])).
% 10.55/4.51  tff(c_2135, plain, (![B_7]: (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), B_7) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~r1_tarski(k3_subset_1('#skF_1', B_7), '#skF_3') | ~m1_subset_1(B_7, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_274, c_2125])).
% 10.55/4.51  tff(c_2154, plain, (![B_7]: (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), B_7) | ~r1_tarski(k3_subset_1('#skF_1', B_7), '#skF_3') | ~m1_subset_1(B_7, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2135])).
% 10.55/4.51  tff(c_3161, plain, (![B_298]: (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', B_298)) | ~m1_subset_1(k3_subset_1('#skF_1', B_298), k1_zfmisc_1('#skF_1')) | ~r1_tarski(B_298, '#skF_3') | ~m1_subset_1(B_298, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_2391, c_2154])).
% 10.55/4.51  tff(c_3231, plain, (![B_298]: (r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), B_298) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', B_298), k1_zfmisc_1('#skF_1')) | ~r1_tarski(B_298, '#skF_3') | ~m1_subset_1(B_298, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_3161, c_16])).
% 10.55/4.51  tff(c_14784, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_3231])).
% 10.55/4.51  tff(c_14787, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_14784])).
% 10.55/4.51  tff(c_14791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_14787])).
% 10.55/4.51  tff(c_14793, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_3231])).
% 10.55/4.51  tff(c_26, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.55/4.51  tff(c_447, plain, (![B_90]: (k4_xboole_0(k3_subset_1('#skF_1', B_90), '#skF_4')=k3_subset_1('#skF_1', B_90) | ~r1_tarski('#skF_4', B_90) | ~m1_subset_1(B_90, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_30, c_437])).
% 10.55/4.51  tff(c_15255, plain, (k4_xboole_0(k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3')), '#skF_4')=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_4', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_14793, c_447])).
% 10.55/4.51  tff(c_15793, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_15255])).
% 10.55/4.51  tff(c_15826, plain, (~r1_xboole_0('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_15793])).
% 10.55/4.51  tff(c_15860, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_26, c_15826])).
% 10.55/4.51  tff(c_15861, plain, (k4_xboole_0(k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3')), '#skF_4')=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_15255])).
% 10.55/4.51  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_tarski(A_1, k4_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.55/4.51  tff(c_16131, plain, (![A_715]: (r1_xboole_0(A_715, '#skF_4') | ~r1_tarski(A_715, k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_15861, c_2])).
% 10.55/4.51  tff(c_16223, plain, (![B_13]: (r1_xboole_0(B_13, '#skF_4') | ~r1_xboole_0(B_13, k3_subset_1('#skF_1', '#skF_3')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_13, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_16131])).
% 10.55/4.51  tff(c_16414, plain, (![B_716]: (r1_xboole_0(B_716, '#skF_4') | ~r1_xboole_0(B_716, k3_subset_1('#skF_1', '#skF_3')) | ~m1_subset_1(B_716, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_14793, c_16223])).
% 10.55/4.51  tff(c_16485, plain, (![B_17]: (r1_xboole_0(B_17, '#skF_4') | ~r1_tarski(B_17, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_17, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_16414])).
% 10.55/4.51  tff(c_16579, plain, (![B_718]: (r1_xboole_0(B_718, '#skF_4') | ~r1_tarski(B_718, '#skF_3') | ~m1_subset_1(B_718, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_16485])).
% 10.55/4.51  tff(c_16595, plain, (r1_xboole_0('#skF_2', '#skF_4') | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_16579])).
% 10.55/4.51  tff(c_16607, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_16595])).
% 10.55/4.51  tff(c_16609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_16607])).
% 10.55/4.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.55/4.51  
% 10.55/4.51  Inference rules
% 10.55/4.51  ----------------------
% 10.55/4.51  #Ref     : 0
% 10.55/4.51  #Sup     : 3459
% 10.55/4.51  #Fact    : 0
% 10.55/4.51  #Define  : 0
% 10.55/4.51  #Split   : 43
% 10.55/4.51  #Chain   : 0
% 10.55/4.51  #Close   : 0
% 10.55/4.51  
% 10.55/4.51  Ordering : KBO
% 10.55/4.51  
% 10.55/4.51  Simplification rules
% 10.55/4.51  ----------------------
% 10.55/4.51  #Subsume      : 1790
% 10.55/4.51  #Demod        : 1727
% 10.55/4.51  #Tautology    : 337
% 10.55/4.51  #SimpNegUnit  : 135
% 10.55/4.51  #BackRed      : 0
% 10.55/4.51  
% 10.55/4.51  #Partial instantiations: 0
% 10.55/4.51  #Strategies tried      : 1
% 10.55/4.51  
% 10.55/4.51  Timing (in seconds)
% 10.55/4.51  ----------------------
% 10.55/4.51  Preprocessing        : 0.30
% 10.55/4.51  Parsing              : 0.17
% 10.55/4.51  CNF conversion       : 0.02
% 10.55/4.51  Main loop            : 3.38
% 10.55/4.51  Inferencing          : 0.79
% 10.55/4.51  Reduction            : 0.83
% 10.55/4.51  Demodulation         : 0.50
% 10.55/4.51  BG Simplification    : 0.06
% 10.55/4.51  Subsumption          : 1.51
% 10.55/4.51  Abstraction          : 0.10
% 10.55/4.51  MUC search           : 0.00
% 10.55/4.51  Cooper               : 0.00
% 10.55/4.51  Total                : 3.72
% 10.55/4.51  Index Insertion      : 0.00
% 10.55/4.51  Index Deletion       : 0.00
% 10.55/4.51  Index Matching       : 0.00
% 10.55/4.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
