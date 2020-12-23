%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:57 EST 2020

% Result     : Theorem 21.97s
% Output     : CNFRefutation 21.97s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 808 expanded)
%              Number of leaves         :   41 ( 282 expanded)
%              Depth                    :   20
%              Number of atoms          :  259 (1444 expanded)
%              Number of equality atoms :   31 ( 184 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_124,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,k3_subset_1(A,C))
             => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_105,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_85,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_75,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_43,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_14,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_652,plain,(
    ! [A_122,B_123,C_124] :
      ( r1_tarski(A_122,B_123)
      | ~ r1_xboole_0(A_122,C_124)
      | ~ r1_tarski(A_122,k2_xboole_0(B_123,C_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_712,plain,(
    ! [A_125,B_126] :
      ( r1_tarski(A_125,A_125)
      | ~ r1_xboole_0(A_125,B_126) ) ),
    inference(resolution,[status(thm)],[c_18,c_652])).

tff(c_727,plain,(
    ! [A_14] : r1_tarski(A_14,A_14) ),
    inference(resolution,[status(thm)],[c_14,c_712])).

tff(c_56,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_192,plain,(
    ! [A_84,B_85] :
      ( k4_xboole_0(A_84,B_85) = k3_subset_1(A_84,B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_205,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_192])).

tff(c_20,plain,(
    ! [A_20,C_22,B_21] :
      ( r1_xboole_0(A_20,k4_xboole_0(C_22,B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_64873,plain,(
    ! [A_2047,C_2048,B_2049,D_2050] :
      ( r1_xboole_0(A_2047,C_2048)
      | ~ r1_xboole_0(B_2049,D_2050)
      | ~ r1_tarski(C_2048,D_2050)
      | ~ r1_tarski(A_2047,B_2049) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_66411,plain,(
    ! [A_2117,C_2118,A_2116,C_2114,B_2115] :
      ( r1_xboole_0(A_2117,C_2118)
      | ~ r1_tarski(C_2118,k4_xboole_0(C_2114,B_2115))
      | ~ r1_tarski(A_2117,A_2116)
      | ~ r1_tarski(A_2116,B_2115) ) ),
    inference(resolution,[status(thm)],[c_20,c_64873])).

tff(c_66531,plain,(
    ! [A_2122,C_2123,A_2124] :
      ( r1_xboole_0(A_2122,C_2123)
      | ~ r1_tarski(C_2123,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_2122,A_2124)
      | ~ r1_tarski(A_2124,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_66411])).

tff(c_66573,plain,(
    ! [A_2125,A_2126] :
      ( r1_xboole_0(A_2125,'#skF_2')
      | ~ r1_tarski(A_2125,A_2126)
      | ~ r1_tarski(A_2126,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_66531])).

tff(c_66648,plain,(
    ! [A_2127] :
      ( r1_xboole_0(A_2127,'#skF_2')
      | ~ r1_tarski(A_2127,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_727,c_66573])).

tff(c_60,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_204,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_192])).

tff(c_546,plain,(
    ! [A_117,B_118,C_119] :
      ( r1_tarski(A_117,k4_xboole_0(B_118,C_119))
      | ~ r1_xboole_0(A_117,C_119)
      | ~ r1_tarski(A_117,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_871,plain,(
    ! [A_137] :
      ( r1_tarski(A_137,k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_xboole_0(A_137,'#skF_2')
      | ~ r1_tarski(A_137,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_546])).

tff(c_54,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_894,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_871,c_54])).

tff(c_895,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_894])).

tff(c_48,plain,(
    ! [A_41] : ~ v1_xboole_0(k1_zfmisc_1(A_41)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36,plain,(
    ! [A_36] : r1_tarski(k1_tarski(A_36),k1_zfmisc_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_73,plain,(
    ! [A_54,B_55] :
      ( k2_xboole_0(A_54,B_55) = B_55
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_87,plain,(
    ! [A_36] : k2_xboole_0(k1_tarski(A_36),k1_zfmisc_1(A_36)) = k1_zfmisc_1(A_36) ),
    inference(resolution,[status(thm)],[c_36,c_73])).

tff(c_176,plain,(
    ! [A_82,B_83] : k2_enumset1(A_82,A_82,A_82,B_83) = k2_tarski(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    ! [A_28] : k2_enumset1(A_28,A_28,A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_206,plain,(
    ! [B_86] : k2_tarski(B_86,B_86) = k1_tarski(B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_26])).

tff(c_140,plain,(
    ! [A_66,C_67,B_68] :
      ( r2_hidden(A_66,C_67)
      | ~ r1_tarski(k2_tarski(A_66,B_68),C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_145,plain,(
    ! [A_66,B_68,B_19] : r2_hidden(A_66,k2_xboole_0(k2_tarski(A_66,B_68),B_19)) ),
    inference(resolution,[status(thm)],[c_18,c_140])).

tff(c_242,plain,(
    ! [B_87,B_88] : r2_hidden(B_87,k2_xboole_0(k1_tarski(B_87),B_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_145])).

tff(c_250,plain,(
    ! [A_89] : r2_hidden(A_89,k1_zfmisc_1(A_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_242])).

tff(c_38,plain,(
    ! [B_38,A_37] :
      ( m1_subset_1(B_38,A_37)
      | ~ r2_hidden(B_38,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_253,plain,(
    ! [A_89] :
      ( m1_subset_1(A_89,k1_zfmisc_1(A_89))
      | v1_xboole_0(k1_zfmisc_1(A_89)) ) ),
    inference(resolution,[status(thm)],[c_250,c_38])).

tff(c_256,plain,(
    ! [A_89] : m1_subset_1(A_89,k1_zfmisc_1(A_89)) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_253])).

tff(c_8,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_257,plain,(
    ! [A_90] : m1_subset_1(A_90,k1_zfmisc_1(A_90)) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_253])).

tff(c_46,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = k3_subset_1(A_39,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_264,plain,(
    ! [A_90] : k4_xboole_0(A_90,A_90) = k3_subset_1(A_90,A_90) ),
    inference(resolution,[status(thm)],[c_257,c_46])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_729,plain,(
    ! [A_127] : r1_tarski(A_127,A_127) ),
    inference(resolution,[status(thm)],[c_14,c_712])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_766,plain,(
    ! [A_129] : k2_xboole_0(A_129,A_129) = A_129 ),
    inference(resolution,[status(thm)],[c_729,c_6])).

tff(c_813,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_766])).

tff(c_831,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k3_subset_1(B_2,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_813])).

tff(c_853,plain,(
    ! [A_134,C_135,B_136] :
      ( r1_tarski(k5_xboole_0(A_134,C_135),B_136)
      | ~ r1_tarski(C_135,B_136)
      | ~ r1_tarski(A_134,B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17] :
      ( r1_tarski(A_15,B_16)
      | ~ r1_xboole_0(A_15,C_17)
      | ~ r1_tarski(A_15,k2_xboole_0(B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3334,plain,(
    ! [A_254,C_255,B_256,C_257] :
      ( r1_tarski(k5_xboole_0(A_254,C_255),B_256)
      | ~ r1_xboole_0(k5_xboole_0(A_254,C_255),C_257)
      | ~ r1_tarski(C_255,k2_xboole_0(B_256,C_257))
      | ~ r1_tarski(A_254,k2_xboole_0(B_256,C_257)) ) ),
    inference(resolution,[status(thm)],[c_853,c_16])).

tff(c_34717,plain,(
    ! [A_1193,C_1194,B_1195] :
      ( r1_tarski(k5_xboole_0(A_1193,C_1194),B_1195)
      | ~ r1_tarski(C_1194,k2_xboole_0(B_1195,k1_xboole_0))
      | ~ r1_tarski(A_1193,k2_xboole_0(B_1195,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_14,c_3334])).

tff(c_63759,plain,(
    ! [A_2029,C_2030,B_2031] :
      ( k2_xboole_0(k5_xboole_0(A_2029,C_2030),B_2031) = B_2031
      | ~ r1_tarski(C_2030,k2_xboole_0(B_2031,k1_xboole_0))
      | ~ r1_tarski(A_2029,k2_xboole_0(B_2031,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_34717,c_6])).

tff(c_63919,plain,(
    ! [A_2035,A_2036] :
      ( k2_xboole_0(k5_xboole_0(A_2035,A_2036),A_2036) = A_2036
      | ~ r1_tarski(A_2035,k2_xboole_0(A_2036,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_18,c_63759])).

tff(c_63990,plain,(
    ! [A_18] : k2_xboole_0(k5_xboole_0(A_18,A_18),A_18) = A_18 ),
    inference(resolution,[status(thm)],[c_18,c_63919])).

tff(c_64012,plain,(
    ! [A_2037] : k2_xboole_0(k3_subset_1(A_2037,A_2037),A_2037) = A_2037 ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_63990])).

tff(c_64290,plain,(
    ! [A_2037] : r1_tarski(k3_subset_1(A_2037,A_2037),A_2037) ),
    inference(superposition,[status(thm),theory(equality)],[c_64012,c_18])).

tff(c_1485,plain,(
    ! [B_184,C_185] :
      ( r1_tarski(k2_xboole_0(B_184,C_185),B_184)
      | ~ r1_xboole_0(k2_xboole_0(B_184,C_185),C_185) ) ),
    inference(resolution,[status(thm)],[c_729,c_16])).

tff(c_1552,plain,(
    ! [B_184] : r1_tarski(k2_xboole_0(B_184,k1_xboole_0),B_184) ),
    inference(resolution,[status(thm)],[c_14,c_1485])).

tff(c_920,plain,(
    ! [A_139,C_140,B_141,D_142] :
      ( r1_xboole_0(A_139,C_140)
      | ~ r1_xboole_0(B_141,D_142)
      | ~ r1_tarski(C_140,D_142)
      | ~ r1_tarski(A_139,B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2048,plain,(
    ! [B_200,C_202,C_198,A_201,A_199] :
      ( r1_xboole_0(A_199,C_202)
      | ~ r1_tarski(C_202,k4_xboole_0(C_198,B_200))
      | ~ r1_tarski(A_199,A_201)
      | ~ r1_tarski(A_201,B_200) ) ),
    inference(resolution,[status(thm)],[c_20,c_920])).

tff(c_34337,plain,(
    ! [A_1172,C_1173,B_1174,A_1175] :
      ( r1_xboole_0(A_1172,k4_xboole_0(C_1173,B_1174))
      | ~ r1_tarski(A_1172,A_1175)
      | ~ r1_tarski(A_1175,B_1174) ) ),
    inference(resolution,[status(thm)],[c_727,c_2048])).

tff(c_35651,plain,(
    ! [A_1227,C_1228,B_1229,B_1230] :
      ( r1_xboole_0(A_1227,k4_xboole_0(C_1228,B_1229))
      | ~ r1_tarski(k2_xboole_0(A_1227,B_1230),B_1229) ) ),
    inference(resolution,[status(thm)],[c_18,c_34337])).

tff(c_35744,plain,(
    ! [B_184,C_1228] : r1_xboole_0(B_184,k4_xboole_0(C_1228,B_184)) ),
    inference(resolution,[status(thm)],[c_1552,c_35651])).

tff(c_22,plain,(
    ! [A_23,B_24,C_25] :
      ( r1_tarski(A_23,k4_xboole_0(B_24,C_25))
      | ~ r1_xboole_0(A_23,C_25)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_35141,plain,(
    ! [B_1209,C_1207,A_1208,A_1211,A_1210] :
      ( r1_xboole_0(A_1210,A_1211)
      | ~ r1_tarski(A_1210,A_1208)
      | ~ r1_tarski(A_1208,C_1207)
      | ~ r1_xboole_0(A_1211,C_1207)
      | ~ r1_tarski(A_1211,B_1209) ) ),
    inference(resolution,[status(thm)],[c_22,c_2048])).

tff(c_43013,plain,(
    ! [A_1474,A_1475,C_1476,B_1477] :
      ( r1_xboole_0(A_1474,A_1475)
      | ~ r1_tarski(A_1474,C_1476)
      | ~ r1_xboole_0(A_1475,C_1476)
      | ~ r1_tarski(A_1475,B_1477) ) ),
    inference(resolution,[status(thm)],[c_727,c_35141])).

tff(c_43141,plain,(
    ! [A_1478,A_1479,B_1480] :
      ( r1_xboole_0(A_1478,A_1479)
      | ~ r1_xboole_0(A_1479,A_1478)
      | ~ r1_tarski(A_1479,B_1480) ) ),
    inference(resolution,[status(thm)],[c_727,c_43013])).

tff(c_43381,plain,(
    ! [C_1481,B_1482,B_1483] :
      ( r1_xboole_0(k4_xboole_0(C_1481,B_1482),B_1482)
      | ~ r1_tarski(B_1482,B_1483) ) ),
    inference(resolution,[status(thm)],[c_35744,c_43141])).

tff(c_43480,plain,(
    ! [C_1484,A_1485] : r1_xboole_0(k4_xboole_0(C_1484,A_1485),A_1485) ),
    inference(resolution,[status(thm)],[c_727,c_43381])).

tff(c_43620,plain,(
    ! [A_1486] : r1_xboole_0(k3_subset_1(A_1486,A_1486),A_1486) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_43480])).

tff(c_567,plain,(
    ! [A_117] :
      ( r1_tarski(A_117,k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_xboole_0(A_117,'#skF_2')
      | ~ r1_tarski(A_117,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_546])).

tff(c_2283,plain,(
    ! [A_205,C_206,A_207] :
      ( r1_xboole_0(A_205,C_206)
      | ~ r1_tarski(C_206,k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_205,A_207)
      | ~ r1_tarski(A_207,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_2048])).

tff(c_5337,plain,(
    ! [A_362,A_363] :
      ( r1_xboole_0(A_362,k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_362,A_363)
      | ~ r1_tarski(A_363,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_727,c_2283])).

tff(c_5466,plain,(
    ! [A_365,B_366] :
      ( r1_xboole_0(A_365,k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k2_xboole_0(A_365,B_366),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_5337])).

tff(c_5526,plain,(
    r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1552,c_5466])).

tff(c_89,plain,(
    ! [A_8] : k2_xboole_0(k1_xboole_0,A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_8,c_73])).

tff(c_699,plain,(
    ! [A_122,A_8] :
      ( r1_tarski(A_122,k1_xboole_0)
      | ~ r1_xboole_0(A_122,A_8)
      | ~ r1_tarski(A_122,A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_652])).

tff(c_5533,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_5526,c_699])).

tff(c_5537,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5533])).

tff(c_5541,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_2')
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_567,c_5537])).

tff(c_5542,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5541])).

tff(c_898,plain,(
    ! [B_138] : k5_xboole_0(B_138,B_138) = k3_subset_1(B_138,B_138) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_813])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k5_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(C_5,B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_31811,plain,(
    ! [B_1130,B_1131] :
      ( r1_tarski(k3_subset_1(B_1130,B_1130),B_1131)
      | ~ r1_tarski(B_1130,B_1131)
      | ~ r1_tarski(B_1130,B_1131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_898,c_4])).

tff(c_1530,plain,(
    ! [A_8] :
      ( r1_tarski(k2_xboole_0(k1_xboole_0,A_8),k1_xboole_0)
      | ~ r1_xboole_0(A_8,A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_1485])).

tff(c_1675,plain,(
    ! [A_190] :
      ( r1_tarski(A_190,k1_xboole_0)
      | ~ r1_xboole_0(A_190,A_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_1530])).

tff(c_3960,plain,(
    ! [C_304,B_305] :
      ( r1_tarski(k4_xboole_0(C_304,B_305),k1_xboole_0)
      | ~ r1_tarski(k4_xboole_0(C_304,B_305),B_305) ) ),
    inference(resolution,[status(thm)],[c_20,c_1675])).

tff(c_3981,plain,(
    ! [A_90] :
      ( r1_tarski(k4_xboole_0(A_90,A_90),k1_xboole_0)
      | ~ r1_tarski(k3_subset_1(A_90,A_90),A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_3960])).

tff(c_3994,plain,(
    ! [A_90] :
      ( r1_tarski(k3_subset_1(A_90,A_90),k1_xboole_0)
      | ~ r1_tarski(k3_subset_1(A_90,A_90),A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_3981])).

tff(c_31948,plain,(
    ! [B_1131] :
      ( r1_tarski(k3_subset_1(B_1131,B_1131),k1_xboole_0)
      | ~ r1_tarski(B_1131,B_1131) ) ),
    inference(resolution,[status(thm)],[c_31811,c_3994])).

tff(c_32112,plain,(
    ! [B_1134] : r1_tarski(k3_subset_1(B_1134,B_1134),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_727,c_31948])).

tff(c_10,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32269,plain,(
    ! [B_1135] : k3_subset_1(B_1135,B_1135) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32112,c_10])).

tff(c_50,plain,(
    ! [B_43,C_45,A_42] :
      ( r1_tarski(B_43,C_45)
      | ~ r1_tarski(k3_subset_1(A_42,C_45),k3_subset_1(A_42,B_43))
      | ~ m1_subset_1(C_45,k1_zfmisc_1(A_42))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_32292,plain,(
    ! [B_43,B_1135] :
      ( r1_tarski(B_43,B_1135)
      | ~ r1_tarski(k1_xboole_0,k3_subset_1(B_1135,B_43))
      | ~ m1_subset_1(B_1135,k1_zfmisc_1(B_1135))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(B_1135)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32269,c_50])).

tff(c_33047,plain,(
    ! [B_1141,B_1142] :
      ( r1_tarski(B_1141,B_1142)
      | ~ m1_subset_1(B_1141,k1_zfmisc_1(B_1142)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_8,c_32292])).

tff(c_33057,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_33047])).

tff(c_33067,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5542,c_33057])).

tff(c_33069,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_5541])).

tff(c_33083,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_33069,c_6])).

tff(c_33141,plain,(
    ! [A_15] :
      ( r1_tarski(A_15,'#skF_2')
      | ~ r1_xboole_0(A_15,'#skF_1')
      | ~ r1_tarski(A_15,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33083,c_16])).

tff(c_43695,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_2')
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_43620,c_33141])).

tff(c_50945,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_43695])).

tff(c_64389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64290,c_50945])).

tff(c_64391,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_43695])).

tff(c_64474,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_1'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_64391,c_3994])).

tff(c_64549,plain,(
    k3_subset_1('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64474,c_10])).

tff(c_64651,plain,(
    ! [B_43] :
      ( r1_tarski(B_43,'#skF_1')
      | ~ r1_tarski(k1_xboole_0,k3_subset_1('#skF_1',B_43))
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_43,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64549,c_50])).

tff(c_64804,plain,(
    ! [B_2045] :
      ( r1_tarski(B_2045,'#skF_1')
      | ~ m1_subset_1(B_2045,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_8,c_64651])).

tff(c_64818,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_64804])).

tff(c_64827,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_895,c_64818])).

tff(c_64828,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_894])).

tff(c_66663,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_66648,c_64828])).

tff(c_66673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_727,c_66663])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:56:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.97/13.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.97/13.82  
% 21.97/13.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.97/13.82  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 21.97/13.82  
% 21.97/13.82  %Foreground sorts:
% 21.97/13.82  
% 21.97/13.82  
% 21.97/13.82  %Background operators:
% 21.97/13.82  
% 21.97/13.82  
% 21.97/13.82  %Foreground operators:
% 21.97/13.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.97/13.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.97/13.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 21.97/13.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 21.97/13.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.97/13.82  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 21.97/13.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.97/13.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 21.97/13.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.97/13.82  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 21.97/13.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 21.97/13.82  tff('#skF_2', type, '#skF_2': $i).
% 21.97/13.82  tff('#skF_3', type, '#skF_3': $i).
% 21.97/13.82  tff('#skF_1', type, '#skF_1': $i).
% 21.97/13.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.97/13.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.97/13.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.97/13.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 21.97/13.82  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 21.97/13.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 21.97/13.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.97/13.82  
% 21.97/13.84  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 21.97/13.84  tff(f_61, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 21.97/13.84  tff(f_59, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 21.97/13.84  tff(f_124, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 21.97/13.84  tff(f_102, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 21.97/13.84  tff(f_65, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 21.97/13.84  tff(f_51, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_xboole_1)).
% 21.97/13.84  tff(f_71, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 21.97/13.84  tff(f_105, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 21.97/13.84  tff(f_85, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 21.97/13.84  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 21.97/13.84  tff(f_73, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 21.97/13.84  tff(f_75, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 21.97/13.84  tff(f_83, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 21.97/13.84  tff(f_98, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 21.97/13.84  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 21.97/13.84  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 21.97/13.84  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 21.97/13.84  tff(f_43, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 21.97/13.84  tff(f_114, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 21.97/13.84  tff(c_14, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 21.97/13.84  tff(c_18, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 21.97/13.84  tff(c_652, plain, (![A_122, B_123, C_124]: (r1_tarski(A_122, B_123) | ~r1_xboole_0(A_122, C_124) | ~r1_tarski(A_122, k2_xboole_0(B_123, C_124)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 21.97/13.84  tff(c_712, plain, (![A_125, B_126]: (r1_tarski(A_125, A_125) | ~r1_xboole_0(A_125, B_126))), inference(resolution, [status(thm)], [c_18, c_652])).
% 21.97/13.84  tff(c_727, plain, (![A_14]: (r1_tarski(A_14, A_14))), inference(resolution, [status(thm)], [c_14, c_712])).
% 21.97/13.84  tff(c_56, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.97/13.84  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.97/13.84  tff(c_192, plain, (![A_84, B_85]: (k4_xboole_0(A_84, B_85)=k3_subset_1(A_84, B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 21.97/13.84  tff(c_205, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_192])).
% 21.97/13.84  tff(c_20, plain, (![A_20, C_22, B_21]: (r1_xboole_0(A_20, k4_xboole_0(C_22, B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 21.97/13.84  tff(c_64873, plain, (![A_2047, C_2048, B_2049, D_2050]: (r1_xboole_0(A_2047, C_2048) | ~r1_xboole_0(B_2049, D_2050) | ~r1_tarski(C_2048, D_2050) | ~r1_tarski(A_2047, B_2049))), inference(cnfTransformation, [status(thm)], [f_51])).
% 21.97/13.84  tff(c_66411, plain, (![A_2117, C_2118, A_2116, C_2114, B_2115]: (r1_xboole_0(A_2117, C_2118) | ~r1_tarski(C_2118, k4_xboole_0(C_2114, B_2115)) | ~r1_tarski(A_2117, A_2116) | ~r1_tarski(A_2116, B_2115))), inference(resolution, [status(thm)], [c_20, c_64873])).
% 21.97/13.84  tff(c_66531, plain, (![A_2122, C_2123, A_2124]: (r1_xboole_0(A_2122, C_2123) | ~r1_tarski(C_2123, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(A_2122, A_2124) | ~r1_tarski(A_2124, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_205, c_66411])).
% 21.97/13.84  tff(c_66573, plain, (![A_2125, A_2126]: (r1_xboole_0(A_2125, '#skF_2') | ~r1_tarski(A_2125, A_2126) | ~r1_tarski(A_2126, '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_66531])).
% 21.97/13.84  tff(c_66648, plain, (![A_2127]: (r1_xboole_0(A_2127, '#skF_2') | ~r1_tarski(A_2127, '#skF_3'))), inference(resolution, [status(thm)], [c_727, c_66573])).
% 21.97/13.84  tff(c_60, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.97/13.84  tff(c_204, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_192])).
% 21.97/13.84  tff(c_546, plain, (![A_117, B_118, C_119]: (r1_tarski(A_117, k4_xboole_0(B_118, C_119)) | ~r1_xboole_0(A_117, C_119) | ~r1_tarski(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_71])).
% 21.97/13.84  tff(c_871, plain, (![A_137]: (r1_tarski(A_137, k3_subset_1('#skF_1', '#skF_2')) | ~r1_xboole_0(A_137, '#skF_2') | ~r1_tarski(A_137, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_204, c_546])).
% 21.97/13.84  tff(c_54, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.97/13.84  tff(c_894, plain, (~r1_xboole_0('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_871, c_54])).
% 21.97/13.84  tff(c_895, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_894])).
% 21.97/13.84  tff(c_48, plain, (![A_41]: (~v1_xboole_0(k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 21.97/13.84  tff(c_36, plain, (![A_36]: (r1_tarski(k1_tarski(A_36), k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 21.97/13.84  tff(c_73, plain, (![A_54, B_55]: (k2_xboole_0(A_54, B_55)=B_55 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.97/13.84  tff(c_87, plain, (![A_36]: (k2_xboole_0(k1_tarski(A_36), k1_zfmisc_1(A_36))=k1_zfmisc_1(A_36))), inference(resolution, [status(thm)], [c_36, c_73])).
% 21.97/13.84  tff(c_176, plain, (![A_82, B_83]: (k2_enumset1(A_82, A_82, A_82, B_83)=k2_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_73])).
% 21.97/13.84  tff(c_26, plain, (![A_28]: (k2_enumset1(A_28, A_28, A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_75])).
% 21.97/13.84  tff(c_206, plain, (![B_86]: (k2_tarski(B_86, B_86)=k1_tarski(B_86))), inference(superposition, [status(thm), theory('equality')], [c_176, c_26])).
% 21.97/13.84  tff(c_140, plain, (![A_66, C_67, B_68]: (r2_hidden(A_66, C_67) | ~r1_tarski(k2_tarski(A_66, B_68), C_67))), inference(cnfTransformation, [status(thm)], [f_83])).
% 21.97/13.84  tff(c_145, plain, (![A_66, B_68, B_19]: (r2_hidden(A_66, k2_xboole_0(k2_tarski(A_66, B_68), B_19)))), inference(resolution, [status(thm)], [c_18, c_140])).
% 21.97/13.84  tff(c_242, plain, (![B_87, B_88]: (r2_hidden(B_87, k2_xboole_0(k1_tarski(B_87), B_88)))), inference(superposition, [status(thm), theory('equality')], [c_206, c_145])).
% 21.97/13.84  tff(c_250, plain, (![A_89]: (r2_hidden(A_89, k1_zfmisc_1(A_89)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_242])).
% 21.97/13.84  tff(c_38, plain, (![B_38, A_37]: (m1_subset_1(B_38, A_37) | ~r2_hidden(B_38, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_98])).
% 21.97/13.84  tff(c_253, plain, (![A_89]: (m1_subset_1(A_89, k1_zfmisc_1(A_89)) | v1_xboole_0(k1_zfmisc_1(A_89)))), inference(resolution, [status(thm)], [c_250, c_38])).
% 21.97/13.84  tff(c_256, plain, (![A_89]: (m1_subset_1(A_89, k1_zfmisc_1(A_89)))), inference(negUnitSimplification, [status(thm)], [c_48, c_253])).
% 21.97/13.84  tff(c_8, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 21.97/13.84  tff(c_257, plain, (![A_90]: (m1_subset_1(A_90, k1_zfmisc_1(A_90)))), inference(negUnitSimplification, [status(thm)], [c_48, c_253])).
% 21.97/13.84  tff(c_46, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=k3_subset_1(A_39, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 21.97/13.84  tff(c_264, plain, (![A_90]: (k4_xboole_0(A_90, A_90)=k3_subset_1(A_90, A_90))), inference(resolution, [status(thm)], [c_257, c_46])).
% 21.97/13.84  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k4_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 21.97/13.84  tff(c_729, plain, (![A_127]: (r1_tarski(A_127, A_127))), inference(resolution, [status(thm)], [c_14, c_712])).
% 21.97/13.84  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.97/13.84  tff(c_766, plain, (![A_129]: (k2_xboole_0(A_129, A_129)=A_129)), inference(resolution, [status(thm)], [c_729, c_6])).
% 21.97/13.84  tff(c_813, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_766])).
% 21.97/13.84  tff(c_831, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k3_subset_1(B_2, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_813])).
% 21.97/13.84  tff(c_853, plain, (![A_134, C_135, B_136]: (r1_tarski(k5_xboole_0(A_134, C_135), B_136) | ~r1_tarski(C_135, B_136) | ~r1_tarski(A_134, B_136))), inference(cnfTransformation, [status(thm)], [f_33])).
% 21.97/13.84  tff(c_16, plain, (![A_15, B_16, C_17]: (r1_tarski(A_15, B_16) | ~r1_xboole_0(A_15, C_17) | ~r1_tarski(A_15, k2_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 21.97/13.84  tff(c_3334, plain, (![A_254, C_255, B_256, C_257]: (r1_tarski(k5_xboole_0(A_254, C_255), B_256) | ~r1_xboole_0(k5_xboole_0(A_254, C_255), C_257) | ~r1_tarski(C_255, k2_xboole_0(B_256, C_257)) | ~r1_tarski(A_254, k2_xboole_0(B_256, C_257)))), inference(resolution, [status(thm)], [c_853, c_16])).
% 21.97/13.84  tff(c_34717, plain, (![A_1193, C_1194, B_1195]: (r1_tarski(k5_xboole_0(A_1193, C_1194), B_1195) | ~r1_tarski(C_1194, k2_xboole_0(B_1195, k1_xboole_0)) | ~r1_tarski(A_1193, k2_xboole_0(B_1195, k1_xboole_0)))), inference(resolution, [status(thm)], [c_14, c_3334])).
% 21.97/13.84  tff(c_63759, plain, (![A_2029, C_2030, B_2031]: (k2_xboole_0(k5_xboole_0(A_2029, C_2030), B_2031)=B_2031 | ~r1_tarski(C_2030, k2_xboole_0(B_2031, k1_xboole_0)) | ~r1_tarski(A_2029, k2_xboole_0(B_2031, k1_xboole_0)))), inference(resolution, [status(thm)], [c_34717, c_6])).
% 21.97/13.84  tff(c_63919, plain, (![A_2035, A_2036]: (k2_xboole_0(k5_xboole_0(A_2035, A_2036), A_2036)=A_2036 | ~r1_tarski(A_2035, k2_xboole_0(A_2036, k1_xboole_0)))), inference(resolution, [status(thm)], [c_18, c_63759])).
% 21.97/13.84  tff(c_63990, plain, (![A_18]: (k2_xboole_0(k5_xboole_0(A_18, A_18), A_18)=A_18)), inference(resolution, [status(thm)], [c_18, c_63919])).
% 21.97/13.84  tff(c_64012, plain, (![A_2037]: (k2_xboole_0(k3_subset_1(A_2037, A_2037), A_2037)=A_2037)), inference(demodulation, [status(thm), theory('equality')], [c_831, c_63990])).
% 21.97/13.84  tff(c_64290, plain, (![A_2037]: (r1_tarski(k3_subset_1(A_2037, A_2037), A_2037))), inference(superposition, [status(thm), theory('equality')], [c_64012, c_18])).
% 21.97/13.84  tff(c_1485, plain, (![B_184, C_185]: (r1_tarski(k2_xboole_0(B_184, C_185), B_184) | ~r1_xboole_0(k2_xboole_0(B_184, C_185), C_185))), inference(resolution, [status(thm)], [c_729, c_16])).
% 21.97/13.84  tff(c_1552, plain, (![B_184]: (r1_tarski(k2_xboole_0(B_184, k1_xboole_0), B_184))), inference(resolution, [status(thm)], [c_14, c_1485])).
% 21.97/13.84  tff(c_920, plain, (![A_139, C_140, B_141, D_142]: (r1_xboole_0(A_139, C_140) | ~r1_xboole_0(B_141, D_142) | ~r1_tarski(C_140, D_142) | ~r1_tarski(A_139, B_141))), inference(cnfTransformation, [status(thm)], [f_51])).
% 21.97/13.84  tff(c_2048, plain, (![B_200, C_202, C_198, A_201, A_199]: (r1_xboole_0(A_199, C_202) | ~r1_tarski(C_202, k4_xboole_0(C_198, B_200)) | ~r1_tarski(A_199, A_201) | ~r1_tarski(A_201, B_200))), inference(resolution, [status(thm)], [c_20, c_920])).
% 21.97/13.84  tff(c_34337, plain, (![A_1172, C_1173, B_1174, A_1175]: (r1_xboole_0(A_1172, k4_xboole_0(C_1173, B_1174)) | ~r1_tarski(A_1172, A_1175) | ~r1_tarski(A_1175, B_1174))), inference(resolution, [status(thm)], [c_727, c_2048])).
% 21.97/13.84  tff(c_35651, plain, (![A_1227, C_1228, B_1229, B_1230]: (r1_xboole_0(A_1227, k4_xboole_0(C_1228, B_1229)) | ~r1_tarski(k2_xboole_0(A_1227, B_1230), B_1229))), inference(resolution, [status(thm)], [c_18, c_34337])).
% 21.97/13.84  tff(c_35744, plain, (![B_184, C_1228]: (r1_xboole_0(B_184, k4_xboole_0(C_1228, B_184)))), inference(resolution, [status(thm)], [c_1552, c_35651])).
% 21.97/13.84  tff(c_22, plain, (![A_23, B_24, C_25]: (r1_tarski(A_23, k4_xboole_0(B_24, C_25)) | ~r1_xboole_0(A_23, C_25) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 21.97/13.84  tff(c_35141, plain, (![B_1209, C_1207, A_1208, A_1211, A_1210]: (r1_xboole_0(A_1210, A_1211) | ~r1_tarski(A_1210, A_1208) | ~r1_tarski(A_1208, C_1207) | ~r1_xboole_0(A_1211, C_1207) | ~r1_tarski(A_1211, B_1209))), inference(resolution, [status(thm)], [c_22, c_2048])).
% 21.97/13.84  tff(c_43013, plain, (![A_1474, A_1475, C_1476, B_1477]: (r1_xboole_0(A_1474, A_1475) | ~r1_tarski(A_1474, C_1476) | ~r1_xboole_0(A_1475, C_1476) | ~r1_tarski(A_1475, B_1477))), inference(resolution, [status(thm)], [c_727, c_35141])).
% 21.97/13.84  tff(c_43141, plain, (![A_1478, A_1479, B_1480]: (r1_xboole_0(A_1478, A_1479) | ~r1_xboole_0(A_1479, A_1478) | ~r1_tarski(A_1479, B_1480))), inference(resolution, [status(thm)], [c_727, c_43013])).
% 21.97/13.84  tff(c_43381, plain, (![C_1481, B_1482, B_1483]: (r1_xboole_0(k4_xboole_0(C_1481, B_1482), B_1482) | ~r1_tarski(B_1482, B_1483))), inference(resolution, [status(thm)], [c_35744, c_43141])).
% 21.97/13.84  tff(c_43480, plain, (![C_1484, A_1485]: (r1_xboole_0(k4_xboole_0(C_1484, A_1485), A_1485))), inference(resolution, [status(thm)], [c_727, c_43381])).
% 21.97/13.84  tff(c_43620, plain, (![A_1486]: (r1_xboole_0(k3_subset_1(A_1486, A_1486), A_1486))), inference(superposition, [status(thm), theory('equality')], [c_264, c_43480])).
% 21.97/13.84  tff(c_567, plain, (![A_117]: (r1_tarski(A_117, k3_subset_1('#skF_1', '#skF_2')) | ~r1_xboole_0(A_117, '#skF_2') | ~r1_tarski(A_117, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_204, c_546])).
% 21.97/13.84  tff(c_2283, plain, (![A_205, C_206, A_207]: (r1_xboole_0(A_205, C_206) | ~r1_tarski(C_206, k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski(A_205, A_207) | ~r1_tarski(A_207, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_204, c_2048])).
% 21.97/13.84  tff(c_5337, plain, (![A_362, A_363]: (r1_xboole_0(A_362, k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski(A_362, A_363) | ~r1_tarski(A_363, '#skF_2'))), inference(resolution, [status(thm)], [c_727, c_2283])).
% 21.97/13.84  tff(c_5466, plain, (![A_365, B_366]: (r1_xboole_0(A_365, k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski(k2_xboole_0(A_365, B_366), '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_5337])).
% 21.97/13.84  tff(c_5526, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1552, c_5466])).
% 21.97/13.84  tff(c_89, plain, (![A_8]: (k2_xboole_0(k1_xboole_0, A_8)=A_8)), inference(resolution, [status(thm)], [c_8, c_73])).
% 21.97/13.84  tff(c_699, plain, (![A_122, A_8]: (r1_tarski(A_122, k1_xboole_0) | ~r1_xboole_0(A_122, A_8) | ~r1_tarski(A_122, A_8))), inference(superposition, [status(thm), theory('equality')], [c_89, c_652])).
% 21.97/13.84  tff(c_5533, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_5526, c_699])).
% 21.97/13.84  tff(c_5537, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_5533])).
% 21.97/13.84  tff(c_5541, plain, (~r1_xboole_0('#skF_2', '#skF_2') | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_567, c_5537])).
% 21.97/13.84  tff(c_5542, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_5541])).
% 21.97/13.84  tff(c_898, plain, (![B_138]: (k5_xboole_0(B_138, B_138)=k3_subset_1(B_138, B_138))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_813])).
% 21.97/13.84  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(k5_xboole_0(A_3, C_5), B_4) | ~r1_tarski(C_5, B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 21.97/13.84  tff(c_31811, plain, (![B_1130, B_1131]: (r1_tarski(k3_subset_1(B_1130, B_1130), B_1131) | ~r1_tarski(B_1130, B_1131) | ~r1_tarski(B_1130, B_1131))), inference(superposition, [status(thm), theory('equality')], [c_898, c_4])).
% 21.97/13.84  tff(c_1530, plain, (![A_8]: (r1_tarski(k2_xboole_0(k1_xboole_0, A_8), k1_xboole_0) | ~r1_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_89, c_1485])).
% 21.97/13.84  tff(c_1675, plain, (![A_190]: (r1_tarski(A_190, k1_xboole_0) | ~r1_xboole_0(A_190, A_190))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_1530])).
% 21.97/13.84  tff(c_3960, plain, (![C_304, B_305]: (r1_tarski(k4_xboole_0(C_304, B_305), k1_xboole_0) | ~r1_tarski(k4_xboole_0(C_304, B_305), B_305))), inference(resolution, [status(thm)], [c_20, c_1675])).
% 21.97/13.84  tff(c_3981, plain, (![A_90]: (r1_tarski(k4_xboole_0(A_90, A_90), k1_xboole_0) | ~r1_tarski(k3_subset_1(A_90, A_90), A_90))), inference(superposition, [status(thm), theory('equality')], [c_264, c_3960])).
% 21.97/13.84  tff(c_3994, plain, (![A_90]: (r1_tarski(k3_subset_1(A_90, A_90), k1_xboole_0) | ~r1_tarski(k3_subset_1(A_90, A_90), A_90))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_3981])).
% 21.97/13.84  tff(c_31948, plain, (![B_1131]: (r1_tarski(k3_subset_1(B_1131, B_1131), k1_xboole_0) | ~r1_tarski(B_1131, B_1131))), inference(resolution, [status(thm)], [c_31811, c_3994])).
% 21.97/13.84  tff(c_32112, plain, (![B_1134]: (r1_tarski(k3_subset_1(B_1134, B_1134), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_727, c_31948])).
% 21.97/13.84  tff(c_10, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 21.97/13.84  tff(c_32269, plain, (![B_1135]: (k3_subset_1(B_1135, B_1135)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32112, c_10])).
% 21.97/13.84  tff(c_50, plain, (![B_43, C_45, A_42]: (r1_tarski(B_43, C_45) | ~r1_tarski(k3_subset_1(A_42, C_45), k3_subset_1(A_42, B_43)) | ~m1_subset_1(C_45, k1_zfmisc_1(A_42)) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 21.97/13.84  tff(c_32292, plain, (![B_43, B_1135]: (r1_tarski(B_43, B_1135) | ~r1_tarski(k1_xboole_0, k3_subset_1(B_1135, B_43)) | ~m1_subset_1(B_1135, k1_zfmisc_1(B_1135)) | ~m1_subset_1(B_43, k1_zfmisc_1(B_1135)))), inference(superposition, [status(thm), theory('equality')], [c_32269, c_50])).
% 21.97/13.84  tff(c_33047, plain, (![B_1141, B_1142]: (r1_tarski(B_1141, B_1142) | ~m1_subset_1(B_1141, k1_zfmisc_1(B_1142)))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_8, c_32292])).
% 21.97/13.84  tff(c_33057, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_33047])).
% 21.97/13.84  tff(c_33067, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5542, c_33057])).
% 21.97/13.84  tff(c_33069, plain, (r1_tarski('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_5541])).
% 21.97/13.84  tff(c_33083, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_33069, c_6])).
% 21.97/13.84  tff(c_33141, plain, (![A_15]: (r1_tarski(A_15, '#skF_2') | ~r1_xboole_0(A_15, '#skF_1') | ~r1_tarski(A_15, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_33083, c_16])).
% 21.97/13.84  tff(c_43695, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_2') | ~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_43620, c_33141])).
% 21.97/13.84  tff(c_50945, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_43695])).
% 21.97/13.84  tff(c_64389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64290, c_50945])).
% 21.97/13.84  tff(c_64391, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_43695])).
% 21.97/13.84  tff(c_64474, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_1'), k1_xboole_0)), inference(resolution, [status(thm)], [c_64391, c_3994])).
% 21.97/13.84  tff(c_64549, plain, (k3_subset_1('#skF_1', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_64474, c_10])).
% 21.97/13.84  tff(c_64651, plain, (![B_43]: (r1_tarski(B_43, '#skF_1') | ~r1_tarski(k1_xboole_0, k3_subset_1('#skF_1', B_43)) | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_43, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_64549, c_50])).
% 21.97/13.84  tff(c_64804, plain, (![B_2045]: (r1_tarski(B_2045, '#skF_1') | ~m1_subset_1(B_2045, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_8, c_64651])).
% 21.97/13.84  tff(c_64818, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_64804])).
% 21.97/13.84  tff(c_64827, plain, $false, inference(negUnitSimplification, [status(thm)], [c_895, c_64818])).
% 21.97/13.84  tff(c_64828, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_894])).
% 21.97/13.84  tff(c_66663, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_66648, c_64828])).
% 21.97/13.84  tff(c_66673, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_727, c_66663])).
% 21.97/13.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.97/13.84  
% 21.97/13.84  Inference rules
% 21.97/13.84  ----------------------
% 21.97/13.84  #Ref     : 0
% 21.97/13.84  #Sup     : 16723
% 21.97/13.84  #Fact    : 0
% 21.97/13.84  #Define  : 0
% 21.97/13.84  #Split   : 91
% 21.97/13.84  #Chain   : 0
% 21.97/13.84  #Close   : 0
% 21.97/13.84  
% 21.97/13.84  Ordering : KBO
% 21.97/13.84  
% 21.97/13.84  Simplification rules
% 21.97/13.84  ----------------------
% 21.97/13.84  #Subsume      : 4655
% 21.97/13.84  #Demod        : 7464
% 21.97/13.84  #Tautology    : 3822
% 21.97/13.84  #SimpNegUnit  : 234
% 21.97/13.84  #BackRed      : 79
% 21.97/13.84  
% 21.97/13.84  #Partial instantiations: 0
% 21.97/13.84  #Strategies tried      : 1
% 21.97/13.84  
% 21.97/13.84  Timing (in seconds)
% 21.97/13.84  ----------------------
% 21.97/13.85  Preprocessing        : 0.32
% 21.97/13.85  Parsing              : 0.17
% 21.97/13.85  CNF conversion       : 0.02
% 21.97/13.85  Main loop            : 12.75
% 21.97/13.85  Inferencing          : 2.00
% 21.97/13.85  Reduction            : 5.35
% 21.97/13.85  Demodulation         : 4.09
% 21.97/13.85  BG Simplification    : 0.17
% 21.97/13.85  Subsumption          : 4.46
% 21.97/13.85  Abstraction          : 0.23
% 21.97/13.85  MUC search           : 0.00
% 21.97/13.85  Cooper               : 0.00
% 21.97/13.85  Total                : 13.12
% 21.97/13.85  Index Insertion      : 0.00
% 21.97/13.85  Index Deletion       : 0.00
% 21.97/13.85  Index Matching       : 0.00
% 21.97/13.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
