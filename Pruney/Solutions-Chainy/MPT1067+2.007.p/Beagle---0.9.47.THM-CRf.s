%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:40 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 179 expanded)
%              Number of leaves         :   28 (  76 expanded)
%              Depth                    :   19
%              Number of atoms          :  207 ( 550 expanded)
%              Number of equality atoms :   18 (  34 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > v1_funct_1 > k7_funct_2 > k6_funct_2 > k5_setfam_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k6_funct_2,type,(
    k6_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k7_funct_2,type,(
    k7_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A)))
                   => r1_tarski(k5_setfam_1(A,D),k5_setfam_1(A,k6_funct_2(A,B,C,k7_funct_2(A,B,C,D)))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A)))
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(A))
                     => ( m1_setfam_1(D,E)
                       => m1_setfam_1(k6_funct_2(A,B,C,k7_funct_2(A,B,C,D)),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A))) )
     => m1_subset_1(k7_funct_2(A,B,C,D),k1_zfmisc_1(k1_zfmisc_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(B))) )
     => m1_subset_1(k6_funct_2(A,B,C,D),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_funct_2)).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_42,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(A_67,B_68)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_53,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_42])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_32,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_60,plain,(
    ! [A_71,B_72] :
      ( k5_setfam_1(A_71,B_72) = k3_tarski(B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k1_zfmisc_1(A_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_69,plain,(
    k5_setfam_1('#skF_1','#skF_4') = k3_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_60])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k5_setfam_1(A_4,B_5),k1_zfmisc_1(A_4))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k1_zfmisc_1(A_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,
    ( m1_subset_1(k3_tarski('#skF_4'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_8])).

tff(c_88,plain,(
    m1_subset_1(k3_tarski('#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_84])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(A_1,k1_zfmisc_1(k3_tarski(A_1))) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_94,plain,(
    ! [A_75,A_76] :
      ( k5_setfam_1(A_75,A_76) = k3_tarski(A_76)
      | ~ r1_tarski(A_76,k1_zfmisc_1(A_75)) ) ),
    inference(resolution,[status(thm)],[c_14,c_60])).

tff(c_103,plain,(
    ! [A_1] : k5_setfam_1(k3_tarski(A_1),A_1) = k3_tarski(A_1) ),
    inference(resolution,[status(thm)],[c_2,c_94])).

tff(c_70,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(k5_setfam_1(A_73,B_74),k1_zfmisc_1(A_73))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(A_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_116,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k5_setfam_1(A_78,B_79),A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k1_zfmisc_1(A_78))) ) ),
    inference(resolution,[status(thm)],[c_70,c_12])).

tff(c_129,plain,(
    ! [A_80,A_81] :
      ( r1_tarski(k5_setfam_1(A_80,A_81),A_80)
      | ~ r1_tarski(A_81,k1_zfmisc_1(A_80)) ) ),
    inference(resolution,[status(thm)],[c_14,c_116])).

tff(c_140,plain,(
    ! [A_1] :
      ( r1_tarski(k3_tarski(A_1),k3_tarski(A_1))
      | ~ r1_tarski(A_1,k1_zfmisc_1(k3_tarski(A_1))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_129])).

tff(c_150,plain,(
    ! [A_82] : r1_tarski(k3_tarski(A_82),k3_tarski(A_82)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_140])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( m1_setfam_1(B_3,A_2)
      | ~ r1_tarski(A_2,k3_tarski(B_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_154,plain,(
    ! [A_82] : m1_setfam_1(A_82,k3_tarski(A_82)) ),
    inference(resolution,[status(thm)],[c_150,c_6])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_345,plain,(
    ! [B_122,E_119,A_121,D_120,C_123] :
      ( m1_setfam_1(k6_funct_2(A_121,B_122,C_123,k7_funct_2(A_121,B_122,C_123,D_120)),E_119)
      | ~ m1_setfam_1(D_120,E_119)
      | ~ m1_subset_1(E_119,k1_zfmisc_1(A_121))
      | ~ m1_subset_1(D_120,k1_zfmisc_1(k1_zfmisc_1(A_121)))
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ v1_funct_2(C_123,A_121,B_122)
      | ~ v1_funct_1(C_123)
      | v1_xboole_0(B_122)
      | v1_xboole_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_357,plain,(
    ! [B_122,C_123,E_119] :
      ( m1_setfam_1(k6_funct_2('#skF_1',B_122,C_123,k7_funct_2('#skF_1',B_122,C_123,'#skF_4')),E_119)
      | ~ m1_setfam_1('#skF_4',E_119)
      | ~ m1_subset_1(E_119,k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_122)))
      | ~ v1_funct_2(C_123,'#skF_1',B_122)
      | ~ v1_funct_1(C_123)
      | v1_xboole_0(B_122)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_345])).

tff(c_455,plain,(
    ! [B_130,C_131,E_132] :
      ( m1_setfam_1(k6_funct_2('#skF_1',B_130,C_131,k7_funct_2('#skF_1',B_130,C_131,'#skF_4')),E_132)
      | ~ m1_setfam_1('#skF_4',E_132)
      | ~ m1_subset_1(E_132,k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_130)))
      | ~ v1_funct_2(C_131,'#skF_1',B_130)
      | ~ v1_funct_1(C_131)
      | v1_xboole_0(B_130) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_357])).

tff(c_465,plain,(
    ! [B_130,A_8,E_132] :
      ( m1_setfam_1(k6_funct_2('#skF_1',B_130,A_8,k7_funct_2('#skF_1',B_130,A_8,'#skF_4')),E_132)
      | ~ m1_setfam_1('#skF_4',E_132)
      | ~ m1_subset_1(E_132,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_2(A_8,'#skF_1',B_130)
      | ~ v1_funct_1(A_8)
      | v1_xboole_0(B_130)
      | ~ r1_tarski(A_8,k2_zfmisc_1('#skF_1',B_130)) ) ),
    inference(resolution,[status(thm)],[c_14,c_455])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(A_2,k3_tarski(B_3))
      | ~ m1_setfam_1(B_3,A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_16,B_17,C_18,D_19] :
      ( m1_subset_1(k7_funct_2(A_16,B_17,C_18,D_19),k1_zfmisc_1(k1_zfmisc_1(B_17)))
      | ~ m1_subset_1(D_19,k1_zfmisc_1(k1_zfmisc_1(A_16)))
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | ~ v1_funct_2(C_18,A_16,B_17)
      | ~ v1_funct_1(C_18)
      | v1_xboole_0(B_17)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_296,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( m1_subset_1(k7_funct_2(A_105,B_106,C_107,D_108),k1_zfmisc_1(k1_zfmisc_1(B_106)))
      | ~ m1_subset_1(D_108,k1_zfmisc_1(k1_zfmisc_1(A_105)))
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ v1_funct_2(C_107,A_105,B_106)
      | ~ v1_funct_1(C_107)
      | v1_xboole_0(B_106)
      | v1_xboole_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k5_setfam_1(A_6,B_7) = k3_tarski(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_902,plain,(
    ! [B_163,A_164,C_165,D_166] :
      ( k5_setfam_1(B_163,k7_funct_2(A_164,B_163,C_165,D_166)) = k3_tarski(k7_funct_2(A_164,B_163,C_165,D_166))
      | ~ m1_subset_1(D_166,k1_zfmisc_1(k1_zfmisc_1(A_164)))
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_164,B_163)))
      | ~ v1_funct_2(C_165,A_164,B_163)
      | ~ v1_funct_1(C_165)
      | v1_xboole_0(B_163)
      | v1_xboole_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_296,c_10])).

tff(c_914,plain,(
    ! [B_163,C_165] :
      ( k5_setfam_1(B_163,k7_funct_2('#skF_1',B_163,C_165,'#skF_4')) = k3_tarski(k7_funct_2('#skF_1',B_163,C_165,'#skF_4'))
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_163)))
      | ~ v1_funct_2(C_165,'#skF_1',B_163)
      | ~ v1_funct_1(C_165)
      | v1_xboole_0(B_163)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_902])).

tff(c_922,plain,(
    ! [B_167,C_168] :
      ( k5_setfam_1(B_167,k7_funct_2('#skF_1',B_167,C_168,'#skF_4')) = k3_tarski(k7_funct_2('#skF_1',B_167,C_168,'#skF_4'))
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_167)))
      | ~ v1_funct_2(C_168,'#skF_1',B_167)
      | ~ v1_funct_1(C_168)
      | v1_xboole_0(B_167) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_914])).

tff(c_930,plain,
    ( k5_setfam_1('#skF_2',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_tarski(k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_922])).

tff(c_935,plain,
    ( k5_setfam_1('#skF_2',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_tarski(k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_930])).

tff(c_936,plain,(
    k5_setfam_1('#skF_2',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_tarski(k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_935])).

tff(c_943,plain,
    ( m1_subset_1(k3_tarski(k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_936,c_8])).

tff(c_996,plain,(
    ~ m1_subset_1(k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_943])).

tff(c_999,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_996])).

tff(c_1005,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_999])).

tff(c_1007,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_1005])).

tff(c_1009,plain,(
    m1_subset_1(k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_943])).

tff(c_241,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( m1_subset_1(k6_funct_2(A_95,B_96,C_97,D_98),k1_zfmisc_1(k1_zfmisc_1(A_95)))
      | ~ m1_subset_1(D_98,k1_zfmisc_1(k1_zfmisc_1(B_96)))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_2(C_97,A_95,B_96)
      | ~ v1_funct_1(C_97)
      | v1_xboole_0(B_96)
      | v1_xboole_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_259,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k5_setfam_1(A_95,k6_funct_2(A_95,B_96,C_97,D_98)) = k3_tarski(k6_funct_2(A_95,B_96,C_97,D_98))
      | ~ m1_subset_1(D_98,k1_zfmisc_1(k1_zfmisc_1(B_96)))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_2(C_97,A_95,B_96)
      | ~ v1_funct_1(C_97)
      | v1_xboole_0(B_96)
      | v1_xboole_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_241,c_10])).

tff(c_1025,plain,(
    ! [A_95,C_97] :
      ( k5_setfam_1(A_95,k6_funct_2(A_95,'#skF_2',C_97,k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) = k3_tarski(k6_funct_2(A_95,'#skF_2',C_97,k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,'#skF_2')))
      | ~ v1_funct_2(C_97,A_95,'#skF_2')
      | ~ v1_funct_1(C_97)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_1009,c_259])).

tff(c_1582,plain,(
    ! [A_217,C_218] :
      ( k5_setfam_1(A_217,k6_funct_2(A_217,'#skF_2',C_218,k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) = k3_tarski(k6_funct_2(A_217,'#skF_2',C_218,k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_217,'#skF_2')))
      | ~ v1_funct_2(C_218,A_217,'#skF_2')
      | ~ v1_funct_1(C_218)
      | v1_xboole_0(A_217) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1025])).

tff(c_1596,plain,
    ( k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) = k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1582])).

tff(c_1603,plain,
    ( k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) = k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1596])).

tff(c_1604,plain,(
    k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) = k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1603])).

tff(c_26,plain,(
    ~ r1_tarski(k5_setfam_1('#skF_1','#skF_4'),k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_80,plain,(
    ~ r1_tarski(k3_tarski('#skF_4'),k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_26])).

tff(c_1605,plain,(
    ~ r1_tarski(k3_tarski('#skF_4'),k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1604,c_80])).

tff(c_1625,plain,(
    ~ m1_setfam_1(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')),k3_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_1605])).

tff(c_1628,plain,
    ( ~ m1_setfam_1('#skF_4',k3_tarski('#skF_4'))
    | ~ m1_subset_1(k3_tarski('#skF_4'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2')
    | ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_465,c_1625])).

tff(c_1634,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_34,c_32,c_88,c_154,c_1628])).

tff(c_1636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1634])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.83  
% 4.63/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.84  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > v1_funct_1 > k7_funct_2 > k6_funct_2 > k5_setfam_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.63/1.84  
% 4.63/1.84  %Foreground sorts:
% 4.63/1.84  
% 4.63/1.84  
% 4.63/1.84  %Background operators:
% 4.63/1.84  
% 4.63/1.84  
% 4.63/1.84  %Foreground operators:
% 4.63/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.63/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.84  tff(k6_funct_2, type, k6_funct_2: ($i * $i * $i * $i) > $i).
% 4.63/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.63/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.63/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.63/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.63/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.63/1.84  tff(k7_funct_2, type, k7_funct_2: ($i * $i * $i * $i) > $i).
% 4.63/1.84  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 4.63/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.63/1.84  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 4.63/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.84  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.63/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.63/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.63/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.63/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.63/1.84  
% 4.63/1.85  tff(f_125, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A))) => r1_tarski(k5_setfam_1(A, D), k5_setfam_1(A, k6_funct_2(A, B, C, k7_funct_2(A, B, C, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t184_funct_2)).
% 4.63/1.85  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.63/1.85  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 4.63/1.85  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 4.63/1.85  tff(f_27, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 4.63/1.85  tff(f_31, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 4.63/1.85  tff(f_105, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(A)) => (m1_setfam_1(D, E) => m1_setfam_1(k6_funct_2(A, B, C, k7_funct_2(A, B, C, D)), E)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_funct_2)).
% 4.63/1.85  tff(f_81, axiom, (![A, B, C, D]: ((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A)))) => m1_subset_1(k7_funct_2(A, B, C, D), k1_zfmisc_1(k1_zfmisc_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_funct_2)).
% 4.63/1.85  tff(f_65, axiom, (![A, B, C, D]: ((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(B)))) => m1_subset_1(k6_funct_2(A, B, C, D), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_funct_2)).
% 4.63/1.85  tff(c_36, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.63/1.85  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.63/1.85  tff(c_42, plain, (![A_67, B_68]: (r1_tarski(A_67, B_68) | ~m1_subset_1(A_67, k1_zfmisc_1(B_68)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.63/1.85  tff(c_53, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_42])).
% 4.63/1.85  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.63/1.85  tff(c_32, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.63/1.85  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.63/1.85  tff(c_60, plain, (![A_71, B_72]: (k5_setfam_1(A_71, B_72)=k3_tarski(B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(k1_zfmisc_1(A_71))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.63/1.85  tff(c_69, plain, (k5_setfam_1('#skF_1', '#skF_4')=k3_tarski('#skF_4')), inference(resolution, [status(thm)], [c_28, c_60])).
% 4.63/1.85  tff(c_8, plain, (![A_4, B_5]: (m1_subset_1(k5_setfam_1(A_4, B_5), k1_zfmisc_1(A_4)) | ~m1_subset_1(B_5, k1_zfmisc_1(k1_zfmisc_1(A_4))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.63/1.85  tff(c_84, plain, (m1_subset_1(k3_tarski('#skF_4'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_69, c_8])).
% 4.63/1.85  tff(c_88, plain, (m1_subset_1(k3_tarski('#skF_4'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_84])).
% 4.63/1.85  tff(c_2, plain, (![A_1]: (r1_tarski(A_1, k1_zfmisc_1(k3_tarski(A_1))))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.63/1.85  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.63/1.85  tff(c_94, plain, (![A_75, A_76]: (k5_setfam_1(A_75, A_76)=k3_tarski(A_76) | ~r1_tarski(A_76, k1_zfmisc_1(A_75)))), inference(resolution, [status(thm)], [c_14, c_60])).
% 4.63/1.85  tff(c_103, plain, (![A_1]: (k5_setfam_1(k3_tarski(A_1), A_1)=k3_tarski(A_1))), inference(resolution, [status(thm)], [c_2, c_94])).
% 4.63/1.85  tff(c_70, plain, (![A_73, B_74]: (m1_subset_1(k5_setfam_1(A_73, B_74), k1_zfmisc_1(A_73)) | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1(A_73))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.63/1.85  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.63/1.85  tff(c_116, plain, (![A_78, B_79]: (r1_tarski(k5_setfam_1(A_78, B_79), A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(k1_zfmisc_1(A_78))))), inference(resolution, [status(thm)], [c_70, c_12])).
% 4.63/1.85  tff(c_129, plain, (![A_80, A_81]: (r1_tarski(k5_setfam_1(A_80, A_81), A_80) | ~r1_tarski(A_81, k1_zfmisc_1(A_80)))), inference(resolution, [status(thm)], [c_14, c_116])).
% 4.63/1.85  tff(c_140, plain, (![A_1]: (r1_tarski(k3_tarski(A_1), k3_tarski(A_1)) | ~r1_tarski(A_1, k1_zfmisc_1(k3_tarski(A_1))))), inference(superposition, [status(thm), theory('equality')], [c_103, c_129])).
% 4.63/1.85  tff(c_150, plain, (![A_82]: (r1_tarski(k3_tarski(A_82), k3_tarski(A_82)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_140])).
% 4.63/1.85  tff(c_6, plain, (![B_3, A_2]: (m1_setfam_1(B_3, A_2) | ~r1_tarski(A_2, k3_tarski(B_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.63/1.85  tff(c_154, plain, (![A_82]: (m1_setfam_1(A_82, k3_tarski(A_82)))), inference(resolution, [status(thm)], [c_150, c_6])).
% 4.63/1.85  tff(c_38, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.63/1.85  tff(c_345, plain, (![B_122, E_119, A_121, D_120, C_123]: (m1_setfam_1(k6_funct_2(A_121, B_122, C_123, k7_funct_2(A_121, B_122, C_123, D_120)), E_119) | ~m1_setfam_1(D_120, E_119) | ~m1_subset_1(E_119, k1_zfmisc_1(A_121)) | ~m1_subset_1(D_120, k1_zfmisc_1(k1_zfmisc_1(A_121))) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~v1_funct_2(C_123, A_121, B_122) | ~v1_funct_1(C_123) | v1_xboole_0(B_122) | v1_xboole_0(A_121))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.63/1.85  tff(c_357, plain, (![B_122, C_123, E_119]: (m1_setfam_1(k6_funct_2('#skF_1', B_122, C_123, k7_funct_2('#skF_1', B_122, C_123, '#skF_4')), E_119) | ~m1_setfam_1('#skF_4', E_119) | ~m1_subset_1(E_119, k1_zfmisc_1('#skF_1')) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_122))) | ~v1_funct_2(C_123, '#skF_1', B_122) | ~v1_funct_1(C_123) | v1_xboole_0(B_122) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_345])).
% 4.63/1.85  tff(c_455, plain, (![B_130, C_131, E_132]: (m1_setfam_1(k6_funct_2('#skF_1', B_130, C_131, k7_funct_2('#skF_1', B_130, C_131, '#skF_4')), E_132) | ~m1_setfam_1('#skF_4', E_132) | ~m1_subset_1(E_132, k1_zfmisc_1('#skF_1')) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_130))) | ~v1_funct_2(C_131, '#skF_1', B_130) | ~v1_funct_1(C_131) | v1_xboole_0(B_130))), inference(negUnitSimplification, [status(thm)], [c_38, c_357])).
% 4.63/1.85  tff(c_465, plain, (![B_130, A_8, E_132]: (m1_setfam_1(k6_funct_2('#skF_1', B_130, A_8, k7_funct_2('#skF_1', B_130, A_8, '#skF_4')), E_132) | ~m1_setfam_1('#skF_4', E_132) | ~m1_subset_1(E_132, k1_zfmisc_1('#skF_1')) | ~v1_funct_2(A_8, '#skF_1', B_130) | ~v1_funct_1(A_8) | v1_xboole_0(B_130) | ~r1_tarski(A_8, k2_zfmisc_1('#skF_1', B_130)))), inference(resolution, [status(thm)], [c_14, c_455])).
% 4.63/1.85  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(A_2, k3_tarski(B_3)) | ~m1_setfam_1(B_3, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.63/1.85  tff(c_22, plain, (![A_16, B_17, C_18, D_19]: (m1_subset_1(k7_funct_2(A_16, B_17, C_18, D_19), k1_zfmisc_1(k1_zfmisc_1(B_17))) | ~m1_subset_1(D_19, k1_zfmisc_1(k1_zfmisc_1(A_16))) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))) | ~v1_funct_2(C_18, A_16, B_17) | ~v1_funct_1(C_18) | v1_xboole_0(B_17) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.63/1.85  tff(c_296, plain, (![A_105, B_106, C_107, D_108]: (m1_subset_1(k7_funct_2(A_105, B_106, C_107, D_108), k1_zfmisc_1(k1_zfmisc_1(B_106))) | ~m1_subset_1(D_108, k1_zfmisc_1(k1_zfmisc_1(A_105))) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))) | ~v1_funct_2(C_107, A_105, B_106) | ~v1_funct_1(C_107) | v1_xboole_0(B_106) | v1_xboole_0(A_105))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.63/1.85  tff(c_10, plain, (![A_6, B_7]: (k5_setfam_1(A_6, B_7)=k3_tarski(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.63/1.85  tff(c_902, plain, (![B_163, A_164, C_165, D_166]: (k5_setfam_1(B_163, k7_funct_2(A_164, B_163, C_165, D_166))=k3_tarski(k7_funct_2(A_164, B_163, C_165, D_166)) | ~m1_subset_1(D_166, k1_zfmisc_1(k1_zfmisc_1(A_164))) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_164, B_163))) | ~v1_funct_2(C_165, A_164, B_163) | ~v1_funct_1(C_165) | v1_xboole_0(B_163) | v1_xboole_0(A_164))), inference(resolution, [status(thm)], [c_296, c_10])).
% 4.63/1.85  tff(c_914, plain, (![B_163, C_165]: (k5_setfam_1(B_163, k7_funct_2('#skF_1', B_163, C_165, '#skF_4'))=k3_tarski(k7_funct_2('#skF_1', B_163, C_165, '#skF_4')) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_163))) | ~v1_funct_2(C_165, '#skF_1', B_163) | ~v1_funct_1(C_165) | v1_xboole_0(B_163) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_902])).
% 4.63/1.85  tff(c_922, plain, (![B_167, C_168]: (k5_setfam_1(B_167, k7_funct_2('#skF_1', B_167, C_168, '#skF_4'))=k3_tarski(k7_funct_2('#skF_1', B_167, C_168, '#skF_4')) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_167))) | ~v1_funct_2(C_168, '#skF_1', B_167) | ~v1_funct_1(C_168) | v1_xboole_0(B_167))), inference(negUnitSimplification, [status(thm)], [c_38, c_914])).
% 4.63/1.85  tff(c_930, plain, (k5_setfam_1('#skF_2', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_tarski(k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_922])).
% 4.63/1.85  tff(c_935, plain, (k5_setfam_1('#skF_2', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_tarski(k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_930])).
% 4.63/1.85  tff(c_936, plain, (k5_setfam_1('#skF_2', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_tarski(k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_36, c_935])).
% 4.63/1.85  tff(c_943, plain, (m1_subset_1(k3_tarski(k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_936, c_8])).
% 4.63/1.85  tff(c_996, plain, (~m1_subset_1(k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_943])).
% 4.63/1.85  tff(c_999, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_996])).
% 4.63/1.85  tff(c_1005, plain, (v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_999])).
% 4.63/1.85  tff(c_1007, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_1005])).
% 4.63/1.85  tff(c_1009, plain, (m1_subset_1(k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitRight, [status(thm)], [c_943])).
% 4.63/1.85  tff(c_241, plain, (![A_95, B_96, C_97, D_98]: (m1_subset_1(k6_funct_2(A_95, B_96, C_97, D_98), k1_zfmisc_1(k1_zfmisc_1(A_95))) | ~m1_subset_1(D_98, k1_zfmisc_1(k1_zfmisc_1(B_96))) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_2(C_97, A_95, B_96) | ~v1_funct_1(C_97) | v1_xboole_0(B_96) | v1_xboole_0(A_95))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.63/1.85  tff(c_259, plain, (![A_95, B_96, C_97, D_98]: (k5_setfam_1(A_95, k6_funct_2(A_95, B_96, C_97, D_98))=k3_tarski(k6_funct_2(A_95, B_96, C_97, D_98)) | ~m1_subset_1(D_98, k1_zfmisc_1(k1_zfmisc_1(B_96))) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_2(C_97, A_95, B_96) | ~v1_funct_1(C_97) | v1_xboole_0(B_96) | v1_xboole_0(A_95))), inference(resolution, [status(thm)], [c_241, c_10])).
% 4.63/1.85  tff(c_1025, plain, (![A_95, C_97]: (k5_setfam_1(A_95, k6_funct_2(A_95, '#skF_2', C_97, k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))=k3_tarski(k6_funct_2(A_95, '#skF_2', C_97, k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, '#skF_2'))) | ~v1_funct_2(C_97, A_95, '#skF_2') | ~v1_funct_1(C_97) | v1_xboole_0('#skF_2') | v1_xboole_0(A_95))), inference(resolution, [status(thm)], [c_1009, c_259])).
% 4.63/1.85  tff(c_1582, plain, (![A_217, C_218]: (k5_setfam_1(A_217, k6_funct_2(A_217, '#skF_2', C_218, k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))=k3_tarski(k6_funct_2(A_217, '#skF_2', C_218, k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_217, '#skF_2'))) | ~v1_funct_2(C_218, A_217, '#skF_2') | ~v1_funct_1(C_218) | v1_xboole_0(A_217))), inference(negUnitSimplification, [status(thm)], [c_36, c_1025])).
% 4.63/1.85  tff(c_1596, plain, (k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))=k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1582])).
% 4.63/1.85  tff(c_1603, plain, (k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))=k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1596])).
% 4.63/1.85  tff(c_1604, plain, (k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))=k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_38, c_1603])).
% 4.63/1.85  tff(c_26, plain, (~r1_tarski(k5_setfam_1('#skF_1', '#skF_4'), k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.63/1.85  tff(c_80, plain, (~r1_tarski(k3_tarski('#skF_4'), k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_26])).
% 4.63/1.85  tff(c_1605, plain, (~r1_tarski(k3_tarski('#skF_4'), k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_1604, c_80])).
% 4.63/1.85  tff(c_1625, plain, (~m1_setfam_1(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')), k3_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_1605])).
% 4.63/1.85  tff(c_1628, plain, (~m1_setfam_1('#skF_4', k3_tarski('#skF_4')) | ~m1_subset_1(k3_tarski('#skF_4'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2') | ~r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_465, c_1625])).
% 4.63/1.85  tff(c_1634, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_34, c_32, c_88, c_154, c_1628])).
% 4.63/1.85  tff(c_1636, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_1634])).
% 4.63/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.85  
% 4.63/1.85  Inference rules
% 4.63/1.85  ----------------------
% 4.63/1.85  #Ref     : 0
% 4.63/1.85  #Sup     : 364
% 4.63/1.85  #Fact    : 0
% 4.63/1.85  #Define  : 0
% 4.63/1.85  #Split   : 5
% 4.63/1.85  #Chain   : 0
% 4.63/1.85  #Close   : 0
% 4.63/1.85  
% 4.63/1.85  Ordering : KBO
% 4.63/1.85  
% 4.63/1.85  Simplification rules
% 4.63/1.85  ----------------------
% 4.63/1.85  #Subsume      : 16
% 4.63/1.85  #Demod        : 65
% 4.63/1.85  #Tautology    : 36
% 4.63/1.85  #SimpNegUnit  : 25
% 4.63/1.85  #BackRed      : 2
% 4.63/1.85  
% 4.63/1.85  #Partial instantiations: 0
% 4.63/1.85  #Strategies tried      : 1
% 4.63/1.85  
% 4.63/1.85  Timing (in seconds)
% 4.63/1.85  ----------------------
% 4.63/1.86  Preprocessing        : 0.35
% 4.63/1.86  Parsing              : 0.19
% 4.63/1.86  CNF conversion       : 0.03
% 4.63/1.86  Main loop            : 0.72
% 4.63/1.86  Inferencing          : 0.27
% 4.63/1.86  Reduction            : 0.20
% 4.63/1.86  Demodulation         : 0.15
% 4.63/1.86  BG Simplification    : 0.04
% 4.63/1.86  Subsumption          : 0.15
% 4.63/1.86  Abstraction          : 0.05
% 4.63/1.86  MUC search           : 0.00
% 4.63/1.86  Cooper               : 0.00
% 4.63/1.86  Total                : 1.10
% 4.63/1.86  Index Insertion      : 0.00
% 4.63/1.86  Index Deletion       : 0.00
% 4.63/1.86  Index Matching       : 0.00
% 4.63/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
