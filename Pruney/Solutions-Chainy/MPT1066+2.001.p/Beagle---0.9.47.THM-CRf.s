%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:39 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 284 expanded)
%              Number of leaves         :   27 ( 113 expanded)
%              Depth                    :   19
%              Number of atoms          :  194 (1009 expanded)
%              Number of equality atoms :   17 (  68 expanded)
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

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(B)))
                   => r1_tarski(k5_setfam_1(B,k7_funct_2(A,B,C,k6_funct_2(A,B,C,D))),k5_setfam_1(B,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t183_funct_2)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(B))) )
     => m1_subset_1(k6_funct_2(A,B,C,D),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A))) )
     => m1_subset_1(k7_funct_2(A,B,C,D),k1_zfmisc_1(k1_zfmisc_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_funct_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_99,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(B)))
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(B))
                     => ( m1_setfam_1(k7_funct_2(A,B,C,k6_funct_2(A,B,C,D)),E)
                       => m1_setfam_1(D,E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_funct_2)).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_28,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_16,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( m1_subset_1(k6_funct_2(A_9,B_10,C_11,D_12),k1_zfmisc_1(k1_zfmisc_1(A_9)))
      | ~ m1_subset_1(D_12,k1_zfmisc_1(k1_zfmisc_1(B_10)))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_2(C_11,A_9,B_10)
      | ~ v1_funct_1(C_11)
      | v1_xboole_0(B_10)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_138,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( m1_subset_1(k6_funct_2(A_79,B_80,C_81,D_82),k1_zfmisc_1(k1_zfmisc_1(A_79)))
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k1_zfmisc_1(B_80)))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ v1_funct_2(C_81,A_79,B_80)
      | ~ v1_funct_1(C_81)
      | v1_xboole_0(B_80)
      | v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k5_setfam_1(A_7,B_8) = k3_tarski(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(k1_zfmisc_1(A_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_179,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( k5_setfam_1(A_94,k6_funct_2(A_94,B_95,C_96,D_97)) = k3_tarski(k6_funct_2(A_94,B_95,C_96,D_97))
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k1_zfmisc_1(B_95)))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ v1_funct_2(C_96,A_94,B_95)
      | ~ v1_funct_1(C_96)
      | v1_xboole_0(B_95)
      | v1_xboole_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_138,c_14])).

tff(c_191,plain,(
    ! [A_94,C_96] :
      ( k5_setfam_1(A_94,k6_funct_2(A_94,'#skF_2',C_96,'#skF_4')) = k3_tarski(k6_funct_2(A_94,'#skF_2',C_96,'#skF_4'))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,'#skF_2')))
      | ~ v1_funct_2(C_96,A_94,'#skF_2')
      | ~ v1_funct_1(C_96)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_24,c_179])).

tff(c_199,plain,(
    ! [A_98,C_99] :
      ( k5_setfam_1(A_98,k6_funct_2(A_98,'#skF_2',C_99,'#skF_4')) = k3_tarski(k6_funct_2(A_98,'#skF_2',C_99,'#skF_4'))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_98,'#skF_2')))
      | ~ v1_funct_2(C_99,A_98,'#skF_2')
      | ~ v1_funct_1(C_99)
      | v1_xboole_0(A_98) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_191])).

tff(c_207,plain,
    ( k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_199])).

tff(c_212,plain,
    ( k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_207])).

tff(c_213,plain,(
    k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_212])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k5_setfam_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_217,plain,
    ( m1_subset_1(k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_12])).

tff(c_221,plain,(
    ~ m1_subset_1(k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_224,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_221])).

tff(c_227,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_224])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_227])).

tff(c_231,plain,(
    m1_subset_1(k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_147,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( m1_subset_1(k7_funct_2(A_83,B_84,C_85,D_86),k1_zfmisc_1(k1_zfmisc_1(B_84)))
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k1_zfmisc_1(A_83)))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_2(C_85,A_83,B_84)
      | ~ v1_funct_1(C_85)
      | v1_xboole_0(B_84)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_242,plain,(
    ! [B_100,A_101,C_102,D_103] :
      ( k5_setfam_1(B_100,k7_funct_2(A_101,B_100,C_102,D_103)) = k3_tarski(k7_funct_2(A_101,B_100,C_102,D_103))
      | ~ m1_subset_1(D_103,k1_zfmisc_1(k1_zfmisc_1(A_101)))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100)))
      | ~ v1_funct_2(C_102,A_101,B_100)
      | ~ v1_funct_1(C_102)
      | v1_xboole_0(B_100)
      | v1_xboole_0(A_101) ) ),
    inference(resolution,[status(thm)],[c_147,c_14])).

tff(c_244,plain,(
    ! [B_100,C_102] :
      ( k5_setfam_1(B_100,k7_funct_2('#skF_1',B_100,C_102,k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) = k3_tarski(k7_funct_2('#skF_1',B_100,C_102,k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_100)))
      | ~ v1_funct_2(C_102,'#skF_1',B_100)
      | ~ v1_funct_1(C_102)
      | v1_xboole_0(B_100)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_231,c_242])).

tff(c_293,plain,(
    ! [B_110,C_111] :
      ( k5_setfam_1(B_110,k7_funct_2('#skF_1',B_110,C_111,k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) = k3_tarski(k7_funct_2('#skF_1',B_110,C_111,k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_110)))
      | ~ v1_funct_2(C_111,'#skF_1',B_110)
      | ~ v1_funct_1(C_111)
      | v1_xboole_0(B_110) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_244])).

tff(c_301,plain,
    ( k5_setfam_1('#skF_2',k7_funct_2('#skF_1','#skF_2','#skF_3',k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) = k3_tarski(k7_funct_2('#skF_1','#skF_2','#skF_3',k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_293])).

tff(c_306,plain,
    ( k5_setfam_1('#skF_2',k7_funct_2('#skF_1','#skF_2','#skF_3',k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) = k3_tarski(k7_funct_2('#skF_1','#skF_2','#skF_3',k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_301])).

tff(c_307,plain,(
    k5_setfam_1('#skF_2',k7_funct_2('#skF_1','#skF_2','#skF_3',k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) = k3_tarski(k7_funct_2('#skF_1','#skF_2','#skF_3',k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_306])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,k3_tarski(B_4))
      | ~ m1_setfam_1(B_4,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    ! [A_67,B_68] :
      ( k5_setfam_1(A_67,B_68) = k3_tarski(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k1_zfmisc_1(A_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_63,plain,(
    k5_setfam_1('#skF_2','#skF_4') = k3_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_59])).

tff(c_22,plain,(
    ~ r1_tarski(k5_setfam_1('#skF_2',k7_funct_2('#skF_1','#skF_2','#skF_3',k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))),k5_setfam_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_64,plain,(
    ~ r1_tarski(k5_setfam_1('#skF_2',k7_funct_2('#skF_1','#skF_2','#skF_3',k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))),k3_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_22])).

tff(c_104,plain,(
    ~ m1_setfam_1('#skF_4',k5_setfam_1('#skF_2',k7_funct_2('#skF_1','#skF_2','#skF_3',k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))) ),
    inference(resolution,[status(thm)],[c_8,c_64])).

tff(c_308,plain,(
    ~ m1_setfam_1('#skF_4',k3_tarski(k7_funct_2('#skF_1','#skF_2','#skF_3',k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_104])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( m1_subset_1(k7_funct_2(A_13,B_14,C_15,D_16),k1_zfmisc_1(k1_zfmisc_1(B_14)))
      | ~ m1_subset_1(D_16,k1_zfmisc_1(k1_zfmisc_1(A_13)))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_2(C_15,A_13,B_14)
      | ~ v1_funct_1(C_15)
      | v1_xboole_0(B_14)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_313,plain,
    ( m1_subset_1(k3_tarski(k7_funct_2('#skF_1','#skF_2','#skF_3',k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_funct_2('#skF_1','#skF_2','#skF_3',k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_12])).

tff(c_330,plain,(
    ~ m1_subset_1(k7_funct_2('#skF_1','#skF_2','#skF_3',k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_333,plain,
    ( ~ m1_subset_1(k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_330])).

tff(c_336,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_231,c_333])).

tff(c_338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_336])).

tff(c_339,plain,(
    m1_subset_1(k3_tarski(k7_funct_2('#skF_1','#skF_2','#skF_3',k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))),k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [B_62,A_63] :
      ( m1_setfam_1(B_62,A_63)
      | ~ r1_tarski(A_63,k3_tarski(B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_47,plain,(
    ! [B_62] : m1_setfam_1(B_62,k3_tarski(B_62)) ),
    inference(resolution,[status(thm)],[c_6,c_38])).

tff(c_174,plain,(
    ! [C_92,D_89,A_91,B_90,E_93] :
      ( m1_setfam_1(D_89,E_93)
      | ~ m1_setfam_1(k7_funct_2(A_91,B_90,C_92,k6_funct_2(A_91,B_90,C_92,D_89)),E_93)
      | ~ m1_subset_1(E_93,k1_zfmisc_1(B_90))
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k1_zfmisc_1(B_90)))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90)))
      | ~ v1_funct_2(C_92,A_91,B_90)
      | ~ v1_funct_1(C_92)
      | v1_xboole_0(B_90)
      | v1_xboole_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_517,plain,(
    ! [D_134,A_135,B_136,C_137] :
      ( m1_setfam_1(D_134,k3_tarski(k7_funct_2(A_135,B_136,C_137,k6_funct_2(A_135,B_136,C_137,D_134))))
      | ~ m1_subset_1(k3_tarski(k7_funct_2(A_135,B_136,C_137,k6_funct_2(A_135,B_136,C_137,D_134))),k1_zfmisc_1(B_136))
      | ~ m1_subset_1(D_134,k1_zfmisc_1(k1_zfmisc_1(B_136)))
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136)))
      | ~ v1_funct_2(C_137,A_135,B_136)
      | ~ v1_funct_1(C_137)
      | v1_xboole_0(B_136)
      | v1_xboole_0(A_135) ) ),
    inference(resolution,[status(thm)],[c_47,c_174])).

tff(c_519,plain,
    ( m1_setfam_1('#skF_4',k3_tarski(k7_funct_2('#skF_1','#skF_2','#skF_3',k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_339,c_517])).

tff(c_522,plain,
    ( m1_setfam_1('#skF_4',k3_tarski(k7_funct_2('#skF_1','#skF_2','#skF_3',k6_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))))
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_519])).

tff(c_524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_308,c_522])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:28:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.55  
% 3.09/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.55  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > v1_funct_1 > k7_funct_2 > k6_funct_2 > k5_setfam_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.09/1.55  
% 3.09/1.55  %Foreground sorts:
% 3.09/1.55  
% 3.09/1.55  
% 3.09/1.55  %Background operators:
% 3.09/1.55  
% 3.09/1.55  
% 3.09/1.55  %Foreground operators:
% 3.09/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.09/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.55  tff(k6_funct_2, type, k6_funct_2: ($i * $i * $i * $i) > $i).
% 3.09/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.09/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.09/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.09/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.09/1.55  tff(k7_funct_2, type, k7_funct_2: ($i * $i * $i * $i) > $i).
% 3.09/1.55  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 3.09/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.09/1.55  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.09/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.55  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.09/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.09/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.09/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.09/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.09/1.55  
% 3.09/1.57  tff(f_119, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(B))) => r1_tarski(k5_setfam_1(B, k7_funct_2(A, B, C, k6_funct_2(A, B, C, D))), k5_setfam_1(B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t183_funct_2)).
% 3.09/1.57  tff(f_59, axiom, (![A, B, C, D]: ((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(B)))) => m1_subset_1(k6_funct_2(A, B, C, D), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_funct_2)).
% 3.09/1.57  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 3.09/1.57  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 3.09/1.57  tff(f_75, axiom, (![A, B, C, D]: ((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A)))) => m1_subset_1(k7_funct_2(A, B, C, D), k1_zfmisc_1(k1_zfmisc_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_funct_2)).
% 3.09/1.57  tff(f_35, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 3.09/1.57  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.09/1.57  tff(f_99, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (m1_setfam_1(k7_funct_2(A, B, C, k6_funct_2(A, B, C, D)), E) => m1_setfam_1(D, E)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_funct_2)).
% 3.09/1.57  tff(c_34, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.09/1.57  tff(c_32, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.09/1.57  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.09/1.57  tff(c_28, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.09/1.57  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.09/1.57  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.09/1.57  tff(c_16, plain, (![A_9, B_10, C_11, D_12]: (m1_subset_1(k6_funct_2(A_9, B_10, C_11, D_12), k1_zfmisc_1(k1_zfmisc_1(A_9))) | ~m1_subset_1(D_12, k1_zfmisc_1(k1_zfmisc_1(B_10))) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))) | ~v1_funct_2(C_11, A_9, B_10) | ~v1_funct_1(C_11) | v1_xboole_0(B_10) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.09/1.57  tff(c_138, plain, (![A_79, B_80, C_81, D_82]: (m1_subset_1(k6_funct_2(A_79, B_80, C_81, D_82), k1_zfmisc_1(k1_zfmisc_1(A_79))) | ~m1_subset_1(D_82, k1_zfmisc_1(k1_zfmisc_1(B_80))) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~v1_funct_2(C_81, A_79, B_80) | ~v1_funct_1(C_81) | v1_xboole_0(B_80) | v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.09/1.57  tff(c_14, plain, (![A_7, B_8]: (k5_setfam_1(A_7, B_8)=k3_tarski(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(k1_zfmisc_1(A_7))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.09/1.57  tff(c_179, plain, (![A_94, B_95, C_96, D_97]: (k5_setfam_1(A_94, k6_funct_2(A_94, B_95, C_96, D_97))=k3_tarski(k6_funct_2(A_94, B_95, C_96, D_97)) | ~m1_subset_1(D_97, k1_zfmisc_1(k1_zfmisc_1(B_95))) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~v1_funct_2(C_96, A_94, B_95) | ~v1_funct_1(C_96) | v1_xboole_0(B_95) | v1_xboole_0(A_94))), inference(resolution, [status(thm)], [c_138, c_14])).
% 3.09/1.57  tff(c_191, plain, (![A_94, C_96]: (k5_setfam_1(A_94, k6_funct_2(A_94, '#skF_2', C_96, '#skF_4'))=k3_tarski(k6_funct_2(A_94, '#skF_2', C_96, '#skF_4')) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, '#skF_2'))) | ~v1_funct_2(C_96, A_94, '#skF_2') | ~v1_funct_1(C_96) | v1_xboole_0('#skF_2') | v1_xboole_0(A_94))), inference(resolution, [status(thm)], [c_24, c_179])).
% 3.09/1.57  tff(c_199, plain, (![A_98, C_99]: (k5_setfam_1(A_98, k6_funct_2(A_98, '#skF_2', C_99, '#skF_4'))=k3_tarski(k6_funct_2(A_98, '#skF_2', C_99, '#skF_4')) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_98, '#skF_2'))) | ~v1_funct_2(C_99, A_98, '#skF_2') | ~v1_funct_1(C_99) | v1_xboole_0(A_98))), inference(negUnitSimplification, [status(thm)], [c_32, c_191])).
% 3.09/1.57  tff(c_207, plain, (k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_199])).
% 3.09/1.57  tff(c_212, plain, (k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_207])).
% 3.09/1.57  tff(c_213, plain, (k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_34, c_212])).
% 3.09/1.57  tff(c_12, plain, (![A_5, B_6]: (m1_subset_1(k5_setfam_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.09/1.57  tff(c_217, plain, (m1_subset_1(k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_213, c_12])).
% 3.09/1.57  tff(c_221, plain, (~m1_subset_1(k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_217])).
% 3.09/1.57  tff(c_224, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_221])).
% 3.09/1.57  tff(c_227, plain, (v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_224])).
% 3.09/1.57  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_227])).
% 3.09/1.57  tff(c_231, plain, (m1_subset_1(k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(splitRight, [status(thm)], [c_217])).
% 3.09/1.57  tff(c_147, plain, (![A_83, B_84, C_85, D_86]: (m1_subset_1(k7_funct_2(A_83, B_84, C_85, D_86), k1_zfmisc_1(k1_zfmisc_1(B_84))) | ~m1_subset_1(D_86, k1_zfmisc_1(k1_zfmisc_1(A_83))) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_2(C_85, A_83, B_84) | ~v1_funct_1(C_85) | v1_xboole_0(B_84) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.09/1.57  tff(c_242, plain, (![B_100, A_101, C_102, D_103]: (k5_setfam_1(B_100, k7_funct_2(A_101, B_100, C_102, D_103))=k3_tarski(k7_funct_2(A_101, B_100, C_102, D_103)) | ~m1_subset_1(D_103, k1_zfmisc_1(k1_zfmisc_1(A_101))) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))) | ~v1_funct_2(C_102, A_101, B_100) | ~v1_funct_1(C_102) | v1_xboole_0(B_100) | v1_xboole_0(A_101))), inference(resolution, [status(thm)], [c_147, c_14])).
% 3.09/1.57  tff(c_244, plain, (![B_100, C_102]: (k5_setfam_1(B_100, k7_funct_2('#skF_1', B_100, C_102, k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))=k3_tarski(k7_funct_2('#skF_1', B_100, C_102, k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_100))) | ~v1_funct_2(C_102, '#skF_1', B_100) | ~v1_funct_1(C_102) | v1_xboole_0(B_100) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_231, c_242])).
% 3.09/1.57  tff(c_293, plain, (![B_110, C_111]: (k5_setfam_1(B_110, k7_funct_2('#skF_1', B_110, C_111, k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))=k3_tarski(k7_funct_2('#skF_1', B_110, C_111, k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_110))) | ~v1_funct_2(C_111, '#skF_1', B_110) | ~v1_funct_1(C_111) | v1_xboole_0(B_110))), inference(negUnitSimplification, [status(thm)], [c_34, c_244])).
% 3.09/1.57  tff(c_301, plain, (k5_setfam_1('#skF_2', k7_funct_2('#skF_1', '#skF_2', '#skF_3', k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))=k3_tarski(k7_funct_2('#skF_1', '#skF_2', '#skF_3', k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_293])).
% 3.09/1.57  tff(c_306, plain, (k5_setfam_1('#skF_2', k7_funct_2('#skF_1', '#skF_2', '#skF_3', k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))=k3_tarski(k7_funct_2('#skF_1', '#skF_2', '#skF_3', k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_301])).
% 3.09/1.57  tff(c_307, plain, (k5_setfam_1('#skF_2', k7_funct_2('#skF_1', '#skF_2', '#skF_3', k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))=k3_tarski(k7_funct_2('#skF_1', '#skF_2', '#skF_3', k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_32, c_306])).
% 3.09/1.57  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, k3_tarski(B_4)) | ~m1_setfam_1(B_4, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.09/1.57  tff(c_59, plain, (![A_67, B_68]: (k5_setfam_1(A_67, B_68)=k3_tarski(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(k1_zfmisc_1(A_67))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.09/1.57  tff(c_63, plain, (k5_setfam_1('#skF_2', '#skF_4')=k3_tarski('#skF_4')), inference(resolution, [status(thm)], [c_24, c_59])).
% 3.09/1.57  tff(c_22, plain, (~r1_tarski(k5_setfam_1('#skF_2', k7_funct_2('#skF_1', '#skF_2', '#skF_3', k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), k5_setfam_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.09/1.57  tff(c_64, plain, (~r1_tarski(k5_setfam_1('#skF_2', k7_funct_2('#skF_1', '#skF_2', '#skF_3', k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), k3_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_22])).
% 3.09/1.57  tff(c_104, plain, (~m1_setfam_1('#skF_4', k5_setfam_1('#skF_2', k7_funct_2('#skF_1', '#skF_2', '#skF_3', k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_8, c_64])).
% 3.09/1.57  tff(c_308, plain, (~m1_setfam_1('#skF_4', k3_tarski(k7_funct_2('#skF_1', '#skF_2', '#skF_3', k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_307, c_104])).
% 3.09/1.57  tff(c_18, plain, (![A_13, B_14, C_15, D_16]: (m1_subset_1(k7_funct_2(A_13, B_14, C_15, D_16), k1_zfmisc_1(k1_zfmisc_1(B_14))) | ~m1_subset_1(D_16, k1_zfmisc_1(k1_zfmisc_1(A_13))) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_2(C_15, A_13, B_14) | ~v1_funct_1(C_15) | v1_xboole_0(B_14) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.09/1.57  tff(c_313, plain, (m1_subset_1(k3_tarski(k7_funct_2('#skF_1', '#skF_2', '#skF_3', k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_funct_2('#skF_1', '#skF_2', '#skF_3', k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_307, c_12])).
% 3.09/1.57  tff(c_330, plain, (~m1_subset_1(k7_funct_2('#skF_1', '#skF_2', '#skF_3', k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_313])).
% 3.09/1.57  tff(c_333, plain, (~m1_subset_1(k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_330])).
% 3.09/1.57  tff(c_336, plain, (v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_231, c_333])).
% 3.09/1.57  tff(c_338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_336])).
% 3.09/1.57  tff(c_339, plain, (m1_subset_1(k3_tarski(k7_funct_2('#skF_1', '#skF_2', '#skF_3', k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_313])).
% 3.09/1.57  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.09/1.57  tff(c_38, plain, (![B_62, A_63]: (m1_setfam_1(B_62, A_63) | ~r1_tarski(A_63, k3_tarski(B_62)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.09/1.57  tff(c_47, plain, (![B_62]: (m1_setfam_1(B_62, k3_tarski(B_62)))), inference(resolution, [status(thm)], [c_6, c_38])).
% 3.09/1.57  tff(c_174, plain, (![C_92, D_89, A_91, B_90, E_93]: (m1_setfam_1(D_89, E_93) | ~m1_setfam_1(k7_funct_2(A_91, B_90, C_92, k6_funct_2(A_91, B_90, C_92, D_89)), E_93) | ~m1_subset_1(E_93, k1_zfmisc_1(B_90)) | ~m1_subset_1(D_89, k1_zfmisc_1(k1_zfmisc_1(B_90))) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))) | ~v1_funct_2(C_92, A_91, B_90) | ~v1_funct_1(C_92) | v1_xboole_0(B_90) | v1_xboole_0(A_91))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.09/1.57  tff(c_517, plain, (![D_134, A_135, B_136, C_137]: (m1_setfam_1(D_134, k3_tarski(k7_funct_2(A_135, B_136, C_137, k6_funct_2(A_135, B_136, C_137, D_134)))) | ~m1_subset_1(k3_tarski(k7_funct_2(A_135, B_136, C_137, k6_funct_2(A_135, B_136, C_137, D_134))), k1_zfmisc_1(B_136)) | ~m1_subset_1(D_134, k1_zfmisc_1(k1_zfmisc_1(B_136))) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))) | ~v1_funct_2(C_137, A_135, B_136) | ~v1_funct_1(C_137) | v1_xboole_0(B_136) | v1_xboole_0(A_135))), inference(resolution, [status(thm)], [c_47, c_174])).
% 3.09/1.57  tff(c_519, plain, (m1_setfam_1('#skF_4', k3_tarski(k7_funct_2('#skF_1', '#skF_2', '#skF_3', k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_339, c_517])).
% 3.09/1.57  tff(c_522, plain, (m1_setfam_1('#skF_4', k3_tarski(k7_funct_2('#skF_1', '#skF_2', '#skF_3', k6_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))) | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_519])).
% 3.09/1.57  tff(c_524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_308, c_522])).
% 3.09/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.57  
% 3.09/1.57  Inference rules
% 3.09/1.57  ----------------------
% 3.09/1.57  #Ref     : 0
% 3.09/1.57  #Sup     : 108
% 3.09/1.57  #Fact    : 0
% 3.09/1.57  #Define  : 0
% 3.09/1.57  #Split   : 2
% 3.09/1.57  #Chain   : 0
% 3.09/1.57  #Close   : 0
% 3.09/1.57  
% 3.09/1.57  Ordering : KBO
% 3.09/1.57  
% 3.09/1.57  Simplification rules
% 3.09/1.57  ----------------------
% 3.09/1.57  #Subsume      : 1
% 3.09/1.57  #Demod        : 28
% 3.09/1.57  #Tautology    : 23
% 3.09/1.57  #SimpNegUnit  : 13
% 3.09/1.57  #BackRed      : 3
% 3.09/1.57  
% 3.09/1.57  #Partial instantiations: 0
% 3.09/1.57  #Strategies tried      : 1
% 3.09/1.57  
% 3.09/1.57  Timing (in seconds)
% 3.09/1.57  ----------------------
% 3.27/1.57  Preprocessing        : 0.36
% 3.27/1.57  Parsing              : 0.20
% 3.27/1.57  CNF conversion       : 0.03
% 3.27/1.57  Main loop            : 0.37
% 3.27/1.57  Inferencing          : 0.14
% 3.27/1.57  Reduction            : 0.10
% 3.27/1.57  Demodulation         : 0.07
% 3.27/1.57  BG Simplification    : 0.02
% 3.27/1.57  Subsumption          : 0.08
% 3.27/1.57  Abstraction          : 0.03
% 3.27/1.57  MUC search           : 0.00
% 3.27/1.57  Cooper               : 0.00
% 3.27/1.57  Total                : 0.76
% 3.27/1.57  Index Insertion      : 0.00
% 3.27/1.57  Index Deletion       : 0.00
% 3.27/1.57  Index Matching       : 0.00
% 3.27/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
