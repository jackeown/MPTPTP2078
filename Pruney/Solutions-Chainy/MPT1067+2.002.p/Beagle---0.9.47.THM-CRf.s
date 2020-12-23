%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:40 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 157 expanded)
%              Number of leaves         :   27 (  68 expanded)
%              Depth                    :   18
%              Number of atoms          :  191 ( 512 expanded)
%              Number of equality atoms :   17 (  31 expanded)
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
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A)))
                   => r1_tarski(k5_setfam_1(A,D),k5_setfam_1(A,k6_funct_2(A,B,C,k7_funct_2(A,B,C,D)))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_funct_2)).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

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
                  ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A)))
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(A))
                     => ( m1_setfam_1(D,E)
                       => m1_setfam_1(k6_funct_2(A,B,C,k7_funct_2(A,B,C,D)),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_funct_2)).

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

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_59,plain,(
    ! [A_67,B_68] :
      ( k5_setfam_1(A_67,B_68) = k3_tarski(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k1_zfmisc_1(A_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_63,plain,(
    k5_setfam_1('#skF_1','#skF_4') = k3_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_59])).

tff(c_83,plain,(
    ! [A_71,B_72] :
      ( m1_subset_1(k5_setfam_1(A_71,B_72),k1_zfmisc_1(A_71))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k1_zfmisc_1(A_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_90,plain,
    ( m1_subset_1(k3_tarski('#skF_4'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_83])).

tff(c_93,plain,(
    m1_subset_1(k3_tarski('#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_90])).

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

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_190,plain,(
    ! [A_95,C_96,B_94,E_97,D_93] :
      ( m1_setfam_1(k6_funct_2(A_95,B_94,C_96,k7_funct_2(A_95,B_94,C_96,D_93)),E_97)
      | ~ m1_setfam_1(D_93,E_97)
      | ~ m1_subset_1(E_97,k1_zfmisc_1(A_95))
      | ~ m1_subset_1(D_93,k1_zfmisc_1(k1_zfmisc_1(A_95)))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94)))
      | ~ v1_funct_2(C_96,A_95,B_94)
      | ~ v1_funct_1(C_96)
      | v1_xboole_0(B_94)
      | v1_xboole_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_202,plain,(
    ! [B_94,C_96,E_97] :
      ( m1_setfam_1(k6_funct_2('#skF_1',B_94,C_96,k7_funct_2('#skF_1',B_94,C_96,'#skF_4')),E_97)
      | ~ m1_setfam_1('#skF_4',E_97)
      | ~ m1_subset_1(E_97,k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_94)))
      | ~ v1_funct_2(C_96,'#skF_1',B_94)
      | ~ v1_funct_1(C_96)
      | v1_xboole_0(B_94)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_190])).

tff(c_273,plain,(
    ! [B_103,C_104,E_105] :
      ( m1_setfam_1(k6_funct_2('#skF_1',B_103,C_104,k7_funct_2('#skF_1',B_103,C_104,'#skF_4')),E_105)
      | ~ m1_setfam_1('#skF_4',E_105)
      | ~ m1_subset_1(E_105,k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_103)))
      | ~ v1_funct_2(C_104,'#skF_1',B_103)
      | ~ v1_funct_1(C_104)
      | v1_xboole_0(B_103) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_202])).

tff(c_281,plain,(
    ! [E_105] :
      ( m1_setfam_1(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')),E_105)
      | ~ m1_setfam_1('#skF_4',E_105)
      | ~ m1_subset_1(E_105,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_1('#skF_3')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_273])).

tff(c_286,plain,(
    ! [E_105] :
      ( m1_setfam_1(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')),E_105)
      | ~ m1_setfam_1('#skF_4',E_105)
      | ~ m1_subset_1(E_105,k1_zfmisc_1('#skF_1'))
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_281])).

tff(c_287,plain,(
    ! [E_105] :
      ( m1_setfam_1(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')),E_105)
      | ~ m1_setfam_1('#skF_4',E_105)
      | ~ m1_subset_1(E_105,k1_zfmisc_1('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_286])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,k3_tarski(B_4))
      | ~ m1_setfam_1(B_4,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

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

tff(c_101,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( m1_subset_1(k7_funct_2(A_75,B_76,C_77,D_78),k1_zfmisc_1(k1_zfmisc_1(B_76)))
      | ~ m1_subset_1(D_78,k1_zfmisc_1(k1_zfmisc_1(A_75)))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | ~ v1_funct_2(C_77,A_75,B_76)
      | ~ v1_funct_1(C_77)
      | v1_xboole_0(B_76)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k5_setfam_1(A_7,B_8) = k3_tarski(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(k1_zfmisc_1(A_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_170,plain,(
    ! [B_89,A_90,C_91,D_92] :
      ( k5_setfam_1(B_89,k7_funct_2(A_90,B_89,C_91,D_92)) = k3_tarski(k7_funct_2(A_90,B_89,C_91,D_92))
      | ~ m1_subset_1(D_92,k1_zfmisc_1(k1_zfmisc_1(A_90)))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89)))
      | ~ v1_funct_2(C_91,A_90,B_89)
      | ~ v1_funct_1(C_91)
      | v1_xboole_0(B_89)
      | v1_xboole_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_101,c_14])).

tff(c_182,plain,(
    ! [B_89,C_91] :
      ( k5_setfam_1(B_89,k7_funct_2('#skF_1',B_89,C_91,'#skF_4')) = k3_tarski(k7_funct_2('#skF_1',B_89,C_91,'#skF_4'))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_89)))
      | ~ v1_funct_2(C_91,'#skF_1',B_89)
      | ~ v1_funct_1(C_91)
      | v1_xboole_0(B_89)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_170])).

tff(c_210,plain,(
    ! [B_98,C_99] :
      ( k5_setfam_1(B_98,k7_funct_2('#skF_1',B_98,C_99,'#skF_4')) = k3_tarski(k7_funct_2('#skF_1',B_98,C_99,'#skF_4'))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_98)))
      | ~ v1_funct_2(C_99,'#skF_1',B_98)
      | ~ v1_funct_1(C_99)
      | v1_xboole_0(B_98) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_182])).

tff(c_218,plain,
    ( k5_setfam_1('#skF_2',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_tarski(k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_210])).

tff(c_223,plain,
    ( k5_setfam_1('#skF_2',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_tarski(k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_218])).

tff(c_224,plain,(
    k5_setfam_1('#skF_2',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_tarski(k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_223])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k5_setfam_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_228,plain,
    ( m1_subset_1(k3_tarski(k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_12])).

tff(c_232,plain,(
    ~ m1_subset_1(k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_250,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_232])).

tff(c_253,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_250])).

tff(c_255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_253])).

tff(c_257,plain,(
    m1_subset_1(k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_143,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( m1_subset_1(k6_funct_2(A_83,B_84,C_85,D_86),k1_zfmisc_1(k1_zfmisc_1(A_83)))
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k1_zfmisc_1(B_84)))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_2(C_85,A_83,B_84)
      | ~ v1_funct_1(C_85)
      | v1_xboole_0(B_84)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_293,plain,(
    ! [A_107,B_108,C_109,D_110] :
      ( k5_setfam_1(A_107,k6_funct_2(A_107,B_108,C_109,D_110)) = k3_tarski(k6_funct_2(A_107,B_108,C_109,D_110))
      | ~ m1_subset_1(D_110,k1_zfmisc_1(k1_zfmisc_1(B_108)))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ v1_funct_2(C_109,A_107,B_108)
      | ~ v1_funct_1(C_109)
      | v1_xboole_0(B_108)
      | v1_xboole_0(A_107) ) ),
    inference(resolution,[status(thm)],[c_143,c_14])).

tff(c_295,plain,(
    ! [A_107,C_109] :
      ( k5_setfam_1(A_107,k6_funct_2(A_107,'#skF_2',C_109,k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) = k3_tarski(k6_funct_2(A_107,'#skF_2',C_109,k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,'#skF_2')))
      | ~ v1_funct_2(C_109,A_107,'#skF_2')
      | ~ v1_funct_1(C_109)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_107) ) ),
    inference(resolution,[status(thm)],[c_257,c_293])).

tff(c_340,plain,(
    ! [A_114,C_115] :
      ( k5_setfam_1(A_114,k6_funct_2(A_114,'#skF_2',C_115,k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) = k3_tarski(k6_funct_2(A_114,'#skF_2',C_115,k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_114,'#skF_2')))
      | ~ v1_funct_2(C_115,A_114,'#skF_2')
      | ~ v1_funct_1(C_115)
      | v1_xboole_0(A_114) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_295])).

tff(c_348,plain,
    ( k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) = k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_340])).

tff(c_353,plain,
    ( k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) = k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_348])).

tff(c_354,plain,(
    k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) = k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_353])).

tff(c_22,plain,(
    ~ r1_tarski(k5_setfam_1('#skF_1','#skF_4'),k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_64,plain,(
    ~ r1_tarski(k3_tarski('#skF_4'),k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_22])).

tff(c_355,plain,(
    ~ r1_tarski(k3_tarski('#skF_4'),k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_64])).

tff(c_366,plain,(
    ~ m1_setfam_1(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')),k3_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_355])).

tff(c_369,plain,
    ( ~ m1_setfam_1('#skF_4',k3_tarski('#skF_4'))
    | ~ m1_subset_1(k3_tarski('#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_287,c_366])).

tff(c_373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_47,c_369])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.38  
% 2.73/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.38  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > v1_funct_1 > k7_funct_2 > k6_funct_2 > k5_setfam_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.73/1.38  
% 2.73/1.38  %Foreground sorts:
% 2.73/1.38  
% 2.73/1.38  
% 2.73/1.38  %Background operators:
% 2.73/1.38  
% 2.73/1.38  
% 2.73/1.38  %Foreground operators:
% 2.73/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.38  tff(k6_funct_2, type, k6_funct_2: ($i * $i * $i * $i) > $i).
% 2.73/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.73/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.73/1.38  tff(k7_funct_2, type, k7_funct_2: ($i * $i * $i * $i) > $i).
% 2.73/1.38  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.73/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.38  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.73/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.73/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.38  
% 2.73/1.40  tff(f_119, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A))) => r1_tarski(k5_setfam_1(A, D), k5_setfam_1(A, k6_funct_2(A, B, C, k7_funct_2(A, B, C, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t184_funct_2)).
% 2.73/1.40  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.73/1.40  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.73/1.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.73/1.40  tff(f_35, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 2.73/1.40  tff(f_99, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(A)) => (m1_setfam_1(D, E) => m1_setfam_1(k6_funct_2(A, B, C, k7_funct_2(A, B, C, D)), E)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_funct_2)).
% 2.73/1.40  tff(f_75, axiom, (![A, B, C, D]: ((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A)))) => m1_subset_1(k7_funct_2(A, B, C, D), k1_zfmisc_1(k1_zfmisc_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_funct_2)).
% 2.73/1.40  tff(f_59, axiom, (![A, B, C, D]: ((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(B)))) => m1_subset_1(k6_funct_2(A, B, C, D), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_funct_2)).
% 2.73/1.40  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.73/1.40  tff(c_59, plain, (![A_67, B_68]: (k5_setfam_1(A_67, B_68)=k3_tarski(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(k1_zfmisc_1(A_67))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.73/1.40  tff(c_63, plain, (k5_setfam_1('#skF_1', '#skF_4')=k3_tarski('#skF_4')), inference(resolution, [status(thm)], [c_24, c_59])).
% 2.73/1.40  tff(c_83, plain, (![A_71, B_72]: (m1_subset_1(k5_setfam_1(A_71, B_72), k1_zfmisc_1(A_71)) | ~m1_subset_1(B_72, k1_zfmisc_1(k1_zfmisc_1(A_71))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.73/1.40  tff(c_90, plain, (m1_subset_1(k3_tarski('#skF_4'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_63, c_83])).
% 2.73/1.40  tff(c_93, plain, (m1_subset_1(k3_tarski('#skF_4'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_90])).
% 2.73/1.40  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.40  tff(c_38, plain, (![B_62, A_63]: (m1_setfam_1(B_62, A_63) | ~r1_tarski(A_63, k3_tarski(B_62)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.73/1.40  tff(c_47, plain, (![B_62]: (m1_setfam_1(B_62, k3_tarski(B_62)))), inference(resolution, [status(thm)], [c_6, c_38])).
% 2.73/1.40  tff(c_32, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.73/1.40  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.73/1.40  tff(c_28, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.73/1.40  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.73/1.40  tff(c_34, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.73/1.40  tff(c_190, plain, (![A_95, C_96, B_94, E_97, D_93]: (m1_setfam_1(k6_funct_2(A_95, B_94, C_96, k7_funct_2(A_95, B_94, C_96, D_93)), E_97) | ~m1_setfam_1(D_93, E_97) | ~m1_subset_1(E_97, k1_zfmisc_1(A_95)) | ~m1_subset_1(D_93, k1_zfmisc_1(k1_zfmisc_1(A_95))) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))) | ~v1_funct_2(C_96, A_95, B_94) | ~v1_funct_1(C_96) | v1_xboole_0(B_94) | v1_xboole_0(A_95))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.73/1.40  tff(c_202, plain, (![B_94, C_96, E_97]: (m1_setfam_1(k6_funct_2('#skF_1', B_94, C_96, k7_funct_2('#skF_1', B_94, C_96, '#skF_4')), E_97) | ~m1_setfam_1('#skF_4', E_97) | ~m1_subset_1(E_97, k1_zfmisc_1('#skF_1')) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_94))) | ~v1_funct_2(C_96, '#skF_1', B_94) | ~v1_funct_1(C_96) | v1_xboole_0(B_94) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_190])).
% 2.73/1.40  tff(c_273, plain, (![B_103, C_104, E_105]: (m1_setfam_1(k6_funct_2('#skF_1', B_103, C_104, k7_funct_2('#skF_1', B_103, C_104, '#skF_4')), E_105) | ~m1_setfam_1('#skF_4', E_105) | ~m1_subset_1(E_105, k1_zfmisc_1('#skF_1')) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_103))) | ~v1_funct_2(C_104, '#skF_1', B_103) | ~v1_funct_1(C_104) | v1_xboole_0(B_103))), inference(negUnitSimplification, [status(thm)], [c_34, c_202])).
% 2.73/1.40  tff(c_281, plain, (![E_105]: (m1_setfam_1(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')), E_105) | ~m1_setfam_1('#skF_4', E_105) | ~m1_subset_1(E_105, k1_zfmisc_1('#skF_1')) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_273])).
% 2.73/1.40  tff(c_286, plain, (![E_105]: (m1_setfam_1(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')), E_105) | ~m1_setfam_1('#skF_4', E_105) | ~m1_subset_1(E_105, k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_281])).
% 2.73/1.40  tff(c_287, plain, (![E_105]: (m1_setfam_1(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')), E_105) | ~m1_setfam_1('#skF_4', E_105) | ~m1_subset_1(E_105, k1_zfmisc_1('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_32, c_286])).
% 2.73/1.40  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, k3_tarski(B_4)) | ~m1_setfam_1(B_4, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.73/1.40  tff(c_18, plain, (![A_13, B_14, C_15, D_16]: (m1_subset_1(k7_funct_2(A_13, B_14, C_15, D_16), k1_zfmisc_1(k1_zfmisc_1(B_14))) | ~m1_subset_1(D_16, k1_zfmisc_1(k1_zfmisc_1(A_13))) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_2(C_15, A_13, B_14) | ~v1_funct_1(C_15) | v1_xboole_0(B_14) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.73/1.40  tff(c_101, plain, (![A_75, B_76, C_77, D_78]: (m1_subset_1(k7_funct_2(A_75, B_76, C_77, D_78), k1_zfmisc_1(k1_zfmisc_1(B_76))) | ~m1_subset_1(D_78, k1_zfmisc_1(k1_zfmisc_1(A_75))) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | ~v1_funct_2(C_77, A_75, B_76) | ~v1_funct_1(C_77) | v1_xboole_0(B_76) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.73/1.40  tff(c_14, plain, (![A_7, B_8]: (k5_setfam_1(A_7, B_8)=k3_tarski(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(k1_zfmisc_1(A_7))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.73/1.40  tff(c_170, plain, (![B_89, A_90, C_91, D_92]: (k5_setfam_1(B_89, k7_funct_2(A_90, B_89, C_91, D_92))=k3_tarski(k7_funct_2(A_90, B_89, C_91, D_92)) | ~m1_subset_1(D_92, k1_zfmisc_1(k1_zfmisc_1(A_90))) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))) | ~v1_funct_2(C_91, A_90, B_89) | ~v1_funct_1(C_91) | v1_xboole_0(B_89) | v1_xboole_0(A_90))), inference(resolution, [status(thm)], [c_101, c_14])).
% 2.73/1.40  tff(c_182, plain, (![B_89, C_91]: (k5_setfam_1(B_89, k7_funct_2('#skF_1', B_89, C_91, '#skF_4'))=k3_tarski(k7_funct_2('#skF_1', B_89, C_91, '#skF_4')) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_89))) | ~v1_funct_2(C_91, '#skF_1', B_89) | ~v1_funct_1(C_91) | v1_xboole_0(B_89) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_170])).
% 2.73/1.40  tff(c_210, plain, (![B_98, C_99]: (k5_setfam_1(B_98, k7_funct_2('#skF_1', B_98, C_99, '#skF_4'))=k3_tarski(k7_funct_2('#skF_1', B_98, C_99, '#skF_4')) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_98))) | ~v1_funct_2(C_99, '#skF_1', B_98) | ~v1_funct_1(C_99) | v1_xboole_0(B_98))), inference(negUnitSimplification, [status(thm)], [c_34, c_182])).
% 2.73/1.40  tff(c_218, plain, (k5_setfam_1('#skF_2', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_tarski(k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_210])).
% 2.73/1.40  tff(c_223, plain, (k5_setfam_1('#skF_2', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_tarski(k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_218])).
% 2.73/1.40  tff(c_224, plain, (k5_setfam_1('#skF_2', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_tarski(k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_32, c_223])).
% 2.73/1.40  tff(c_12, plain, (![A_5, B_6]: (m1_subset_1(k5_setfam_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.73/1.40  tff(c_228, plain, (m1_subset_1(k3_tarski(k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_224, c_12])).
% 2.73/1.40  tff(c_232, plain, (~m1_subset_1(k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_228])).
% 2.73/1.40  tff(c_250, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_232])).
% 2.73/1.40  tff(c_253, plain, (v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_250])).
% 2.73/1.40  tff(c_255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_253])).
% 2.73/1.40  tff(c_257, plain, (m1_subset_1(k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitRight, [status(thm)], [c_228])).
% 2.73/1.40  tff(c_143, plain, (![A_83, B_84, C_85, D_86]: (m1_subset_1(k6_funct_2(A_83, B_84, C_85, D_86), k1_zfmisc_1(k1_zfmisc_1(A_83))) | ~m1_subset_1(D_86, k1_zfmisc_1(k1_zfmisc_1(B_84))) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_2(C_85, A_83, B_84) | ~v1_funct_1(C_85) | v1_xboole_0(B_84) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.73/1.40  tff(c_293, plain, (![A_107, B_108, C_109, D_110]: (k5_setfam_1(A_107, k6_funct_2(A_107, B_108, C_109, D_110))=k3_tarski(k6_funct_2(A_107, B_108, C_109, D_110)) | ~m1_subset_1(D_110, k1_zfmisc_1(k1_zfmisc_1(B_108))) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~v1_funct_2(C_109, A_107, B_108) | ~v1_funct_1(C_109) | v1_xboole_0(B_108) | v1_xboole_0(A_107))), inference(resolution, [status(thm)], [c_143, c_14])).
% 2.73/1.40  tff(c_295, plain, (![A_107, C_109]: (k5_setfam_1(A_107, k6_funct_2(A_107, '#skF_2', C_109, k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))=k3_tarski(k6_funct_2(A_107, '#skF_2', C_109, k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, '#skF_2'))) | ~v1_funct_2(C_109, A_107, '#skF_2') | ~v1_funct_1(C_109) | v1_xboole_0('#skF_2') | v1_xboole_0(A_107))), inference(resolution, [status(thm)], [c_257, c_293])).
% 2.73/1.40  tff(c_340, plain, (![A_114, C_115]: (k5_setfam_1(A_114, k6_funct_2(A_114, '#skF_2', C_115, k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))=k3_tarski(k6_funct_2(A_114, '#skF_2', C_115, k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_114, '#skF_2'))) | ~v1_funct_2(C_115, A_114, '#skF_2') | ~v1_funct_1(C_115) | v1_xboole_0(A_114))), inference(negUnitSimplification, [status(thm)], [c_32, c_295])).
% 2.73/1.40  tff(c_348, plain, (k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))=k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_340])).
% 2.73/1.40  tff(c_353, plain, (k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))=k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_348])).
% 2.73/1.40  tff(c_354, plain, (k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))=k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_34, c_353])).
% 2.73/1.40  tff(c_22, plain, (~r1_tarski(k5_setfam_1('#skF_1', '#skF_4'), k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.73/1.40  tff(c_64, plain, (~r1_tarski(k3_tarski('#skF_4'), k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_22])).
% 2.73/1.40  tff(c_355, plain, (~r1_tarski(k3_tarski('#skF_4'), k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_354, c_64])).
% 2.73/1.40  tff(c_366, plain, (~m1_setfam_1(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')), k3_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_355])).
% 2.73/1.40  tff(c_369, plain, (~m1_setfam_1('#skF_4', k3_tarski('#skF_4')) | ~m1_subset_1(k3_tarski('#skF_4'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_287, c_366])).
% 2.73/1.40  tff(c_373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_47, c_369])).
% 2.73/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.40  
% 2.73/1.40  Inference rules
% 2.73/1.40  ----------------------
% 2.73/1.40  #Ref     : 0
% 2.73/1.40  #Sup     : 73
% 2.73/1.40  #Fact    : 0
% 2.73/1.40  #Define  : 0
% 2.73/1.40  #Split   : 1
% 2.73/1.40  #Chain   : 0
% 2.73/1.40  #Close   : 0
% 2.73/1.40  
% 2.73/1.40  Ordering : KBO
% 2.73/1.40  
% 2.73/1.40  Simplification rules
% 2.73/1.40  ----------------------
% 2.73/1.40  #Subsume      : 0
% 2.73/1.40  #Demod        : 22
% 2.73/1.40  #Tautology    : 16
% 2.73/1.40  #SimpNegUnit  : 11
% 2.73/1.40  #BackRed      : 2
% 2.73/1.40  
% 2.73/1.40  #Partial instantiations: 0
% 2.73/1.40  #Strategies tried      : 1
% 2.73/1.40  
% 2.73/1.40  Timing (in seconds)
% 2.73/1.40  ----------------------
% 2.73/1.40  Preprocessing        : 0.33
% 2.73/1.40  Parsing              : 0.17
% 2.73/1.40  CNF conversion       : 0.03
% 2.73/1.40  Main loop            : 0.30
% 2.73/1.40  Inferencing          : 0.11
% 2.73/1.40  Reduction            : 0.08
% 2.73/1.40  Demodulation         : 0.06
% 2.73/1.40  BG Simplification    : 0.02
% 2.73/1.40  Subsumption          : 0.06
% 2.73/1.40  Abstraction          : 0.02
% 2.73/1.40  MUC search           : 0.00
% 2.73/1.40  Cooper               : 0.00
% 2.73/1.40  Total                : 0.67
% 2.73/1.40  Index Insertion      : 0.00
% 2.73/1.40  Index Deletion       : 0.00
% 2.73/1.40  Index Matching       : 0.00
% 2.73/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
