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
% DateTime   : Thu Dec  3 10:18:15 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 222 expanded)
%              Number of leaves         :   27 (  93 expanded)
%              Depth                    :   15
%              Number of atoms          :  215 ( 995 expanded)
%              Number of equality atoms :   33 ( 117 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C,D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,A)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
               => ! [E] :
                    ( ( v1_funct_1(E)
                      & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                   => ! [F] :
                        ( m1_subset_1(F,B)
                       => ( v1_partfun1(E,A)
                         => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k7_partfun1(C,E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_119,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C,D] :
              ( ( v1_funct_1(D)
                & v1_funct_2(D,B,A)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
             => ! [E] :
                  ( ( v1_funct_1(E)
                    & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                 => ! [F] :
                      ( m1_subset_1(F,B)
                     => ( v1_partfun1(E,A)
                       => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k1_funct_1(E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_partfun1(C,A)
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_funct_2)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_93,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( m1_subset_1(D,A)
                 => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

tff(c_22,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_30,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_76,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k3_funct_2(A_105,B_106,C_107,D_108) = k1_funct_1(C_107,D_108)
      | ~ m1_subset_1(D_108,A_105)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ v1_funct_2(C_107,A_105,B_106)
      | ~ v1_funct_1(C_107)
      | v1_xboole_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_82,plain,(
    ! [B_106,C_107] :
      ( k3_funct_2('#skF_2',B_106,C_107,'#skF_6') = k1_funct_1(C_107,'#skF_6')
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_106)))
      | ~ v1_funct_2(C_107,'#skF_2',B_106)
      | ~ v1_funct_1(C_107)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_76])).

tff(c_100,plain,(
    ! [B_111,C_112] :
      ( k3_funct_2('#skF_2',B_111,C_112,'#skF_6') = k1_funct_1(C_112,'#skF_6')
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_111)))
      | ~ v1_funct_2(C_112,'#skF_2',B_111)
      | ~ v1_funct_1(C_112) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_82])).

tff(c_103,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_100])).

tff(c_106,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_103])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_26,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_20,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_240,plain,(
    ! [A_130,C_133,B_131,E_134,F_132,D_135] :
      ( k3_funct_2(B_131,C_133,k8_funct_2(B_131,A_130,C_133,D_135,E_134),F_132) = k1_funct_1(E_134,k3_funct_2(B_131,A_130,D_135,F_132))
      | ~ v1_partfun1(E_134,A_130)
      | ~ m1_subset_1(F_132,B_131)
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_130,C_133)))
      | ~ v1_funct_1(E_134)
      | ~ m1_subset_1(D_135,k1_zfmisc_1(k2_zfmisc_1(B_131,A_130)))
      | ~ v1_funct_2(D_135,B_131,A_130)
      | ~ v1_funct_1(D_135)
      | v1_xboole_0(B_131)
      | v1_xboole_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_244,plain,(
    ! [B_131,D_135,F_132] :
      ( k3_funct_2(B_131,'#skF_3',k8_funct_2(B_131,'#skF_1','#skF_3',D_135,'#skF_5'),F_132) = k1_funct_1('#skF_5',k3_funct_2(B_131,'#skF_1',D_135,F_132))
      | ~ v1_partfun1('#skF_5','#skF_1')
      | ~ m1_subset_1(F_132,B_131)
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_135,k1_zfmisc_1(k2_zfmisc_1(B_131,'#skF_1')))
      | ~ v1_funct_2(D_135,B_131,'#skF_1')
      | ~ v1_funct_1(D_135)
      | v1_xboole_0(B_131)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_240])).

tff(c_251,plain,(
    ! [B_131,D_135,F_132] :
      ( k3_funct_2(B_131,'#skF_3',k8_funct_2(B_131,'#skF_1','#skF_3',D_135,'#skF_5'),F_132) = k1_funct_1('#skF_5',k3_funct_2(B_131,'#skF_1',D_135,F_132))
      | ~ m1_subset_1(F_132,B_131)
      | ~ m1_subset_1(D_135,k1_zfmisc_1(k2_zfmisc_1(B_131,'#skF_1')))
      | ~ v1_funct_2(D_135,B_131,'#skF_1')
      | ~ v1_funct_1(D_135)
      | v1_xboole_0(B_131)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20,c_244])).

tff(c_257,plain,(
    ! [B_141,D_142,F_143] :
      ( k3_funct_2(B_141,'#skF_3',k8_funct_2(B_141,'#skF_1','#skF_3',D_142,'#skF_5'),F_143) = k1_funct_1('#skF_5',k3_funct_2(B_141,'#skF_1',D_142,F_143))
      | ~ m1_subset_1(F_143,B_141)
      | ~ m1_subset_1(D_142,k1_zfmisc_1(k2_zfmisc_1(B_141,'#skF_1')))
      | ~ v1_funct_2(D_142,B_141,'#skF_1')
      | ~ v1_funct_1(D_142)
      | v1_xboole_0(B_141) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_251])).

tff(c_259,plain,(
    ! [F_143] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_143) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_143))
      | ~ m1_subset_1(F_143,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_257])).

tff(c_262,plain,(
    ! [F_143] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_143) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_143))
      | ~ m1_subset_1(F_143,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_259])).

tff(c_264,plain,(
    ! [F_144] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_144) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_144))
      | ~ m1_subset_1(F_144,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_262])).

tff(c_37,plain,(
    ! [C_95,A_96,B_97] :
      ( ~ v1_partfun1(C_95,A_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_xboole_0(B_97)
      | v1_xboole_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_43,plain,
    ( ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_37])).

tff(c_48,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_43])).

tff(c_49,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_48])).

tff(c_50,plain,(
    ! [C_98,A_99,B_100] :
      ( v1_funct_2(C_98,A_99,B_100)
      | ~ v1_partfun1(C_98,A_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ v1_funct_1(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_56,plain,
    ( v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_50])).

tff(c_62,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20,c_56])).

tff(c_63,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( m1_subset_1(k3_funct_2(A_101,B_102,C_103,D_104),B_102)
      | ~ m1_subset_1(D_104,A_101)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ v1_funct_2(C_103,A_101,B_102)
      | ~ v1_funct_1(C_103)
      | v1_xboole_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_65,plain,(
    ! [D_104] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_104),'#skF_1')
      | ~ m1_subset_1(D_104,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_63])).

tff(c_70,plain,(
    ! [D_104] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_104),'#skF_1')
      | ~ m1_subset_1(D_104,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_65])).

tff(c_88,plain,(
    ! [D_109] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_109),'#skF_1')
      | ~ m1_subset_1(D_109,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_70])).

tff(c_6,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( k3_funct_2(A_9,B_10,C_11,D_12) = k1_funct_1(C_11,D_12)
      | ~ m1_subset_1(D_12,A_9)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_2(C_11,A_9,B_10)
      | ~ v1_funct_1(C_11)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_90,plain,(
    ! [B_10,C_11,D_109] :
      ( k3_funct_2('#skF_1',B_10,C_11,k3_funct_2('#skF_2','#skF_1','#skF_4',D_109)) = k1_funct_1(C_11,k3_funct_2('#skF_2','#skF_1','#skF_4',D_109))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_10)))
      | ~ v1_funct_2(C_11,'#skF_1',B_10)
      | ~ v1_funct_1(C_11)
      | v1_xboole_0('#skF_1')
      | ~ m1_subset_1(D_109,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_88,c_6])).

tff(c_107,plain,(
    ! [B_113,C_114,D_115] :
      ( k3_funct_2('#skF_1',B_113,C_114,k3_funct_2('#skF_2','#skF_1','#skF_4',D_115)) = k1_funct_1(C_114,k3_funct_2('#skF_2','#skF_1','#skF_4',D_115))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_113)))
      | ~ v1_funct_2(C_114,'#skF_1',B_113)
      | ~ v1_funct_1(C_114)
      | ~ m1_subset_1(D_115,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_90])).

tff(c_109,plain,(
    ! [D_115] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',D_115)) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',D_115))
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_115,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_107])).

tff(c_128,plain,(
    ! [D_116] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',D_116)) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',D_116))
      | ~ m1_subset_1(D_116,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_62,c_109])).

tff(c_140,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_128])).

tff(c_144,plain,(
    k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_106,c_140])).

tff(c_71,plain,(
    ! [D_104] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_104),'#skF_1')
      | ~ m1_subset_1(D_104,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_70])).

tff(c_117,plain,
    ( m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_71])).

tff(c_121,plain,(
    m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_117])).

tff(c_154,plain,(
    ! [A_117,B_118,C_119,D_120] :
      ( k3_funct_2(A_117,B_118,C_119,D_120) = k7_partfun1(B_118,C_119,D_120)
      | ~ m1_subset_1(D_120,A_117)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | ~ v1_funct_2(C_119,A_117,B_118)
      | ~ v1_funct_1(C_119)
      | v1_xboole_0(B_118)
      | v1_xboole_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_156,plain,(
    ! [B_118,C_119] :
      ( k3_funct_2('#skF_1',B_118,C_119,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_118,C_119,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_118)))
      | ~ v1_funct_2(C_119,'#skF_1',B_118)
      | ~ v1_funct_1(C_119)
      | v1_xboole_0(B_118)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_121,c_154])).

tff(c_226,plain,(
    ! [B_126,C_127] :
      ( k3_funct_2('#skF_1',B_126,C_127,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_126,C_127,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_126)))
      | ~ v1_funct_2(C_127,'#skF_1',B_126)
      | ~ v1_funct_1(C_127)
      | v1_xboole_0(B_126) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_156])).

tff(c_229,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_226])).

tff(c_232,plain,
    ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_62,c_144,c_229])).

tff(c_233,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_232])).

tff(c_18,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_113,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_18])).

tff(c_234,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_113])).

tff(c_270,plain,
    ( k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_234])).

tff(c_277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_106,c_270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:33:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.36  
% 2.64/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.36  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.75/1.36  
% 2.75/1.36  %Foreground sorts:
% 2.75/1.36  
% 2.75/1.36  
% 2.75/1.36  %Background operators:
% 2.75/1.36  
% 2.75/1.36  
% 2.75/1.36  %Foreground operators:
% 2.75/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.75/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.36  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.75/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.75/1.36  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.75/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.75/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.36  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.75/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.75/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.75/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.75/1.36  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.75/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.36  
% 2.75/1.39  tff(f_146, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_funct_2)).
% 2.75/1.39  tff(f_62, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.75/1.39  tff(f_119, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_funct_2)).
% 2.75/1.39  tff(f_36, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_partfun1)).
% 2.75/1.39  tff(f_74, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_partfun1(C, A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_funct_2)).
% 2.75/1.39  tff(f_49, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 2.75/1.39  tff(f_93, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 2.75/1.39  tff(c_22, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.75/1.39  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.75/1.39  tff(c_30, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.75/1.39  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.75/1.39  tff(c_34, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.75/1.39  tff(c_76, plain, (![A_105, B_106, C_107, D_108]: (k3_funct_2(A_105, B_106, C_107, D_108)=k1_funct_1(C_107, D_108) | ~m1_subset_1(D_108, A_105) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))) | ~v1_funct_2(C_107, A_105, B_106) | ~v1_funct_1(C_107) | v1_xboole_0(A_105))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.75/1.39  tff(c_82, plain, (![B_106, C_107]: (k3_funct_2('#skF_2', B_106, C_107, '#skF_6')=k1_funct_1(C_107, '#skF_6') | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_106))) | ~v1_funct_2(C_107, '#skF_2', B_106) | ~v1_funct_1(C_107) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_76])).
% 2.75/1.39  tff(c_100, plain, (![B_111, C_112]: (k3_funct_2('#skF_2', B_111, C_112, '#skF_6')=k1_funct_1(C_112, '#skF_6') | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_111))) | ~v1_funct_2(C_112, '#skF_2', B_111) | ~v1_funct_1(C_112))), inference(negUnitSimplification, [status(thm)], [c_34, c_82])).
% 2.75/1.39  tff(c_103, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_100])).
% 2.75/1.39  tff(c_106, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_103])).
% 2.75/1.39  tff(c_36, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.75/1.39  tff(c_26, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.75/1.39  tff(c_20, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.75/1.39  tff(c_24, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.75/1.39  tff(c_240, plain, (![A_130, C_133, B_131, E_134, F_132, D_135]: (k3_funct_2(B_131, C_133, k8_funct_2(B_131, A_130, C_133, D_135, E_134), F_132)=k1_funct_1(E_134, k3_funct_2(B_131, A_130, D_135, F_132)) | ~v1_partfun1(E_134, A_130) | ~m1_subset_1(F_132, B_131) | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_130, C_133))) | ~v1_funct_1(E_134) | ~m1_subset_1(D_135, k1_zfmisc_1(k2_zfmisc_1(B_131, A_130))) | ~v1_funct_2(D_135, B_131, A_130) | ~v1_funct_1(D_135) | v1_xboole_0(B_131) | v1_xboole_0(A_130))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.75/1.39  tff(c_244, plain, (![B_131, D_135, F_132]: (k3_funct_2(B_131, '#skF_3', k8_funct_2(B_131, '#skF_1', '#skF_3', D_135, '#skF_5'), F_132)=k1_funct_1('#skF_5', k3_funct_2(B_131, '#skF_1', D_135, F_132)) | ~v1_partfun1('#skF_5', '#skF_1') | ~m1_subset_1(F_132, B_131) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_135, k1_zfmisc_1(k2_zfmisc_1(B_131, '#skF_1'))) | ~v1_funct_2(D_135, B_131, '#skF_1') | ~v1_funct_1(D_135) | v1_xboole_0(B_131) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_240])).
% 2.75/1.39  tff(c_251, plain, (![B_131, D_135, F_132]: (k3_funct_2(B_131, '#skF_3', k8_funct_2(B_131, '#skF_1', '#skF_3', D_135, '#skF_5'), F_132)=k1_funct_1('#skF_5', k3_funct_2(B_131, '#skF_1', D_135, F_132)) | ~m1_subset_1(F_132, B_131) | ~m1_subset_1(D_135, k1_zfmisc_1(k2_zfmisc_1(B_131, '#skF_1'))) | ~v1_funct_2(D_135, B_131, '#skF_1') | ~v1_funct_1(D_135) | v1_xboole_0(B_131) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20, c_244])).
% 2.75/1.39  tff(c_257, plain, (![B_141, D_142, F_143]: (k3_funct_2(B_141, '#skF_3', k8_funct_2(B_141, '#skF_1', '#skF_3', D_142, '#skF_5'), F_143)=k1_funct_1('#skF_5', k3_funct_2(B_141, '#skF_1', D_142, F_143)) | ~m1_subset_1(F_143, B_141) | ~m1_subset_1(D_142, k1_zfmisc_1(k2_zfmisc_1(B_141, '#skF_1'))) | ~v1_funct_2(D_142, B_141, '#skF_1') | ~v1_funct_1(D_142) | v1_xboole_0(B_141))), inference(negUnitSimplification, [status(thm)], [c_36, c_251])).
% 2.75/1.39  tff(c_259, plain, (![F_143]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_143)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_143)) | ~m1_subset_1(F_143, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_257])).
% 2.75/1.39  tff(c_262, plain, (![F_143]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_143)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_143)) | ~m1_subset_1(F_143, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_259])).
% 2.75/1.39  tff(c_264, plain, (![F_144]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_144)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_144)) | ~m1_subset_1(F_144, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_34, c_262])).
% 2.75/1.39  tff(c_37, plain, (![C_95, A_96, B_97]: (~v1_partfun1(C_95, A_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_xboole_0(B_97) | v1_xboole_0(A_96))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.75/1.39  tff(c_43, plain, (~v1_partfun1('#skF_5', '#skF_1') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_37])).
% 2.75/1.39  tff(c_48, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_43])).
% 2.75/1.39  tff(c_49, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_36, c_48])).
% 2.75/1.39  tff(c_50, plain, (![C_98, A_99, B_100]: (v1_funct_2(C_98, A_99, B_100) | ~v1_partfun1(C_98, A_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~v1_funct_1(C_98))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.75/1.39  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_50])).
% 2.75/1.39  tff(c_62, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20, c_56])).
% 2.75/1.39  tff(c_63, plain, (![A_101, B_102, C_103, D_104]: (m1_subset_1(k3_funct_2(A_101, B_102, C_103, D_104), B_102) | ~m1_subset_1(D_104, A_101) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~v1_funct_2(C_103, A_101, B_102) | ~v1_funct_1(C_103) | v1_xboole_0(A_101))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.75/1.39  tff(c_65, plain, (![D_104]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_104), '#skF_1') | ~m1_subset_1(D_104, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_63])).
% 2.75/1.39  tff(c_70, plain, (![D_104]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_104), '#skF_1') | ~m1_subset_1(D_104, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_65])).
% 2.75/1.39  tff(c_88, plain, (![D_109]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_109), '#skF_1') | ~m1_subset_1(D_109, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_34, c_70])).
% 2.75/1.39  tff(c_6, plain, (![A_9, B_10, C_11, D_12]: (k3_funct_2(A_9, B_10, C_11, D_12)=k1_funct_1(C_11, D_12) | ~m1_subset_1(D_12, A_9) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))) | ~v1_funct_2(C_11, A_9, B_10) | ~v1_funct_1(C_11) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.75/1.39  tff(c_90, plain, (![B_10, C_11, D_109]: (k3_funct_2('#skF_1', B_10, C_11, k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_109))=k1_funct_1(C_11, k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_109)) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_10))) | ~v1_funct_2(C_11, '#skF_1', B_10) | ~v1_funct_1(C_11) | v1_xboole_0('#skF_1') | ~m1_subset_1(D_109, '#skF_2'))), inference(resolution, [status(thm)], [c_88, c_6])).
% 2.75/1.39  tff(c_107, plain, (![B_113, C_114, D_115]: (k3_funct_2('#skF_1', B_113, C_114, k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_115))=k1_funct_1(C_114, k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_115)) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_113))) | ~v1_funct_2(C_114, '#skF_1', B_113) | ~v1_funct_1(C_114) | ~m1_subset_1(D_115, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_90])).
% 2.75/1.39  tff(c_109, plain, (![D_115]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_115))=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_115)) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_115, '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_107])).
% 2.75/1.39  tff(c_128, plain, (![D_116]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_116))=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_116)) | ~m1_subset_1(D_116, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_62, c_109])).
% 2.75/1.39  tff(c_140, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_106, c_128])).
% 2.75/1.39  tff(c_144, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_106, c_140])).
% 2.75/1.39  tff(c_71, plain, (![D_104]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_104), '#skF_1') | ~m1_subset_1(D_104, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_34, c_70])).
% 2.75/1.39  tff(c_117, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_106, c_71])).
% 2.75/1.39  tff(c_121, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_117])).
% 2.75/1.39  tff(c_154, plain, (![A_117, B_118, C_119, D_120]: (k3_funct_2(A_117, B_118, C_119, D_120)=k7_partfun1(B_118, C_119, D_120) | ~m1_subset_1(D_120, A_117) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | ~v1_funct_2(C_119, A_117, B_118) | ~v1_funct_1(C_119) | v1_xboole_0(B_118) | v1_xboole_0(A_117))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.75/1.39  tff(c_156, plain, (![B_118, C_119]: (k3_funct_2('#skF_1', B_118, C_119, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_118, C_119, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_118))) | ~v1_funct_2(C_119, '#skF_1', B_118) | ~v1_funct_1(C_119) | v1_xboole_0(B_118) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_121, c_154])).
% 2.75/1.39  tff(c_226, plain, (![B_126, C_127]: (k3_funct_2('#skF_1', B_126, C_127, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_126, C_127, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_126))) | ~v1_funct_2(C_127, '#skF_1', B_126) | ~v1_funct_1(C_127) | v1_xboole_0(B_126))), inference(negUnitSimplification, [status(thm)], [c_36, c_156])).
% 2.75/1.39  tff(c_229, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_226])).
% 2.75/1.39  tff(c_232, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_62, c_144, c_229])).
% 2.75/1.39  tff(c_233, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_49, c_232])).
% 2.75/1.39  tff(c_18, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.75/1.39  tff(c_113, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_18])).
% 2.75/1.39  tff(c_234, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_113])).
% 2.75/1.39  tff(c_270, plain, (k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_264, c_234])).
% 2.75/1.39  tff(c_277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_106, c_270])).
% 2.75/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.39  
% 2.75/1.39  Inference rules
% 2.75/1.39  ----------------------
% 2.75/1.39  #Ref     : 0
% 2.75/1.39  #Sup     : 48
% 2.75/1.39  #Fact    : 0
% 2.75/1.39  #Define  : 0
% 2.75/1.39  #Split   : 2
% 2.75/1.39  #Chain   : 0
% 2.75/1.39  #Close   : 0
% 2.75/1.39  
% 2.75/1.39  Ordering : KBO
% 2.75/1.39  
% 2.75/1.39  Simplification rules
% 2.75/1.39  ----------------------
% 2.75/1.39  #Subsume      : 1
% 2.75/1.39  #Demod        : 39
% 2.75/1.39  #Tautology    : 16
% 2.75/1.39  #SimpNegUnit  : 21
% 2.75/1.39  #BackRed      : 2
% 2.75/1.39  
% 2.75/1.39  #Partial instantiations: 0
% 2.75/1.39  #Strategies tried      : 1
% 2.75/1.39  
% 2.75/1.39  Timing (in seconds)
% 2.75/1.39  ----------------------
% 2.75/1.39  Preprocessing        : 0.36
% 2.75/1.39  Parsing              : 0.18
% 2.75/1.39  CNF conversion       : 0.04
% 2.75/1.39  Main loop            : 0.26
% 2.75/1.39  Inferencing          : 0.10
% 2.75/1.39  Reduction            : 0.08
% 2.75/1.39  Demodulation         : 0.05
% 2.75/1.39  BG Simplification    : 0.02
% 2.75/1.39  Subsumption          : 0.05
% 2.75/1.39  Abstraction          : 0.02
% 2.75/1.39  MUC search           : 0.00
% 2.75/1.39  Cooper               : 0.00
% 2.75/1.39  Total                : 0.66
% 2.75/1.39  Index Insertion      : 0.00
% 2.75/1.39  Index Deletion       : 0.00
% 2.75/1.39  Index Matching       : 0.00
% 2.75/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
