%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:13 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 222 expanded)
%              Number of leaves         :   27 (  93 expanded)
%              Depth                    :   15
%              Number of atoms          :  214 ( 993 expanded)
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

tff(f_144,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_117,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_91,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

tff(c_20,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_28,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_74,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k3_funct_2(A_105,B_106,C_107,D_108) = k1_funct_1(C_107,D_108)
      | ~ m1_subset_1(D_108,A_105)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ v1_funct_2(C_107,A_105,B_106)
      | ~ v1_funct_1(C_107)
      | v1_xboole_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_80,plain,(
    ! [B_106,C_107] :
      ( k3_funct_2('#skF_2',B_106,C_107,'#skF_6') = k1_funct_1(C_107,'#skF_6')
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_106)))
      | ~ v1_funct_2(C_107,'#skF_2',B_106)
      | ~ v1_funct_1(C_107)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_74])).

tff(c_98,plain,(
    ! [B_111,C_112] :
      ( k3_funct_2('#skF_2',B_111,C_112,'#skF_6') = k1_funct_1(C_112,'#skF_6')
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_111)))
      | ~ v1_funct_2(C_112,'#skF_2',B_111)
      | ~ v1_funct_1(C_112) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_80])).

tff(c_101,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_98])).

tff(c_104,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_101])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_24,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_18,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_238,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_242,plain,(
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
    inference(resolution,[status(thm)],[c_22,c_238])).

tff(c_249,plain,(
    ! [B_131,D_135,F_132] :
      ( k3_funct_2(B_131,'#skF_3',k8_funct_2(B_131,'#skF_1','#skF_3',D_135,'#skF_5'),F_132) = k1_funct_1('#skF_5',k3_funct_2(B_131,'#skF_1',D_135,F_132))
      | ~ m1_subset_1(F_132,B_131)
      | ~ m1_subset_1(D_135,k1_zfmisc_1(k2_zfmisc_1(B_131,'#skF_1')))
      | ~ v1_funct_2(D_135,B_131,'#skF_1')
      | ~ v1_funct_1(D_135)
      | v1_xboole_0(B_131)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_242])).

tff(c_255,plain,(
    ! [B_141,D_142,F_143] :
      ( k3_funct_2(B_141,'#skF_3',k8_funct_2(B_141,'#skF_1','#skF_3',D_142,'#skF_5'),F_143) = k1_funct_1('#skF_5',k3_funct_2(B_141,'#skF_1',D_142,F_143))
      | ~ m1_subset_1(F_143,B_141)
      | ~ m1_subset_1(D_142,k1_zfmisc_1(k2_zfmisc_1(B_141,'#skF_1')))
      | ~ v1_funct_2(D_142,B_141,'#skF_1')
      | ~ v1_funct_1(D_142)
      | v1_xboole_0(B_141) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_249])).

tff(c_257,plain,(
    ! [F_143] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_143) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_143))
      | ~ m1_subset_1(F_143,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_255])).

tff(c_260,plain,(
    ! [F_143] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_143) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_143))
      | ~ m1_subset_1(F_143,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_257])).

tff(c_262,plain,(
    ! [F_144] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_144) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_144))
      | ~ m1_subset_1(F_144,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_260])).

tff(c_35,plain,(
    ! [C_95,A_96,B_97] :
      ( ~ v1_partfun1(C_95,A_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_xboole_0(B_97)
      | v1_xboole_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_41,plain,
    ( ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_35])).

tff(c_46,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_41])).

tff(c_47,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_46])).

tff(c_48,plain,(
    ! [C_98,A_99,B_100] :
      ( v1_funct_2(C_98,A_99,B_100)
      | ~ v1_partfun1(C_98,A_99)
      | ~ v1_funct_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,
    ( v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_48])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_54])).

tff(c_61,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( m1_subset_1(k3_funct_2(A_101,B_102,C_103,D_104),B_102)
      | ~ m1_subset_1(D_104,A_101)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ v1_funct_2(C_103,A_101,B_102)
      | ~ v1_funct_1(C_103)
      | v1_xboole_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_63,plain,(
    ! [D_104] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_104),'#skF_1')
      | ~ m1_subset_1(D_104,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_61])).

tff(c_68,plain,(
    ! [D_104] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_104),'#skF_1')
      | ~ m1_subset_1(D_104,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_63])).

tff(c_86,plain,(
    ! [D_109] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_109),'#skF_1')
      | ~ m1_subset_1(D_109,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_68])).

tff(c_10,plain,(
    ! [A_12,B_13,C_14,D_15] :
      ( k3_funct_2(A_12,B_13,C_14,D_15) = k1_funct_1(C_14,D_15)
      | ~ m1_subset_1(D_15,A_12)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ v1_funct_2(C_14,A_12,B_13)
      | ~ v1_funct_1(C_14)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_88,plain,(
    ! [B_13,C_14,D_109] :
      ( k3_funct_2('#skF_1',B_13,C_14,k3_funct_2('#skF_2','#skF_1','#skF_4',D_109)) = k1_funct_1(C_14,k3_funct_2('#skF_2','#skF_1','#skF_4',D_109))
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_13)))
      | ~ v1_funct_2(C_14,'#skF_1',B_13)
      | ~ v1_funct_1(C_14)
      | v1_xboole_0('#skF_1')
      | ~ m1_subset_1(D_109,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_86,c_10])).

tff(c_105,plain,(
    ! [B_113,C_114,D_115] :
      ( k3_funct_2('#skF_1',B_113,C_114,k3_funct_2('#skF_2','#skF_1','#skF_4',D_115)) = k1_funct_1(C_114,k3_funct_2('#skF_2','#skF_1','#skF_4',D_115))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_113)))
      | ~ v1_funct_2(C_114,'#skF_1',B_113)
      | ~ v1_funct_1(C_114)
      | ~ m1_subset_1(D_115,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_88])).

tff(c_107,plain,(
    ! [D_115] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',D_115)) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',D_115))
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_115,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_105])).

tff(c_126,plain,(
    ! [D_116] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',D_116)) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',D_116))
      | ~ m1_subset_1(D_116,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_60,c_107])).

tff(c_138,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_126])).

tff(c_142,plain,(
    k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_104,c_138])).

tff(c_69,plain,(
    ! [D_104] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_104),'#skF_1')
      | ~ m1_subset_1(D_104,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_68])).

tff(c_115,plain,
    ( m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_69])).

tff(c_119,plain,(
    m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_115])).

tff(c_152,plain,(
    ! [A_117,B_118,C_119,D_120] :
      ( k3_funct_2(A_117,B_118,C_119,D_120) = k7_partfun1(B_118,C_119,D_120)
      | ~ m1_subset_1(D_120,A_117)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | ~ v1_funct_2(C_119,A_117,B_118)
      | ~ v1_funct_1(C_119)
      | v1_xboole_0(B_118)
      | v1_xboole_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_154,plain,(
    ! [B_118,C_119] :
      ( k3_funct_2('#skF_1',B_118,C_119,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_118,C_119,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_118)))
      | ~ v1_funct_2(C_119,'#skF_1',B_118)
      | ~ v1_funct_1(C_119)
      | v1_xboole_0(B_118)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_119,c_152])).

tff(c_224,plain,(
    ! [B_126,C_127] :
      ( k3_funct_2('#skF_1',B_126,C_127,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_126,C_127,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_126)))
      | ~ v1_funct_2(C_127,'#skF_1',B_126)
      | ~ v1_funct_1(C_127)
      | v1_xboole_0(B_126) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_154])).

tff(c_227,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_224])).

tff(c_230,plain,
    ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_60,c_142,c_227])).

tff(c_231,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_230])).

tff(c_16,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_111,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_16])).

tff(c_232,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_111])).

tff(c_268,plain,
    ( k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_232])).

tff(c_275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_104,c_268])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:22:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.85  
% 3.14/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.85  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.14/1.85  
% 3.14/1.85  %Foreground sorts:
% 3.14/1.85  
% 3.14/1.85  
% 3.14/1.85  %Background operators:
% 3.14/1.85  
% 3.14/1.85  
% 3.14/1.85  %Foreground operators:
% 3.14/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.14/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.85  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.14/1.85  tff('#skF_5', type, '#skF_5': $i).
% 3.14/1.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.14/1.85  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.14/1.85  tff('#skF_6', type, '#skF_6': $i).
% 3.14/1.85  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.85  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.14/1.85  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.85  tff('#skF_1', type, '#skF_1': $i).
% 3.14/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.85  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.14/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.14/1.85  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.85  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.14/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.85  
% 3.14/1.89  tff(f_144, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_funct_2)).
% 3.14/1.89  tff(f_72, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.14/1.89  tff(f_117, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_funct_2)).
% 3.14/1.89  tff(f_46, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_partfun1)).
% 3.14/1.89  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 3.14/1.89  tff(f_59, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 3.14/1.89  tff(f_91, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_2)).
% 3.14/1.89  tff(c_20, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.14/1.89  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.14/1.89  tff(c_28, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.14/1.89  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.14/1.89  tff(c_32, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.14/1.89  tff(c_74, plain, (![A_105, B_106, C_107, D_108]: (k3_funct_2(A_105, B_106, C_107, D_108)=k1_funct_1(C_107, D_108) | ~m1_subset_1(D_108, A_105) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))) | ~v1_funct_2(C_107, A_105, B_106) | ~v1_funct_1(C_107) | v1_xboole_0(A_105))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.14/1.89  tff(c_80, plain, (![B_106, C_107]: (k3_funct_2('#skF_2', B_106, C_107, '#skF_6')=k1_funct_1(C_107, '#skF_6') | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_106))) | ~v1_funct_2(C_107, '#skF_2', B_106) | ~v1_funct_1(C_107) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_74])).
% 3.14/1.89  tff(c_98, plain, (![B_111, C_112]: (k3_funct_2('#skF_2', B_111, C_112, '#skF_6')=k1_funct_1(C_112, '#skF_6') | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_111))) | ~v1_funct_2(C_112, '#skF_2', B_111) | ~v1_funct_1(C_112))), inference(negUnitSimplification, [status(thm)], [c_32, c_80])).
% 3.14/1.89  tff(c_101, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_98])).
% 3.14/1.89  tff(c_104, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_101])).
% 3.14/1.89  tff(c_34, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.14/1.89  tff(c_24, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.14/1.89  tff(c_18, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.14/1.89  tff(c_22, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.14/1.89  tff(c_238, plain, (![A_130, C_133, B_131, E_134, F_132, D_135]: (k3_funct_2(B_131, C_133, k8_funct_2(B_131, A_130, C_133, D_135, E_134), F_132)=k1_funct_1(E_134, k3_funct_2(B_131, A_130, D_135, F_132)) | ~v1_partfun1(E_134, A_130) | ~m1_subset_1(F_132, B_131) | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_130, C_133))) | ~v1_funct_1(E_134) | ~m1_subset_1(D_135, k1_zfmisc_1(k2_zfmisc_1(B_131, A_130))) | ~v1_funct_2(D_135, B_131, A_130) | ~v1_funct_1(D_135) | v1_xboole_0(B_131) | v1_xboole_0(A_130))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.14/1.89  tff(c_242, plain, (![B_131, D_135, F_132]: (k3_funct_2(B_131, '#skF_3', k8_funct_2(B_131, '#skF_1', '#skF_3', D_135, '#skF_5'), F_132)=k1_funct_1('#skF_5', k3_funct_2(B_131, '#skF_1', D_135, F_132)) | ~v1_partfun1('#skF_5', '#skF_1') | ~m1_subset_1(F_132, B_131) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_135, k1_zfmisc_1(k2_zfmisc_1(B_131, '#skF_1'))) | ~v1_funct_2(D_135, B_131, '#skF_1') | ~v1_funct_1(D_135) | v1_xboole_0(B_131) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_238])).
% 3.14/1.89  tff(c_249, plain, (![B_131, D_135, F_132]: (k3_funct_2(B_131, '#skF_3', k8_funct_2(B_131, '#skF_1', '#skF_3', D_135, '#skF_5'), F_132)=k1_funct_1('#skF_5', k3_funct_2(B_131, '#skF_1', D_135, F_132)) | ~m1_subset_1(F_132, B_131) | ~m1_subset_1(D_135, k1_zfmisc_1(k2_zfmisc_1(B_131, '#skF_1'))) | ~v1_funct_2(D_135, B_131, '#skF_1') | ~v1_funct_1(D_135) | v1_xboole_0(B_131) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_242])).
% 3.14/1.89  tff(c_255, plain, (![B_141, D_142, F_143]: (k3_funct_2(B_141, '#skF_3', k8_funct_2(B_141, '#skF_1', '#skF_3', D_142, '#skF_5'), F_143)=k1_funct_1('#skF_5', k3_funct_2(B_141, '#skF_1', D_142, F_143)) | ~m1_subset_1(F_143, B_141) | ~m1_subset_1(D_142, k1_zfmisc_1(k2_zfmisc_1(B_141, '#skF_1'))) | ~v1_funct_2(D_142, B_141, '#skF_1') | ~v1_funct_1(D_142) | v1_xboole_0(B_141))), inference(negUnitSimplification, [status(thm)], [c_34, c_249])).
% 3.14/1.89  tff(c_257, plain, (![F_143]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_143)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_143)) | ~m1_subset_1(F_143, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_255])).
% 3.14/1.89  tff(c_260, plain, (![F_143]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_143)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_143)) | ~m1_subset_1(F_143, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_257])).
% 3.14/1.89  tff(c_262, plain, (![F_144]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_144)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_144)) | ~m1_subset_1(F_144, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_260])).
% 3.14/1.89  tff(c_35, plain, (![C_95, A_96, B_97]: (~v1_partfun1(C_95, A_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_xboole_0(B_97) | v1_xboole_0(A_96))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.14/1.89  tff(c_41, plain, (~v1_partfun1('#skF_5', '#skF_1') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_35])).
% 3.14/1.89  tff(c_46, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_41])).
% 3.14/1.89  tff(c_47, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_46])).
% 3.14/1.89  tff(c_48, plain, (![C_98, A_99, B_100]: (v1_funct_2(C_98, A_99, B_100) | ~v1_partfun1(C_98, A_99) | ~v1_funct_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.14/1.89  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_48])).
% 3.14/1.89  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_54])).
% 3.14/1.89  tff(c_61, plain, (![A_101, B_102, C_103, D_104]: (m1_subset_1(k3_funct_2(A_101, B_102, C_103, D_104), B_102) | ~m1_subset_1(D_104, A_101) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~v1_funct_2(C_103, A_101, B_102) | ~v1_funct_1(C_103) | v1_xboole_0(A_101))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.14/1.89  tff(c_63, plain, (![D_104]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_104), '#skF_1') | ~m1_subset_1(D_104, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_61])).
% 3.14/1.89  tff(c_68, plain, (![D_104]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_104), '#skF_1') | ~m1_subset_1(D_104, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_63])).
% 3.14/1.89  tff(c_86, plain, (![D_109]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_109), '#skF_1') | ~m1_subset_1(D_109, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_68])).
% 3.14/1.89  tff(c_10, plain, (![A_12, B_13, C_14, D_15]: (k3_funct_2(A_12, B_13, C_14, D_15)=k1_funct_1(C_14, D_15) | ~m1_subset_1(D_15, A_12) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))) | ~v1_funct_2(C_14, A_12, B_13) | ~v1_funct_1(C_14) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.14/1.89  tff(c_88, plain, (![B_13, C_14, D_109]: (k3_funct_2('#skF_1', B_13, C_14, k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_109))=k1_funct_1(C_14, k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_109)) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_13))) | ~v1_funct_2(C_14, '#skF_1', B_13) | ~v1_funct_1(C_14) | v1_xboole_0('#skF_1') | ~m1_subset_1(D_109, '#skF_2'))), inference(resolution, [status(thm)], [c_86, c_10])).
% 3.14/1.89  tff(c_105, plain, (![B_113, C_114, D_115]: (k3_funct_2('#skF_1', B_113, C_114, k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_115))=k1_funct_1(C_114, k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_115)) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_113))) | ~v1_funct_2(C_114, '#skF_1', B_113) | ~v1_funct_1(C_114) | ~m1_subset_1(D_115, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_34, c_88])).
% 3.14/1.89  tff(c_107, plain, (![D_115]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_115))=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_115)) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_115, '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_105])).
% 3.14/1.89  tff(c_126, plain, (![D_116]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_116))=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_116)) | ~m1_subset_1(D_116, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_60, c_107])).
% 3.14/1.89  tff(c_138, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_104, c_126])).
% 3.14/1.89  tff(c_142, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_104, c_138])).
% 3.14/1.89  tff(c_69, plain, (![D_104]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_104), '#skF_1') | ~m1_subset_1(D_104, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_68])).
% 3.14/1.89  tff(c_115, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_104, c_69])).
% 3.14/1.89  tff(c_119, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_115])).
% 3.14/1.89  tff(c_152, plain, (![A_117, B_118, C_119, D_120]: (k3_funct_2(A_117, B_118, C_119, D_120)=k7_partfun1(B_118, C_119, D_120) | ~m1_subset_1(D_120, A_117) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | ~v1_funct_2(C_119, A_117, B_118) | ~v1_funct_1(C_119) | v1_xboole_0(B_118) | v1_xboole_0(A_117))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.14/1.89  tff(c_154, plain, (![B_118, C_119]: (k3_funct_2('#skF_1', B_118, C_119, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_118, C_119, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_118))) | ~v1_funct_2(C_119, '#skF_1', B_118) | ~v1_funct_1(C_119) | v1_xboole_0(B_118) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_119, c_152])).
% 3.14/1.89  tff(c_224, plain, (![B_126, C_127]: (k3_funct_2('#skF_1', B_126, C_127, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_126, C_127, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_126))) | ~v1_funct_2(C_127, '#skF_1', B_126) | ~v1_funct_1(C_127) | v1_xboole_0(B_126))), inference(negUnitSimplification, [status(thm)], [c_34, c_154])).
% 3.14/1.89  tff(c_227, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_224])).
% 3.14/1.89  tff(c_230, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_60, c_142, c_227])).
% 3.14/1.89  tff(c_231, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_47, c_230])).
% 3.14/1.89  tff(c_16, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.14/1.89  tff(c_111, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_16])).
% 3.14/1.89  tff(c_232, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_111])).
% 3.14/1.89  tff(c_268, plain, (k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_262, c_232])).
% 3.14/1.89  tff(c_275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_104, c_268])).
% 3.14/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.89  
% 3.14/1.89  Inference rules
% 3.14/1.89  ----------------------
% 3.14/1.89  #Ref     : 0
% 3.14/1.89  #Sup     : 48
% 3.14/1.89  #Fact    : 0
% 3.14/1.89  #Define  : 0
% 3.14/1.89  #Split   : 2
% 3.14/1.89  #Chain   : 0
% 3.14/1.89  #Close   : 0
% 3.14/1.89  
% 3.14/1.89  Ordering : KBO
% 3.14/1.89  
% 3.14/1.89  Simplification rules
% 3.14/1.89  ----------------------
% 3.14/1.89  #Subsume      : 1
% 3.14/1.89  #Demod        : 39
% 3.14/1.89  #Tautology    : 15
% 3.14/1.89  #SimpNegUnit  : 21
% 3.14/1.89  #BackRed      : 2
% 3.14/1.89  
% 3.14/1.89  #Partial instantiations: 0
% 3.14/1.89  #Strategies tried      : 1
% 3.14/1.89  
% 3.14/1.89  Timing (in seconds)
% 3.14/1.89  ----------------------
% 3.14/1.89  Preprocessing        : 0.53
% 3.14/1.89  Parsing              : 0.27
% 3.14/1.89  CNF conversion       : 0.06
% 3.14/1.89  Main loop            : 0.40
% 3.14/1.89  Inferencing          : 0.15
% 3.14/1.89  Reduction            : 0.12
% 3.14/1.89  Demodulation         : 0.08
% 3.14/1.89  BG Simplification    : 0.03
% 3.14/1.89  Subsumption          : 0.08
% 3.14/1.90  Abstraction          : 0.02
% 3.14/1.90  MUC search           : 0.00
% 3.14/1.90  Cooper               : 0.00
% 3.14/1.90  Total                : 1.00
% 3.14/1.90  Index Insertion      : 0.00
% 3.14/1.90  Index Deletion       : 0.00
% 3.14/1.90  Index Matching       : 0.00
% 3.14/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
