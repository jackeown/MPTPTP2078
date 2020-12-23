%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:15 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 206 expanded)
%              Number of leaves         :   27 (  87 expanded)
%              Depth                    :   16
%              Number of atoms          :  206 ( 911 expanded)
%              Number of equality atoms :   31 ( 104 expanded)
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

tff(f_147,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_120,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_partfun1(C,A)
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_funct_2)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',ie1_funct_2)).

tff(c_24,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_32,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_85,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( k3_funct_2(A_100,B_101,C_102,D_103) = k1_funct_1(C_102,D_103)
      | ~ m1_subset_1(D_103,A_100)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ v1_funct_2(C_102,A_100,B_101)
      | ~ v1_funct_1(C_102)
      | v1_xboole_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_95,plain,(
    ! [B_101,C_102] :
      ( k3_funct_2('#skF_2',B_101,C_102,'#skF_6') = k1_funct_1(C_102,'#skF_6')
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_101)))
      | ~ v1_funct_2(C_102,'#skF_2',B_101)
      | ~ v1_funct_1(C_102)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_85])).

tff(c_107,plain,(
    ! [B_104,C_105] :
      ( k3_funct_2('#skF_2',B_104,C_105,'#skF_6') = k1_funct_1(C_105,'#skF_6')
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_104)))
      | ~ v1_funct_2(C_105,'#skF_2',B_104)
      | ~ v1_funct_1(C_105) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_95])).

tff(c_110,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_107])).

tff(c_113,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_110])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_28,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_22,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_215,plain,(
    ! [F_128,E_125,A_126,D_124,B_127,C_129] :
      ( k3_funct_2(B_127,C_129,k8_funct_2(B_127,A_126,C_129,D_124,E_125),F_128) = k1_funct_1(E_125,k3_funct_2(B_127,A_126,D_124,F_128))
      | ~ v1_partfun1(E_125,A_126)
      | ~ m1_subset_1(F_128,B_127)
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_126,C_129)))
      | ~ v1_funct_1(E_125)
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(B_127,A_126)))
      | ~ v1_funct_2(D_124,B_127,A_126)
      | ~ v1_funct_1(D_124)
      | v1_xboole_0(B_127)
      | v1_xboole_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_219,plain,(
    ! [B_127,D_124,F_128] :
      ( k3_funct_2(B_127,'#skF_3',k8_funct_2(B_127,'#skF_1','#skF_3',D_124,'#skF_5'),F_128) = k1_funct_1('#skF_5',k3_funct_2(B_127,'#skF_1',D_124,F_128))
      | ~ v1_partfun1('#skF_5','#skF_1')
      | ~ m1_subset_1(F_128,B_127)
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(B_127,'#skF_1')))
      | ~ v1_funct_2(D_124,B_127,'#skF_1')
      | ~ v1_funct_1(D_124)
      | v1_xboole_0(B_127)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_215])).

tff(c_226,plain,(
    ! [B_127,D_124,F_128] :
      ( k3_funct_2(B_127,'#skF_3',k8_funct_2(B_127,'#skF_1','#skF_3',D_124,'#skF_5'),F_128) = k1_funct_1('#skF_5',k3_funct_2(B_127,'#skF_1',D_124,F_128))
      | ~ m1_subset_1(F_128,B_127)
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(B_127,'#skF_1')))
      | ~ v1_funct_2(D_124,B_127,'#skF_1')
      | ~ v1_funct_1(D_124)
      | v1_xboole_0(B_127)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_219])).

tff(c_262,plain,(
    ! [B_134,D_135,F_136] :
      ( k3_funct_2(B_134,'#skF_3',k8_funct_2(B_134,'#skF_1','#skF_3',D_135,'#skF_5'),F_136) = k1_funct_1('#skF_5',k3_funct_2(B_134,'#skF_1',D_135,F_136))
      | ~ m1_subset_1(F_136,B_134)
      | ~ m1_subset_1(D_135,k1_zfmisc_1(k2_zfmisc_1(B_134,'#skF_1')))
      | ~ v1_funct_2(D_135,B_134,'#skF_1')
      | ~ v1_funct_1(D_135)
      | v1_xboole_0(B_134) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_226])).

tff(c_264,plain,(
    ! [F_136] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_136) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_136))
      | ~ m1_subset_1(F_136,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_262])).

tff(c_267,plain,(
    ! [F_136] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_136) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_136))
      | ~ m1_subset_1(F_136,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_264])).

tff(c_269,plain,(
    ! [F_137] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_137) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_137))
      | ~ m1_subset_1(F_137,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_267])).

tff(c_44,plain,(
    ! [C_88,A_89,B_90] :
      ( ~ v1_partfun1(C_88,A_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ v1_xboole_0(B_90)
      | v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_50,plain,
    ( ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_44])).

tff(c_55,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_50])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_55])).

tff(c_57,plain,(
    ! [C_91,A_92,B_93] :
      ( v1_funct_2(C_91,A_92,B_93)
      | ~ v1_partfun1(C_91,A_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ v1_funct_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_63,plain,
    ( v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_57])).

tff(c_69,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_63])).

tff(c_70,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( m1_subset_1(k3_funct_2(A_94,B_95,C_96,D_97),B_95)
      | ~ m1_subset_1(D_97,A_94)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ v1_funct_2(C_96,A_94,B_95)
      | ~ v1_funct_1(C_96)
      | v1_xboole_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_72,plain,(
    ! [D_97] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_97),'#skF_1')
      | ~ m1_subset_1(D_97,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_70])).

tff(c_77,plain,(
    ! [D_97] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_97),'#skF_1')
      | ~ m1_subset_1(D_97,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_72])).

tff(c_78,plain,(
    ! [D_97] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_97),'#skF_1')
      | ~ m1_subset_1(D_97,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_77])).

tff(c_118,plain,
    ( m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_78])).

tff(c_122,plain,(
    m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_118])).

tff(c_10,plain,(
    ! [A_15,B_16,C_17,D_18] :
      ( k3_funct_2(A_15,B_16,C_17,D_18) = k1_funct_1(C_17,D_18)
      | ~ m1_subset_1(D_18,A_15)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | ~ v1_funct_2(C_17,A_15,B_16)
      | ~ v1_funct_1(C_17)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_125,plain,(
    ! [B_16,C_17] :
      ( k3_funct_2('#skF_1',B_16,C_17,k1_funct_1('#skF_4','#skF_6')) = k1_funct_1(C_17,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_16)))
      | ~ v1_funct_2(C_17,'#skF_1',B_16)
      | ~ v1_funct_1(C_17)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_122,c_10])).

tff(c_129,plain,(
    ! [B_106,C_107] :
      ( k3_funct_2('#skF_1',B_106,C_107,k1_funct_1('#skF_4','#skF_6')) = k1_funct_1(C_107,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_106)))
      | ~ v1_funct_2(C_107,'#skF_1',B_106)
      | ~ v1_funct_1(C_107) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_125])).

tff(c_132,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_129])).

tff(c_135,plain,(
    k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_69,c_132])).

tff(c_145,plain,(
    ! [A_108,B_109,C_110,D_111] :
      ( k3_funct_2(A_108,B_109,C_110,D_111) = k7_partfun1(B_109,C_110,D_111)
      | ~ m1_subset_1(D_111,A_108)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ v1_funct_2(C_110,A_108,B_109)
      | ~ v1_funct_1(C_110)
      | v1_xboole_0(B_109)
      | v1_xboole_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_147,plain,(
    ! [B_109,C_110] :
      ( k3_funct_2('#skF_1',B_109,C_110,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_109,C_110,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_109)))
      | ~ v1_funct_2(C_110,'#skF_1',B_109)
      | ~ v1_funct_1(C_110)
      | v1_xboole_0(B_109)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_122,c_145])).

tff(c_194,plain,(
    ! [B_114,C_115] :
      ( k3_funct_2('#skF_1',B_114,C_115,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_114,C_115,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_114)))
      | ~ v1_funct_2(C_115,'#skF_1',B_114)
      | ~ v1_funct_1(C_115)
      | v1_xboole_0(B_114) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_147])).

tff(c_197,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_194])).

tff(c_200,plain,
    ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_69,c_135,c_197])).

tff(c_201,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_200])).

tff(c_20,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_114,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_20])).

tff(c_202,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_114])).

tff(c_275,plain,
    ( k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_202])).

tff(c_282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_113,c_275])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n010.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 15:18:29 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.30  
% 2.42/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.30  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.42/1.30  
% 2.42/1.30  %Foreground sorts:
% 2.42/1.30  
% 2.42/1.30  
% 2.42/1.30  %Background operators:
% 2.42/1.30  
% 2.42/1.30  
% 2.42/1.30  %Foreground operators:
% 2.42/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.42/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.30  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.42/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.42/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.42/1.30  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.42/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.42/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.30  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.42/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.42/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.42/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.42/1.30  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.42/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.30  
% 2.67/1.32  tff(f_147, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_funct_2)).
% 2.67/1.32  tff(f_82, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.67/1.32  tff(f_120, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_funct_2)).
% 2.67/1.32  tff(f_40, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_partfun1)).
% 2.67/1.32  tff(f_94, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_partfun1(C, A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_funct_2)).
% 2.67/1.32  tff(f_53, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 2.67/1.32  tff(f_69, axiom, (![A, B, C, D]: ((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', ie1_funct_2)).
% 2.67/1.32  tff(c_24, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.67/1.32  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.67/1.32  tff(c_32, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.67/1.32  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.67/1.32  tff(c_36, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.67/1.32  tff(c_85, plain, (![A_100, B_101, C_102, D_103]: (k3_funct_2(A_100, B_101, C_102, D_103)=k1_funct_1(C_102, D_103) | ~m1_subset_1(D_103, A_100) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~v1_funct_2(C_102, A_100, B_101) | ~v1_funct_1(C_102) | v1_xboole_0(A_100))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.67/1.32  tff(c_95, plain, (![B_101, C_102]: (k3_funct_2('#skF_2', B_101, C_102, '#skF_6')=k1_funct_1(C_102, '#skF_6') | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_101))) | ~v1_funct_2(C_102, '#skF_2', B_101) | ~v1_funct_1(C_102) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_85])).
% 2.67/1.32  tff(c_107, plain, (![B_104, C_105]: (k3_funct_2('#skF_2', B_104, C_105, '#skF_6')=k1_funct_1(C_105, '#skF_6') | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_104))) | ~v1_funct_2(C_105, '#skF_2', B_104) | ~v1_funct_1(C_105))), inference(negUnitSimplification, [status(thm)], [c_36, c_95])).
% 2.67/1.32  tff(c_110, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_107])).
% 2.67/1.32  tff(c_113, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_110])).
% 2.67/1.32  tff(c_38, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.67/1.32  tff(c_28, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.67/1.32  tff(c_22, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.67/1.32  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.67/1.32  tff(c_215, plain, (![F_128, E_125, A_126, D_124, B_127, C_129]: (k3_funct_2(B_127, C_129, k8_funct_2(B_127, A_126, C_129, D_124, E_125), F_128)=k1_funct_1(E_125, k3_funct_2(B_127, A_126, D_124, F_128)) | ~v1_partfun1(E_125, A_126) | ~m1_subset_1(F_128, B_127) | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_126, C_129))) | ~v1_funct_1(E_125) | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(B_127, A_126))) | ~v1_funct_2(D_124, B_127, A_126) | ~v1_funct_1(D_124) | v1_xboole_0(B_127) | v1_xboole_0(A_126))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.67/1.32  tff(c_219, plain, (![B_127, D_124, F_128]: (k3_funct_2(B_127, '#skF_3', k8_funct_2(B_127, '#skF_1', '#skF_3', D_124, '#skF_5'), F_128)=k1_funct_1('#skF_5', k3_funct_2(B_127, '#skF_1', D_124, F_128)) | ~v1_partfun1('#skF_5', '#skF_1') | ~m1_subset_1(F_128, B_127) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(B_127, '#skF_1'))) | ~v1_funct_2(D_124, B_127, '#skF_1') | ~v1_funct_1(D_124) | v1_xboole_0(B_127) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_215])).
% 2.67/1.32  tff(c_226, plain, (![B_127, D_124, F_128]: (k3_funct_2(B_127, '#skF_3', k8_funct_2(B_127, '#skF_1', '#skF_3', D_124, '#skF_5'), F_128)=k1_funct_1('#skF_5', k3_funct_2(B_127, '#skF_1', D_124, F_128)) | ~m1_subset_1(F_128, B_127) | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(B_127, '#skF_1'))) | ~v1_funct_2(D_124, B_127, '#skF_1') | ~v1_funct_1(D_124) | v1_xboole_0(B_127) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_219])).
% 2.67/1.32  tff(c_262, plain, (![B_134, D_135, F_136]: (k3_funct_2(B_134, '#skF_3', k8_funct_2(B_134, '#skF_1', '#skF_3', D_135, '#skF_5'), F_136)=k1_funct_1('#skF_5', k3_funct_2(B_134, '#skF_1', D_135, F_136)) | ~m1_subset_1(F_136, B_134) | ~m1_subset_1(D_135, k1_zfmisc_1(k2_zfmisc_1(B_134, '#skF_1'))) | ~v1_funct_2(D_135, B_134, '#skF_1') | ~v1_funct_1(D_135) | v1_xboole_0(B_134))), inference(negUnitSimplification, [status(thm)], [c_38, c_226])).
% 2.67/1.32  tff(c_264, plain, (![F_136]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_136)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_136)) | ~m1_subset_1(F_136, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_262])).
% 2.67/1.32  tff(c_267, plain, (![F_136]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_136)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_136)) | ~m1_subset_1(F_136, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_264])).
% 2.67/1.32  tff(c_269, plain, (![F_137]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_137)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_137)) | ~m1_subset_1(F_137, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_267])).
% 2.67/1.32  tff(c_44, plain, (![C_88, A_89, B_90]: (~v1_partfun1(C_88, A_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~v1_xboole_0(B_90) | v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.67/1.32  tff(c_50, plain, (~v1_partfun1('#skF_5', '#skF_1') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_44])).
% 2.67/1.32  tff(c_55, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_50])).
% 2.67/1.32  tff(c_56, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_55])).
% 2.67/1.32  tff(c_57, plain, (![C_91, A_92, B_93]: (v1_funct_2(C_91, A_92, B_93) | ~v1_partfun1(C_91, A_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~v1_funct_1(C_91))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.67/1.32  tff(c_63, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_57])).
% 2.67/1.32  tff(c_69, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_63])).
% 2.67/1.32  tff(c_70, plain, (![A_94, B_95, C_96, D_97]: (m1_subset_1(k3_funct_2(A_94, B_95, C_96, D_97), B_95) | ~m1_subset_1(D_97, A_94) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~v1_funct_2(C_96, A_94, B_95) | ~v1_funct_1(C_96) | v1_xboole_0(A_94))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.67/1.32  tff(c_72, plain, (![D_97]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_97), '#skF_1') | ~m1_subset_1(D_97, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_70])).
% 2.67/1.32  tff(c_77, plain, (![D_97]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_97), '#skF_1') | ~m1_subset_1(D_97, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_72])).
% 2.67/1.32  tff(c_78, plain, (![D_97]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_97), '#skF_1') | ~m1_subset_1(D_97, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_77])).
% 2.67/1.32  tff(c_118, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_113, c_78])).
% 2.67/1.32  tff(c_122, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_118])).
% 2.67/1.32  tff(c_10, plain, (![A_15, B_16, C_17, D_18]: (k3_funct_2(A_15, B_16, C_17, D_18)=k1_funct_1(C_17, D_18) | ~m1_subset_1(D_18, A_15) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))) | ~v1_funct_2(C_17, A_15, B_16) | ~v1_funct_1(C_17) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.67/1.32  tff(c_125, plain, (![B_16, C_17]: (k3_funct_2('#skF_1', B_16, C_17, k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1(C_17, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_16))) | ~v1_funct_2(C_17, '#skF_1', B_16) | ~v1_funct_1(C_17) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_122, c_10])).
% 2.67/1.32  tff(c_129, plain, (![B_106, C_107]: (k3_funct_2('#skF_1', B_106, C_107, k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1(C_107, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_106))) | ~v1_funct_2(C_107, '#skF_1', B_106) | ~v1_funct_1(C_107))), inference(negUnitSimplification, [status(thm)], [c_38, c_125])).
% 2.67/1.32  tff(c_132, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_129])).
% 2.67/1.32  tff(c_135, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_69, c_132])).
% 2.67/1.32  tff(c_145, plain, (![A_108, B_109, C_110, D_111]: (k3_funct_2(A_108, B_109, C_110, D_111)=k7_partfun1(B_109, C_110, D_111) | ~m1_subset_1(D_111, A_108) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~v1_funct_2(C_110, A_108, B_109) | ~v1_funct_1(C_110) | v1_xboole_0(B_109) | v1_xboole_0(A_108))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.67/1.32  tff(c_147, plain, (![B_109, C_110]: (k3_funct_2('#skF_1', B_109, C_110, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_109, C_110, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_109))) | ~v1_funct_2(C_110, '#skF_1', B_109) | ~v1_funct_1(C_110) | v1_xboole_0(B_109) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_122, c_145])).
% 2.67/1.32  tff(c_194, plain, (![B_114, C_115]: (k3_funct_2('#skF_1', B_114, C_115, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_114, C_115, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_114))) | ~v1_funct_2(C_115, '#skF_1', B_114) | ~v1_funct_1(C_115) | v1_xboole_0(B_114))), inference(negUnitSimplification, [status(thm)], [c_38, c_147])).
% 2.67/1.32  tff(c_197, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_26, c_194])).
% 2.67/1.32  tff(c_200, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_69, c_135, c_197])).
% 2.67/1.32  tff(c_201, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_56, c_200])).
% 2.67/1.32  tff(c_20, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.67/1.32  tff(c_114, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_20])).
% 2.67/1.32  tff(c_202, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_114])).
% 2.67/1.32  tff(c_275, plain, (k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_269, c_202])).
% 2.67/1.32  tff(c_282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_113, c_275])).
% 2.67/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.32  
% 2.67/1.32  Inference rules
% 2.67/1.32  ----------------------
% 2.67/1.32  #Ref     : 1
% 2.67/1.32  #Sup     : 48
% 2.67/1.32  #Fact    : 0
% 2.67/1.32  #Define  : 0
% 2.67/1.32  #Split   : 0
% 2.67/1.32  #Chain   : 0
% 2.67/1.32  #Close   : 0
% 2.67/1.32  
% 2.67/1.32  Ordering : KBO
% 2.67/1.32  
% 2.67/1.32  Simplification rules
% 2.67/1.32  ----------------------
% 2.67/1.32  #Subsume      : 1
% 2.67/1.32  #Demod        : 39
% 2.67/1.32  #Tautology    : 17
% 2.67/1.32  #SimpNegUnit  : 21
% 2.67/1.32  #BackRed      : 2
% 2.67/1.32  
% 2.67/1.32  #Partial instantiations: 0
% 2.67/1.32  #Strategies tried      : 1
% 2.67/1.32  
% 2.67/1.32  Timing (in seconds)
% 2.67/1.32  ----------------------
% 2.67/1.33  Preprocessing        : 0.34
% 2.67/1.33  Parsing              : 0.18
% 2.67/1.33  CNF conversion       : 0.03
% 2.67/1.33  Main loop            : 0.24
% 2.67/1.33  Inferencing          : 0.09
% 2.67/1.33  Reduction            : 0.07
% 2.67/1.33  Demodulation         : 0.05
% 2.67/1.33  BG Simplification    : 0.02
% 2.67/1.33  Subsumption          : 0.05
% 2.67/1.33  Abstraction          : 0.02
% 2.67/1.33  MUC search           : 0.00
% 2.67/1.33  Cooper               : 0.00
% 2.67/1.33  Total                : 0.62
% 2.67/1.33  Index Insertion      : 0.00
% 2.67/1.33  Index Deletion       : 0.00
% 2.67/1.33  Index Matching       : 0.00
% 2.67/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
