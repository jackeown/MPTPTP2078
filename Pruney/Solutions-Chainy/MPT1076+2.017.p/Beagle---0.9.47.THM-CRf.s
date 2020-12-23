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
% DateTime   : Thu Dec  3 10:18:14 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 112 expanded)
%              Number of leaves         :   33 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  160 ( 390 expanded)
%              Number of equality atoms :   24 (  45 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
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

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_99,axiom,(
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

tff(c_24,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_32,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_112,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( m1_subset_1(k3_funct_2(A_105,B_106,C_107,D_108),B_106)
      | ~ m1_subset_1(D_108,A_105)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ v1_funct_2(C_107,A_105,B_106)
      | ~ v1_funct_1(C_107)
      | v1_xboole_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_114,plain,(
    ! [D_108] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_108),'#skF_1')
      | ~ m1_subset_1(D_108,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_112])).

tff(c_119,plain,(
    ! [D_108] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_108),'#skF_1')
      | ~ m1_subset_1(D_108,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_114])).

tff(c_125,plain,(
    ! [D_109] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_109),'#skF_1')
      | ~ m1_subset_1(D_109,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_119])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_58,plain,(
    ! [C_91,B_92,A_93] :
      ( v5_relat_1(C_91,B_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_66,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_58])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_39,plain,(
    ! [C_83,A_84,B_85] :
      ( v1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_47,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_39])).

tff(c_28,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_22,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_49,plain,(
    ! [C_88,A_89,B_90] :
      ( v4_relat_1(C_88,A_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_57,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_49])).

tff(c_68,plain,(
    ! [B_95,A_96] :
      ( k1_relat_1(B_95) = A_96
      | ~ v1_partfun1(B_95,A_96)
      | ~ v4_relat_1(B_95,A_96)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_71,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_57,c_68])).

tff(c_77,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_22,c_71])).

tff(c_91,plain,(
    ! [A_97,B_98,C_99] :
      ( k7_partfun1(A_97,B_98,C_99) = k1_funct_1(B_98,C_99)
      | ~ r2_hidden(C_99,k1_relat_1(B_98))
      | ~ v1_funct_1(B_98)
      | ~ v5_relat_1(B_98,A_97)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_93,plain,(
    ! [A_97,C_99] :
      ( k7_partfun1(A_97,'#skF_5',C_99) = k1_funct_1('#skF_5',C_99)
      | ~ r2_hidden(C_99,'#skF_1')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_97)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_91])).

tff(c_100,plain,(
    ! [A_100,C_101] :
      ( k7_partfun1(A_100,'#skF_5',C_101) = k1_funct_1('#skF_5',C_101)
      | ~ r2_hidden(C_101,'#skF_1')
      | ~ v5_relat_1('#skF_5',A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_28,c_93])).

tff(c_103,plain,(
    ! [A_100,A_1] :
      ( k7_partfun1(A_100,'#skF_5',A_1) = k1_funct_1('#skF_5',A_1)
      | ~ v5_relat_1('#skF_5',A_100)
      | v1_xboole_0('#skF_1')
      | ~ m1_subset_1(A_1,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2,c_100])).

tff(c_107,plain,(
    ! [A_102,A_103] :
      ( k7_partfun1(A_102,'#skF_5',A_103) = k1_funct_1('#skF_5',A_103)
      | ~ v5_relat_1('#skF_5',A_102)
      | ~ m1_subset_1(A_103,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_103])).

tff(c_110,plain,(
    ! [A_103] :
      ( k7_partfun1('#skF_3','#skF_5',A_103) = k1_funct_1('#skF_5',A_103)
      | ~ m1_subset_1(A_103,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_107])).

tff(c_129,plain,(
    ! [D_109] :
      ( k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',D_109)) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',D_109))
      | ~ m1_subset_1(D_109,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_125,c_110])).

tff(c_152,plain,(
    ! [D_116,B_119,F_115,A_118,C_117,E_114] :
      ( k3_funct_2(B_119,C_117,k8_funct_2(B_119,A_118,C_117,D_116,E_114),F_115) = k1_funct_1(E_114,k3_funct_2(B_119,A_118,D_116,F_115))
      | ~ v1_partfun1(E_114,A_118)
      | ~ m1_subset_1(F_115,B_119)
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_118,C_117)))
      | ~ v1_funct_1(E_114)
      | ~ m1_subset_1(D_116,k1_zfmisc_1(k2_zfmisc_1(B_119,A_118)))
      | ~ v1_funct_2(D_116,B_119,A_118)
      | ~ v1_funct_1(D_116)
      | v1_xboole_0(B_119)
      | v1_xboole_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_156,plain,(
    ! [B_119,D_116,F_115] :
      ( k3_funct_2(B_119,'#skF_3',k8_funct_2(B_119,'#skF_1','#skF_3',D_116,'#skF_5'),F_115) = k1_funct_1('#skF_5',k3_funct_2(B_119,'#skF_1',D_116,F_115))
      | ~ v1_partfun1('#skF_5','#skF_1')
      | ~ m1_subset_1(F_115,B_119)
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_116,k1_zfmisc_1(k2_zfmisc_1(B_119,'#skF_1')))
      | ~ v1_funct_2(D_116,B_119,'#skF_1')
      | ~ v1_funct_1(D_116)
      | v1_xboole_0(B_119)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_152])).

tff(c_163,plain,(
    ! [B_119,D_116,F_115] :
      ( k3_funct_2(B_119,'#skF_3',k8_funct_2(B_119,'#skF_1','#skF_3',D_116,'#skF_5'),F_115) = k1_funct_1('#skF_5',k3_funct_2(B_119,'#skF_1',D_116,F_115))
      | ~ m1_subset_1(F_115,B_119)
      | ~ m1_subset_1(D_116,k1_zfmisc_1(k2_zfmisc_1(B_119,'#skF_1')))
      | ~ v1_funct_2(D_116,B_119,'#skF_1')
      | ~ v1_funct_1(D_116)
      | v1_xboole_0(B_119)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_156])).

tff(c_166,plain,(
    ! [B_120,D_121,F_122] :
      ( k3_funct_2(B_120,'#skF_3',k8_funct_2(B_120,'#skF_1','#skF_3',D_121,'#skF_5'),F_122) = k1_funct_1('#skF_5',k3_funct_2(B_120,'#skF_1',D_121,F_122))
      | ~ m1_subset_1(F_122,B_120)
      | ~ m1_subset_1(D_121,k1_zfmisc_1(k2_zfmisc_1(B_120,'#skF_1')))
      | ~ v1_funct_2(D_121,B_120,'#skF_1')
      | ~ v1_funct_1(D_121)
      | v1_xboole_0(B_120) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_163])).

tff(c_168,plain,(
    ! [F_122] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_122) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_122))
      | ~ m1_subset_1(F_122,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_166])).

tff(c_171,plain,(
    ! [F_122] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_122) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_122))
      | ~ m1_subset_1(F_122,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_168])).

tff(c_173,plain,(
    ! [F_123] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_123) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_123))
      | ~ m1_subset_1(F_123,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_171])).

tff(c_20,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_179,plain,
    ( k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_20])).

tff(c_185,plain,(
    k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_179])).

tff(c_189,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_185])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:45:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.32  
% 2.38/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.33  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.38/1.33  
% 2.38/1.33  %Foreground sorts:
% 2.38/1.33  
% 2.38/1.33  
% 2.38/1.33  %Background operators:
% 2.38/1.33  
% 2.38/1.33  
% 2.38/1.33  %Foreground operators:
% 2.38/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.33  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.38/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.38/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.38/1.33  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.38/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.38/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.38/1.33  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.38/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.38/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.38/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.38/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.38/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.38/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.38/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.38/1.33  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.38/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.38/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.33  
% 2.38/1.34  tff(f_126, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_funct_2)).
% 2.38/1.34  tff(f_73, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 2.38/1.34  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.38/1.34  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.38/1.34  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.38/1.34  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.38/1.34  tff(f_60, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 2.38/1.34  tff(f_99, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_funct_2)).
% 2.38/1.34  tff(c_24, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.38/1.34  tff(c_36, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.38/1.34  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.38/1.34  tff(c_32, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.38/1.34  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.38/1.34  tff(c_112, plain, (![A_105, B_106, C_107, D_108]: (m1_subset_1(k3_funct_2(A_105, B_106, C_107, D_108), B_106) | ~m1_subset_1(D_108, A_105) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))) | ~v1_funct_2(C_107, A_105, B_106) | ~v1_funct_1(C_107) | v1_xboole_0(A_105))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.38/1.34  tff(c_114, plain, (![D_108]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_108), '#skF_1') | ~m1_subset_1(D_108, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_112])).
% 2.38/1.34  tff(c_119, plain, (![D_108]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_108), '#skF_1') | ~m1_subset_1(D_108, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_114])).
% 2.38/1.34  tff(c_125, plain, (![D_109]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_109), '#skF_1') | ~m1_subset_1(D_109, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_119])).
% 2.38/1.34  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.38/1.34  tff(c_58, plain, (![C_91, B_92, A_93]: (v5_relat_1(C_91, B_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.38/1.34  tff(c_66, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_58])).
% 2.38/1.34  tff(c_38, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.38/1.34  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.38/1.34  tff(c_39, plain, (![C_83, A_84, B_85]: (v1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.38/1.34  tff(c_47, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_39])).
% 2.38/1.34  tff(c_28, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.38/1.34  tff(c_22, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.38/1.34  tff(c_49, plain, (![C_88, A_89, B_90]: (v4_relat_1(C_88, A_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.38/1.34  tff(c_57, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_49])).
% 2.38/1.34  tff(c_68, plain, (![B_95, A_96]: (k1_relat_1(B_95)=A_96 | ~v1_partfun1(B_95, A_96) | ~v4_relat_1(B_95, A_96) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.38/1.34  tff(c_71, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_57, c_68])).
% 2.38/1.34  tff(c_77, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_47, c_22, c_71])).
% 2.38/1.34  tff(c_91, plain, (![A_97, B_98, C_99]: (k7_partfun1(A_97, B_98, C_99)=k1_funct_1(B_98, C_99) | ~r2_hidden(C_99, k1_relat_1(B_98)) | ~v1_funct_1(B_98) | ~v5_relat_1(B_98, A_97) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.38/1.34  tff(c_93, plain, (![A_97, C_99]: (k7_partfun1(A_97, '#skF_5', C_99)=k1_funct_1('#skF_5', C_99) | ~r2_hidden(C_99, '#skF_1') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_97) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_91])).
% 2.38/1.34  tff(c_100, plain, (![A_100, C_101]: (k7_partfun1(A_100, '#skF_5', C_101)=k1_funct_1('#skF_5', C_101) | ~r2_hidden(C_101, '#skF_1') | ~v5_relat_1('#skF_5', A_100))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_28, c_93])).
% 2.38/1.34  tff(c_103, plain, (![A_100, A_1]: (k7_partfun1(A_100, '#skF_5', A_1)=k1_funct_1('#skF_5', A_1) | ~v5_relat_1('#skF_5', A_100) | v1_xboole_0('#skF_1') | ~m1_subset_1(A_1, '#skF_1'))), inference(resolution, [status(thm)], [c_2, c_100])).
% 2.38/1.34  tff(c_107, plain, (![A_102, A_103]: (k7_partfun1(A_102, '#skF_5', A_103)=k1_funct_1('#skF_5', A_103) | ~v5_relat_1('#skF_5', A_102) | ~m1_subset_1(A_103, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_38, c_103])).
% 2.38/1.34  tff(c_110, plain, (![A_103]: (k7_partfun1('#skF_3', '#skF_5', A_103)=k1_funct_1('#skF_5', A_103) | ~m1_subset_1(A_103, '#skF_1'))), inference(resolution, [status(thm)], [c_66, c_107])).
% 2.38/1.34  tff(c_129, plain, (![D_109]: (k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_109))=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_109)) | ~m1_subset_1(D_109, '#skF_2'))), inference(resolution, [status(thm)], [c_125, c_110])).
% 2.38/1.34  tff(c_152, plain, (![D_116, B_119, F_115, A_118, C_117, E_114]: (k3_funct_2(B_119, C_117, k8_funct_2(B_119, A_118, C_117, D_116, E_114), F_115)=k1_funct_1(E_114, k3_funct_2(B_119, A_118, D_116, F_115)) | ~v1_partfun1(E_114, A_118) | ~m1_subset_1(F_115, B_119) | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_118, C_117))) | ~v1_funct_1(E_114) | ~m1_subset_1(D_116, k1_zfmisc_1(k2_zfmisc_1(B_119, A_118))) | ~v1_funct_2(D_116, B_119, A_118) | ~v1_funct_1(D_116) | v1_xboole_0(B_119) | v1_xboole_0(A_118))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.38/1.34  tff(c_156, plain, (![B_119, D_116, F_115]: (k3_funct_2(B_119, '#skF_3', k8_funct_2(B_119, '#skF_1', '#skF_3', D_116, '#skF_5'), F_115)=k1_funct_1('#skF_5', k3_funct_2(B_119, '#skF_1', D_116, F_115)) | ~v1_partfun1('#skF_5', '#skF_1') | ~m1_subset_1(F_115, B_119) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_116, k1_zfmisc_1(k2_zfmisc_1(B_119, '#skF_1'))) | ~v1_funct_2(D_116, B_119, '#skF_1') | ~v1_funct_1(D_116) | v1_xboole_0(B_119) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_152])).
% 2.38/1.34  tff(c_163, plain, (![B_119, D_116, F_115]: (k3_funct_2(B_119, '#skF_3', k8_funct_2(B_119, '#skF_1', '#skF_3', D_116, '#skF_5'), F_115)=k1_funct_1('#skF_5', k3_funct_2(B_119, '#skF_1', D_116, F_115)) | ~m1_subset_1(F_115, B_119) | ~m1_subset_1(D_116, k1_zfmisc_1(k2_zfmisc_1(B_119, '#skF_1'))) | ~v1_funct_2(D_116, B_119, '#skF_1') | ~v1_funct_1(D_116) | v1_xboole_0(B_119) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_156])).
% 2.38/1.34  tff(c_166, plain, (![B_120, D_121, F_122]: (k3_funct_2(B_120, '#skF_3', k8_funct_2(B_120, '#skF_1', '#skF_3', D_121, '#skF_5'), F_122)=k1_funct_1('#skF_5', k3_funct_2(B_120, '#skF_1', D_121, F_122)) | ~m1_subset_1(F_122, B_120) | ~m1_subset_1(D_121, k1_zfmisc_1(k2_zfmisc_1(B_120, '#skF_1'))) | ~v1_funct_2(D_121, B_120, '#skF_1') | ~v1_funct_1(D_121) | v1_xboole_0(B_120))), inference(negUnitSimplification, [status(thm)], [c_38, c_163])).
% 2.38/1.34  tff(c_168, plain, (![F_122]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_122)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_122)) | ~m1_subset_1(F_122, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_166])).
% 2.38/1.34  tff(c_171, plain, (![F_122]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_122)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_122)) | ~m1_subset_1(F_122, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_168])).
% 2.38/1.34  tff(c_173, plain, (![F_123]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_123)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_123)) | ~m1_subset_1(F_123, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_171])).
% 2.38/1.34  tff(c_20, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.38/1.34  tff(c_179, plain, (k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_173, c_20])).
% 2.38/1.34  tff(c_185, plain, (k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_179])).
% 2.38/1.34  tff(c_189, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_129, c_185])).
% 2.38/1.34  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_189])).
% 2.38/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.34  
% 2.38/1.34  Inference rules
% 2.38/1.34  ----------------------
% 2.38/1.34  #Ref     : 0
% 2.38/1.34  #Sup     : 29
% 2.38/1.34  #Fact    : 0
% 2.38/1.34  #Define  : 0
% 2.38/1.34  #Split   : 3
% 2.38/1.34  #Chain   : 0
% 2.38/1.34  #Close   : 0
% 2.38/1.34  
% 2.38/1.34  Ordering : KBO
% 2.38/1.34  
% 2.38/1.34  Simplification rules
% 2.38/1.34  ----------------------
% 2.38/1.34  #Subsume      : 2
% 2.38/1.34  #Demod        : 25
% 2.38/1.34  #Tautology    : 7
% 2.38/1.34  #SimpNegUnit  : 7
% 2.38/1.34  #BackRed      : 0
% 2.38/1.34  
% 2.38/1.34  #Partial instantiations: 0
% 2.38/1.34  #Strategies tried      : 1
% 2.38/1.34  
% 2.38/1.34  Timing (in seconds)
% 2.38/1.34  ----------------------
% 2.38/1.35  Preprocessing        : 0.35
% 2.38/1.35  Parsing              : 0.19
% 2.38/1.35  CNF conversion       : 0.03
% 2.38/1.35  Main loop            : 0.18
% 2.38/1.35  Inferencing          : 0.07
% 2.38/1.35  Reduction            : 0.06
% 2.38/1.35  Demodulation         : 0.04
% 2.38/1.35  BG Simplification    : 0.01
% 2.38/1.35  Subsumption          : 0.02
% 2.38/1.35  Abstraction          : 0.01
% 2.38/1.35  MUC search           : 0.00
% 2.38/1.35  Cooper               : 0.00
% 2.38/1.35  Total                : 0.57
% 2.38/1.35  Index Insertion      : 0.00
% 2.38/1.35  Index Deletion       : 0.00
% 2.38/1.35  Index Matching       : 0.00
% 2.38/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
