%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:14 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 112 expanded)
%              Number of leaves         :   33 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  163 ( 393 expanded)
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

tff(f_133,negated_conjecture,(
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

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_106,axiom,(
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

tff(c_30,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_38,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_178,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( m1_subset_1(k3_funct_2(A_116,B_117,C_118,D_119),B_117)
      | ~ m1_subset_1(D_119,A_116)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_2(C_118,A_116,B_117)
      | ~ v1_funct_1(C_118)
      | v1_xboole_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_183,plain,(
    ! [D_119] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_119),'#skF_1')
      | ~ m1_subset_1(D_119,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_178])).

tff(c_189,plain,(
    ! [D_119] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_119),'#skF_1')
      | ~ m1_subset_1(D_119,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_183])).

tff(c_195,plain,(
    ! [D_120] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_120),'#skF_1')
      | ~ m1_subset_1(D_120,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_189])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_99,plain,(
    ! [C_97,B_98,A_99] :
      ( v5_relat_1(C_97,B_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_99,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_112,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_99])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_65,plain,(
    ! [C_87,A_88,B_89] :
      ( v1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_78,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_65])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_28,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_85,plain,(
    ! [C_94,A_95,B_96] :
      ( v4_relat_1(C_94,A_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_98,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_85])).

tff(c_115,plain,(
    ! [B_101,A_102] :
      ( k1_relat_1(B_101) = A_102
      | ~ v1_partfun1(B_101,A_102)
      | ~ v4_relat_1(B_101,A_102)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_118,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_98,c_115])).

tff(c_124,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_28,c_118])).

tff(c_139,plain,(
    ! [A_105,B_106,C_107] :
      ( k7_partfun1(A_105,B_106,C_107) = k1_funct_1(B_106,C_107)
      | ~ r2_hidden(C_107,k1_relat_1(B_106))
      | ~ v1_funct_1(B_106)
      | ~ v5_relat_1(B_106,A_105)
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_141,plain,(
    ! [A_105,C_107] :
      ( k7_partfun1(A_105,'#skF_5',C_107) = k1_funct_1('#skF_5',C_107)
      | ~ r2_hidden(C_107,'#skF_1')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_105)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_139])).

tff(c_148,plain,(
    ! [A_108,C_109] :
      ( k7_partfun1(A_108,'#skF_5',C_109) = k1_funct_1('#skF_5',C_109)
      | ~ r2_hidden(C_109,'#skF_1')
      | ~ v5_relat_1('#skF_5',A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_34,c_141])).

tff(c_151,plain,(
    ! [A_108,B_2] :
      ( k7_partfun1(A_108,'#skF_5',B_2) = k1_funct_1('#skF_5',B_2)
      | ~ v5_relat_1('#skF_5',A_108)
      | ~ m1_subset_1(B_2,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_4,c_148])).

tff(c_155,plain,(
    ! [A_110,B_111] :
      ( k7_partfun1(A_110,'#skF_5',B_111) = k1_funct_1('#skF_5',B_111)
      | ~ v5_relat_1('#skF_5',A_110)
      | ~ m1_subset_1(B_111,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_151])).

tff(c_158,plain,(
    ! [B_111] :
      ( k7_partfun1('#skF_3','#skF_5',B_111) = k1_funct_1('#skF_5',B_111)
      | ~ m1_subset_1(B_111,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_112,c_155])).

tff(c_202,plain,(
    ! [D_120] :
      ( k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',D_120)) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',D_120))
      | ~ m1_subset_1(D_120,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_195,c_158])).

tff(c_204,plain,(
    ! [E_121,B_126,D_123,F_122,A_125,C_124] :
      ( k3_funct_2(B_126,C_124,k8_funct_2(B_126,A_125,C_124,D_123,E_121),F_122) = k1_funct_1(E_121,k3_funct_2(B_126,A_125,D_123,F_122))
      | ~ v1_partfun1(E_121,A_125)
      | ~ m1_subset_1(F_122,B_126)
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_125,C_124)))
      | ~ v1_funct_1(E_121)
      | ~ m1_subset_1(D_123,k1_zfmisc_1(k2_zfmisc_1(B_126,A_125)))
      | ~ v1_funct_2(D_123,B_126,A_125)
      | ~ v1_funct_1(D_123)
      | v1_xboole_0(B_126)
      | v1_xboole_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_211,plain,(
    ! [B_126,D_123,F_122] :
      ( k3_funct_2(B_126,'#skF_3',k8_funct_2(B_126,'#skF_1','#skF_3',D_123,'#skF_5'),F_122) = k1_funct_1('#skF_5',k3_funct_2(B_126,'#skF_1',D_123,F_122))
      | ~ v1_partfun1('#skF_5','#skF_1')
      | ~ m1_subset_1(F_122,B_126)
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_123,k1_zfmisc_1(k2_zfmisc_1(B_126,'#skF_1')))
      | ~ v1_funct_2(D_123,B_126,'#skF_1')
      | ~ v1_funct_1(D_123)
      | v1_xboole_0(B_126)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_204])).

tff(c_219,plain,(
    ! [B_126,D_123,F_122] :
      ( k3_funct_2(B_126,'#skF_3',k8_funct_2(B_126,'#skF_1','#skF_3',D_123,'#skF_5'),F_122) = k1_funct_1('#skF_5',k3_funct_2(B_126,'#skF_1',D_123,F_122))
      | ~ m1_subset_1(F_122,B_126)
      | ~ m1_subset_1(D_123,k1_zfmisc_1(k2_zfmisc_1(B_126,'#skF_1')))
      | ~ v1_funct_2(D_123,B_126,'#skF_1')
      | ~ v1_funct_1(D_123)
      | v1_xboole_0(B_126)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_211])).

tff(c_231,plain,(
    ! [B_128,D_129,F_130] :
      ( k3_funct_2(B_128,'#skF_3',k8_funct_2(B_128,'#skF_1','#skF_3',D_129,'#skF_5'),F_130) = k1_funct_1('#skF_5',k3_funct_2(B_128,'#skF_1',D_129,F_130))
      | ~ m1_subset_1(F_130,B_128)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1(B_128,'#skF_1')))
      | ~ v1_funct_2(D_129,B_128,'#skF_1')
      | ~ v1_funct_1(D_129)
      | v1_xboole_0(B_128) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_219])).

tff(c_236,plain,(
    ! [F_130] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_130) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_130))
      | ~ m1_subset_1(F_130,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_231])).

tff(c_240,plain,(
    ! [F_130] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_130) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_130))
      | ~ m1_subset_1(F_130,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_236])).

tff(c_242,plain,(
    ! [F_131] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_131) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_131))
      | ~ m1_subset_1(F_131,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_240])).

tff(c_26,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_248,plain,
    ( k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_26])).

tff(c_254,plain,(
    k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_248])).

tff(c_258,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_254])).

tff(c_262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.40  
% 2.59/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.40  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.59/1.40  
% 2.59/1.40  %Foreground sorts:
% 2.59/1.40  
% 2.59/1.40  
% 2.59/1.40  %Background operators:
% 2.59/1.40  
% 2.59/1.40  
% 2.59/1.40  %Foreground operators:
% 2.59/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.40  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.59/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.59/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.59/1.40  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.59/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.59/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.40  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.59/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.59/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.59/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.59/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.59/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.59/1.40  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.59/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.59/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.40  
% 2.59/1.42  tff(f_133, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_funct_2)).
% 2.59/1.42  tff(f_80, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 2.59/1.42  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.59/1.42  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.59/1.42  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.59/1.42  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.59/1.42  tff(f_67, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 2.59/1.42  tff(f_106, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_funct_2)).
% 2.59/1.42  tff(c_30, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.59/1.42  tff(c_42, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.59/1.42  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.59/1.42  tff(c_38, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.59/1.42  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.59/1.42  tff(c_178, plain, (![A_116, B_117, C_118, D_119]: (m1_subset_1(k3_funct_2(A_116, B_117, C_118, D_119), B_117) | ~m1_subset_1(D_119, A_116) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_2(C_118, A_116, B_117) | ~v1_funct_1(C_118) | v1_xboole_0(A_116))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.59/1.42  tff(c_183, plain, (![D_119]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_119), '#skF_1') | ~m1_subset_1(D_119, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_178])).
% 2.59/1.42  tff(c_189, plain, (![D_119]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_119), '#skF_1') | ~m1_subset_1(D_119, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_183])).
% 2.59/1.42  tff(c_195, plain, (![D_120]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_120), '#skF_1') | ~m1_subset_1(D_120, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_189])).
% 2.59/1.42  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.59/1.42  tff(c_99, plain, (![C_97, B_98, A_99]: (v5_relat_1(C_97, B_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.59/1.42  tff(c_112, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_99])).
% 2.59/1.42  tff(c_44, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.59/1.42  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.59/1.42  tff(c_65, plain, (![C_87, A_88, B_89]: (v1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.59/1.42  tff(c_78, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_65])).
% 2.59/1.42  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.59/1.42  tff(c_28, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.59/1.42  tff(c_85, plain, (![C_94, A_95, B_96]: (v4_relat_1(C_94, A_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.59/1.42  tff(c_98, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_85])).
% 2.59/1.42  tff(c_115, plain, (![B_101, A_102]: (k1_relat_1(B_101)=A_102 | ~v1_partfun1(B_101, A_102) | ~v4_relat_1(B_101, A_102) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.59/1.42  tff(c_118, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_98, c_115])).
% 2.59/1.42  tff(c_124, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_28, c_118])).
% 2.59/1.42  tff(c_139, plain, (![A_105, B_106, C_107]: (k7_partfun1(A_105, B_106, C_107)=k1_funct_1(B_106, C_107) | ~r2_hidden(C_107, k1_relat_1(B_106)) | ~v1_funct_1(B_106) | ~v5_relat_1(B_106, A_105) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.59/1.42  tff(c_141, plain, (![A_105, C_107]: (k7_partfun1(A_105, '#skF_5', C_107)=k1_funct_1('#skF_5', C_107) | ~r2_hidden(C_107, '#skF_1') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_105) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_139])).
% 2.59/1.42  tff(c_148, plain, (![A_108, C_109]: (k7_partfun1(A_108, '#skF_5', C_109)=k1_funct_1('#skF_5', C_109) | ~r2_hidden(C_109, '#skF_1') | ~v5_relat_1('#skF_5', A_108))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_34, c_141])).
% 2.59/1.42  tff(c_151, plain, (![A_108, B_2]: (k7_partfun1(A_108, '#skF_5', B_2)=k1_funct_1('#skF_5', B_2) | ~v5_relat_1('#skF_5', A_108) | ~m1_subset_1(B_2, '#skF_1') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_4, c_148])).
% 2.59/1.42  tff(c_155, plain, (![A_110, B_111]: (k7_partfun1(A_110, '#skF_5', B_111)=k1_funct_1('#skF_5', B_111) | ~v5_relat_1('#skF_5', A_110) | ~m1_subset_1(B_111, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_151])).
% 2.59/1.42  tff(c_158, plain, (![B_111]: (k7_partfun1('#skF_3', '#skF_5', B_111)=k1_funct_1('#skF_5', B_111) | ~m1_subset_1(B_111, '#skF_1'))), inference(resolution, [status(thm)], [c_112, c_155])).
% 2.59/1.42  tff(c_202, plain, (![D_120]: (k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_120))=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_120)) | ~m1_subset_1(D_120, '#skF_2'))), inference(resolution, [status(thm)], [c_195, c_158])).
% 2.59/1.42  tff(c_204, plain, (![E_121, B_126, D_123, F_122, A_125, C_124]: (k3_funct_2(B_126, C_124, k8_funct_2(B_126, A_125, C_124, D_123, E_121), F_122)=k1_funct_1(E_121, k3_funct_2(B_126, A_125, D_123, F_122)) | ~v1_partfun1(E_121, A_125) | ~m1_subset_1(F_122, B_126) | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_125, C_124))) | ~v1_funct_1(E_121) | ~m1_subset_1(D_123, k1_zfmisc_1(k2_zfmisc_1(B_126, A_125))) | ~v1_funct_2(D_123, B_126, A_125) | ~v1_funct_1(D_123) | v1_xboole_0(B_126) | v1_xboole_0(A_125))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.59/1.42  tff(c_211, plain, (![B_126, D_123, F_122]: (k3_funct_2(B_126, '#skF_3', k8_funct_2(B_126, '#skF_1', '#skF_3', D_123, '#skF_5'), F_122)=k1_funct_1('#skF_5', k3_funct_2(B_126, '#skF_1', D_123, F_122)) | ~v1_partfun1('#skF_5', '#skF_1') | ~m1_subset_1(F_122, B_126) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_123, k1_zfmisc_1(k2_zfmisc_1(B_126, '#skF_1'))) | ~v1_funct_2(D_123, B_126, '#skF_1') | ~v1_funct_1(D_123) | v1_xboole_0(B_126) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_204])).
% 2.59/1.42  tff(c_219, plain, (![B_126, D_123, F_122]: (k3_funct_2(B_126, '#skF_3', k8_funct_2(B_126, '#skF_1', '#skF_3', D_123, '#skF_5'), F_122)=k1_funct_1('#skF_5', k3_funct_2(B_126, '#skF_1', D_123, F_122)) | ~m1_subset_1(F_122, B_126) | ~m1_subset_1(D_123, k1_zfmisc_1(k2_zfmisc_1(B_126, '#skF_1'))) | ~v1_funct_2(D_123, B_126, '#skF_1') | ~v1_funct_1(D_123) | v1_xboole_0(B_126) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_211])).
% 2.59/1.42  tff(c_231, plain, (![B_128, D_129, F_130]: (k3_funct_2(B_128, '#skF_3', k8_funct_2(B_128, '#skF_1', '#skF_3', D_129, '#skF_5'), F_130)=k1_funct_1('#skF_5', k3_funct_2(B_128, '#skF_1', D_129, F_130)) | ~m1_subset_1(F_130, B_128) | ~m1_subset_1(D_129, k1_zfmisc_1(k2_zfmisc_1(B_128, '#skF_1'))) | ~v1_funct_2(D_129, B_128, '#skF_1') | ~v1_funct_1(D_129) | v1_xboole_0(B_128))), inference(negUnitSimplification, [status(thm)], [c_44, c_219])).
% 2.59/1.42  tff(c_236, plain, (![F_130]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_130)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_130)) | ~m1_subset_1(F_130, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_231])).
% 2.59/1.42  tff(c_240, plain, (![F_130]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_130)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_130)) | ~m1_subset_1(F_130, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_236])).
% 2.59/1.42  tff(c_242, plain, (![F_131]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_131)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_131)) | ~m1_subset_1(F_131, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_240])).
% 2.59/1.42  tff(c_26, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.59/1.42  tff(c_248, plain, (k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_242, c_26])).
% 2.59/1.42  tff(c_254, plain, (k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_248])).
% 2.59/1.42  tff(c_258, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_202, c_254])).
% 2.59/1.42  tff(c_262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_258])).
% 2.59/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.42  
% 2.59/1.42  Inference rules
% 2.59/1.42  ----------------------
% 2.59/1.42  #Ref     : 0
% 2.59/1.42  #Sup     : 42
% 2.59/1.42  #Fact    : 0
% 2.59/1.42  #Define  : 0
% 2.59/1.42  #Split   : 6
% 2.59/1.42  #Chain   : 0
% 2.59/1.42  #Close   : 0
% 2.59/1.42  
% 2.59/1.42  Ordering : KBO
% 2.59/1.42  
% 2.59/1.42  Simplification rules
% 2.59/1.42  ----------------------
% 2.59/1.42  #Subsume      : 12
% 2.59/1.42  #Demod        : 25
% 2.59/1.42  #Tautology    : 9
% 2.59/1.42  #SimpNegUnit  : 7
% 2.59/1.42  #BackRed      : 0
% 2.59/1.42  
% 2.59/1.42  #Partial instantiations: 0
% 2.59/1.42  #Strategies tried      : 1
% 2.59/1.42  
% 2.59/1.42  Timing (in seconds)
% 2.59/1.42  ----------------------
% 2.59/1.42  Preprocessing        : 0.36
% 2.59/1.42  Parsing              : 0.19
% 2.59/1.42  CNF conversion       : 0.03
% 2.59/1.42  Main loop            : 0.23
% 2.59/1.42  Inferencing          : 0.08
% 2.59/1.42  Reduction            : 0.07
% 2.59/1.42  Demodulation         : 0.05
% 2.59/1.42  BG Simplification    : 0.02
% 2.59/1.42  Subsumption          : 0.04
% 2.59/1.42  Abstraction          : 0.01
% 2.59/1.42  MUC search           : 0.00
% 2.59/1.42  Cooper               : 0.00
% 2.59/1.42  Total                : 0.63
% 2.59/1.42  Index Insertion      : 0.00
% 2.59/1.42  Index Deletion       : 0.00
% 2.59/1.42  Index Matching       : 0.00
% 2.59/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
