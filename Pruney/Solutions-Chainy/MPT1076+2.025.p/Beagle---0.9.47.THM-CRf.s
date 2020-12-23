%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:15 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 118 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  166 ( 402 expanded)
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

tff(f_131,negated_conjecture,(
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

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_46,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_104,axiom,(
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

tff(c_26,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_34,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_132,plain,(
    ! [A_111,B_112,C_113,D_114] :
      ( m1_subset_1(k3_funct_2(A_111,B_112,C_113,D_114),B_112)
      | ~ m1_subset_1(D_114,A_111)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ v1_funct_2(C_113,A_111,B_112)
      | ~ v1_funct_1(C_113)
      | v1_xboole_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_136,plain,(
    ! [D_114] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_114),'#skF_1')
      | ~ m1_subset_1(D_114,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_132])).

tff(c_143,plain,(
    ! [D_114] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_114),'#skF_1')
      | ~ m1_subset_1(D_114,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_136])).

tff(c_145,plain,(
    ! [D_115] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_115),'#skF_1')
      | ~ m1_subset_1(D_115,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_143])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_65,plain,(
    ! [C_94,B_95,A_96] :
      ( v5_relat_1(C_94,B_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_72,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_65])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_43,plain,(
    ! [B_89,A_90] :
      ( v1_relat_1(B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_90))
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_46,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_43])).

tff(c_52,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_46])).

tff(c_30,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_24,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_56,plain,(
    ! [C_91,A_92,B_93] :
      ( v4_relat_1(C_91,A_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_63,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_56])).

tff(c_75,plain,(
    ! [B_98,A_99] :
      ( k1_relat_1(B_98) = A_99
      | ~ v1_partfun1(B_98,A_99)
      | ~ v4_relat_1(B_98,A_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_81,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_63,c_75])).

tff(c_87,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_24,c_81])).

tff(c_98,plain,(
    ! [A_100,B_101,C_102] :
      ( k7_partfun1(A_100,B_101,C_102) = k1_funct_1(B_101,C_102)
      | ~ r2_hidden(C_102,k1_relat_1(B_101))
      | ~ v1_funct_1(B_101)
      | ~ v5_relat_1(B_101,A_100)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_100,plain,(
    ! [A_100,C_102] :
      ( k7_partfun1(A_100,'#skF_5',C_102) = k1_funct_1('#skF_5',C_102)
      | ~ r2_hidden(C_102,'#skF_1')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_100)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_98])).

tff(c_107,plain,(
    ! [A_103,C_104] :
      ( k7_partfun1(A_103,'#skF_5',C_104) = k1_funct_1('#skF_5',C_104)
      | ~ r2_hidden(C_104,'#skF_1')
      | ~ v5_relat_1('#skF_5',A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_30,c_100])).

tff(c_110,plain,(
    ! [A_103,A_1] :
      ( k7_partfun1(A_103,'#skF_5',A_1) = k1_funct_1('#skF_5',A_1)
      | ~ v5_relat_1('#skF_5',A_103)
      | v1_xboole_0('#skF_1')
      | ~ m1_subset_1(A_1,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2,c_107])).

tff(c_114,plain,(
    ! [A_105,A_106] :
      ( k7_partfun1(A_105,'#skF_5',A_106) = k1_funct_1('#skF_5',A_106)
      | ~ v5_relat_1('#skF_5',A_105)
      | ~ m1_subset_1(A_106,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_110])).

tff(c_117,plain,(
    ! [A_106] :
      ( k7_partfun1('#skF_3','#skF_5',A_106) = k1_funct_1('#skF_5',A_106)
      | ~ m1_subset_1(A_106,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_72,c_114])).

tff(c_149,plain,(
    ! [D_115] :
      ( k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',D_115)) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',D_115))
      | ~ m1_subset_1(D_115,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_145,c_117])).

tff(c_150,plain,(
    ! [A_117,E_116,B_119,F_121,D_118,C_120] :
      ( k3_funct_2(B_119,C_120,k8_funct_2(B_119,A_117,C_120,D_118,E_116),F_121) = k1_funct_1(E_116,k3_funct_2(B_119,A_117,D_118,F_121))
      | ~ v1_partfun1(E_116,A_117)
      | ~ m1_subset_1(F_121,B_119)
      | ~ m1_subset_1(E_116,k1_zfmisc_1(k2_zfmisc_1(A_117,C_120)))
      | ~ v1_funct_1(E_116)
      | ~ m1_subset_1(D_118,k1_zfmisc_1(k2_zfmisc_1(B_119,A_117)))
      | ~ v1_funct_2(D_118,B_119,A_117)
      | ~ v1_funct_1(D_118)
      | v1_xboole_0(B_119)
      | v1_xboole_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_152,plain,(
    ! [B_119,D_118,F_121] :
      ( k3_funct_2(B_119,'#skF_3',k8_funct_2(B_119,'#skF_1','#skF_3',D_118,'#skF_5'),F_121) = k1_funct_1('#skF_5',k3_funct_2(B_119,'#skF_1',D_118,F_121))
      | ~ v1_partfun1('#skF_5','#skF_1')
      | ~ m1_subset_1(F_121,B_119)
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_118,k1_zfmisc_1(k2_zfmisc_1(B_119,'#skF_1')))
      | ~ v1_funct_2(D_118,B_119,'#skF_1')
      | ~ v1_funct_1(D_118)
      | v1_xboole_0(B_119)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_150])).

tff(c_157,plain,(
    ! [B_119,D_118,F_121] :
      ( k3_funct_2(B_119,'#skF_3',k8_funct_2(B_119,'#skF_1','#skF_3',D_118,'#skF_5'),F_121) = k1_funct_1('#skF_5',k3_funct_2(B_119,'#skF_1',D_118,F_121))
      | ~ m1_subset_1(F_121,B_119)
      | ~ m1_subset_1(D_118,k1_zfmisc_1(k2_zfmisc_1(B_119,'#skF_1')))
      | ~ v1_funct_2(D_118,B_119,'#skF_1')
      | ~ v1_funct_1(D_118)
      | v1_xboole_0(B_119)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_152])).

tff(c_173,plain,(
    ! [B_123,D_124,F_125] :
      ( k3_funct_2(B_123,'#skF_3',k8_funct_2(B_123,'#skF_1','#skF_3',D_124,'#skF_5'),F_125) = k1_funct_1('#skF_5',k3_funct_2(B_123,'#skF_1',D_124,F_125))
      | ~ m1_subset_1(F_125,B_123)
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(B_123,'#skF_1')))
      | ~ v1_funct_2(D_124,B_123,'#skF_1')
      | ~ v1_funct_1(D_124)
      | v1_xboole_0(B_123) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_157])).

tff(c_175,plain,(
    ! [F_125] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_125) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_125))
      | ~ m1_subset_1(F_125,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_173])).

tff(c_178,plain,(
    ! [F_125] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_125) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_125))
      | ~ m1_subset_1(F_125,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_175])).

tff(c_180,plain,(
    ! [F_126] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_126) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_126))
      | ~ m1_subset_1(F_126,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_178])).

tff(c_22,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_186,plain,
    ( k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_22])).

tff(c_192,plain,(
    k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_186])).

tff(c_196,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_192])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:22:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.28  
% 2.25/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.28  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.25/1.28  
% 2.25/1.28  %Foreground sorts:
% 2.25/1.28  
% 2.25/1.28  
% 2.25/1.28  %Background operators:
% 2.25/1.28  
% 2.25/1.28  
% 2.25/1.28  %Foreground operators:
% 2.25/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.25/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.28  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.25/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.25/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.25/1.28  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.25/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.25/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.28  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.25/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.25/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.25/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.25/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.25/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.25/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.25/1.28  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.25/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.25/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.28  
% 2.25/1.30  tff(f_131, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_funct_2)).
% 2.25/1.30  tff(f_78, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 2.25/1.30  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.25/1.30  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.25/1.30  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.25/1.30  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.25/1.30  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.25/1.30  tff(f_65, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 2.25/1.30  tff(f_104, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_funct_2)).
% 2.25/1.30  tff(c_26, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.25/1.30  tff(c_38, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.25/1.30  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.25/1.30  tff(c_34, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.25/1.30  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.25/1.30  tff(c_132, plain, (![A_111, B_112, C_113, D_114]: (m1_subset_1(k3_funct_2(A_111, B_112, C_113, D_114), B_112) | ~m1_subset_1(D_114, A_111) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~v1_funct_2(C_113, A_111, B_112) | ~v1_funct_1(C_113) | v1_xboole_0(A_111))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.25/1.30  tff(c_136, plain, (![D_114]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_114), '#skF_1') | ~m1_subset_1(D_114, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_132])).
% 2.25/1.30  tff(c_143, plain, (![D_114]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_114), '#skF_1') | ~m1_subset_1(D_114, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_136])).
% 2.25/1.30  tff(c_145, plain, (![D_115]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_115), '#skF_1') | ~m1_subset_1(D_115, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_143])).
% 2.25/1.30  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.25/1.30  tff(c_65, plain, (![C_94, B_95, A_96]: (v5_relat_1(C_94, B_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.25/1.30  tff(c_72, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_65])).
% 2.25/1.30  tff(c_40, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.25/1.30  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.25/1.30  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.25/1.30  tff(c_43, plain, (![B_89, A_90]: (v1_relat_1(B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(A_90)) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.25/1.30  tff(c_46, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_43])).
% 2.25/1.30  tff(c_52, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_46])).
% 2.25/1.30  tff(c_30, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.25/1.30  tff(c_24, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.25/1.30  tff(c_56, plain, (![C_91, A_92, B_93]: (v4_relat_1(C_91, A_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.25/1.30  tff(c_63, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_56])).
% 2.25/1.30  tff(c_75, plain, (![B_98, A_99]: (k1_relat_1(B_98)=A_99 | ~v1_partfun1(B_98, A_99) | ~v4_relat_1(B_98, A_99) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.25/1.30  tff(c_81, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_63, c_75])).
% 2.25/1.30  tff(c_87, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_24, c_81])).
% 2.25/1.30  tff(c_98, plain, (![A_100, B_101, C_102]: (k7_partfun1(A_100, B_101, C_102)=k1_funct_1(B_101, C_102) | ~r2_hidden(C_102, k1_relat_1(B_101)) | ~v1_funct_1(B_101) | ~v5_relat_1(B_101, A_100) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.25/1.30  tff(c_100, plain, (![A_100, C_102]: (k7_partfun1(A_100, '#skF_5', C_102)=k1_funct_1('#skF_5', C_102) | ~r2_hidden(C_102, '#skF_1') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_100) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_98])).
% 2.25/1.30  tff(c_107, plain, (![A_103, C_104]: (k7_partfun1(A_103, '#skF_5', C_104)=k1_funct_1('#skF_5', C_104) | ~r2_hidden(C_104, '#skF_1') | ~v5_relat_1('#skF_5', A_103))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_30, c_100])).
% 2.25/1.30  tff(c_110, plain, (![A_103, A_1]: (k7_partfun1(A_103, '#skF_5', A_1)=k1_funct_1('#skF_5', A_1) | ~v5_relat_1('#skF_5', A_103) | v1_xboole_0('#skF_1') | ~m1_subset_1(A_1, '#skF_1'))), inference(resolution, [status(thm)], [c_2, c_107])).
% 2.25/1.30  tff(c_114, plain, (![A_105, A_106]: (k7_partfun1(A_105, '#skF_5', A_106)=k1_funct_1('#skF_5', A_106) | ~v5_relat_1('#skF_5', A_105) | ~m1_subset_1(A_106, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_40, c_110])).
% 2.25/1.30  tff(c_117, plain, (![A_106]: (k7_partfun1('#skF_3', '#skF_5', A_106)=k1_funct_1('#skF_5', A_106) | ~m1_subset_1(A_106, '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_114])).
% 2.25/1.30  tff(c_149, plain, (![D_115]: (k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_115))=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_115)) | ~m1_subset_1(D_115, '#skF_2'))), inference(resolution, [status(thm)], [c_145, c_117])).
% 2.25/1.30  tff(c_150, plain, (![A_117, E_116, B_119, F_121, D_118, C_120]: (k3_funct_2(B_119, C_120, k8_funct_2(B_119, A_117, C_120, D_118, E_116), F_121)=k1_funct_1(E_116, k3_funct_2(B_119, A_117, D_118, F_121)) | ~v1_partfun1(E_116, A_117) | ~m1_subset_1(F_121, B_119) | ~m1_subset_1(E_116, k1_zfmisc_1(k2_zfmisc_1(A_117, C_120))) | ~v1_funct_1(E_116) | ~m1_subset_1(D_118, k1_zfmisc_1(k2_zfmisc_1(B_119, A_117))) | ~v1_funct_2(D_118, B_119, A_117) | ~v1_funct_1(D_118) | v1_xboole_0(B_119) | v1_xboole_0(A_117))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.25/1.30  tff(c_152, plain, (![B_119, D_118, F_121]: (k3_funct_2(B_119, '#skF_3', k8_funct_2(B_119, '#skF_1', '#skF_3', D_118, '#skF_5'), F_121)=k1_funct_1('#skF_5', k3_funct_2(B_119, '#skF_1', D_118, F_121)) | ~v1_partfun1('#skF_5', '#skF_1') | ~m1_subset_1(F_121, B_119) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_118, k1_zfmisc_1(k2_zfmisc_1(B_119, '#skF_1'))) | ~v1_funct_2(D_118, B_119, '#skF_1') | ~v1_funct_1(D_118) | v1_xboole_0(B_119) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_150])).
% 2.25/1.30  tff(c_157, plain, (![B_119, D_118, F_121]: (k3_funct_2(B_119, '#skF_3', k8_funct_2(B_119, '#skF_1', '#skF_3', D_118, '#skF_5'), F_121)=k1_funct_1('#skF_5', k3_funct_2(B_119, '#skF_1', D_118, F_121)) | ~m1_subset_1(F_121, B_119) | ~m1_subset_1(D_118, k1_zfmisc_1(k2_zfmisc_1(B_119, '#skF_1'))) | ~v1_funct_2(D_118, B_119, '#skF_1') | ~v1_funct_1(D_118) | v1_xboole_0(B_119) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_152])).
% 2.25/1.30  tff(c_173, plain, (![B_123, D_124, F_125]: (k3_funct_2(B_123, '#skF_3', k8_funct_2(B_123, '#skF_1', '#skF_3', D_124, '#skF_5'), F_125)=k1_funct_1('#skF_5', k3_funct_2(B_123, '#skF_1', D_124, F_125)) | ~m1_subset_1(F_125, B_123) | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(B_123, '#skF_1'))) | ~v1_funct_2(D_124, B_123, '#skF_1') | ~v1_funct_1(D_124) | v1_xboole_0(B_123))), inference(negUnitSimplification, [status(thm)], [c_40, c_157])).
% 2.25/1.30  tff(c_175, plain, (![F_125]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_125)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_125)) | ~m1_subset_1(F_125, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_173])).
% 2.25/1.30  tff(c_178, plain, (![F_125]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_125)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_125)) | ~m1_subset_1(F_125, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_175])).
% 2.25/1.30  tff(c_180, plain, (![F_126]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_126)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_126)) | ~m1_subset_1(F_126, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_178])).
% 2.25/1.30  tff(c_22, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.25/1.30  tff(c_186, plain, (k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_180, c_22])).
% 2.25/1.30  tff(c_192, plain, (k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_186])).
% 2.25/1.30  tff(c_196, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_149, c_192])).
% 2.25/1.30  tff(c_200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_196])).
% 2.25/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.30  
% 2.25/1.30  Inference rules
% 2.25/1.30  ----------------------
% 2.25/1.30  #Ref     : 0
% 2.25/1.30  #Sup     : 29
% 2.25/1.30  #Fact    : 0
% 2.25/1.30  #Define  : 0
% 2.25/1.30  #Split   : 3
% 2.25/1.30  #Chain   : 0
% 2.25/1.30  #Close   : 0
% 2.25/1.30  
% 2.25/1.30  Ordering : KBO
% 2.25/1.30  
% 2.25/1.30  Simplification rules
% 2.25/1.30  ----------------------
% 2.25/1.30  #Subsume      : 2
% 2.25/1.30  #Demod        : 27
% 2.25/1.30  #Tautology    : 7
% 2.25/1.30  #SimpNegUnit  : 7
% 2.25/1.30  #BackRed      : 0
% 2.25/1.30  
% 2.25/1.30  #Partial instantiations: 0
% 2.25/1.30  #Strategies tried      : 1
% 2.25/1.30  
% 2.25/1.30  Timing (in seconds)
% 2.25/1.30  ----------------------
% 2.25/1.30  Preprocessing        : 0.34
% 2.25/1.30  Parsing              : 0.17
% 2.25/1.30  CNF conversion       : 0.03
% 2.25/1.30  Main loop            : 0.20
% 2.25/1.30  Inferencing          : 0.08
% 2.25/1.30  Reduction            : 0.06
% 2.25/1.30  Demodulation         : 0.05
% 2.25/1.30  BG Simplification    : 0.01
% 2.25/1.30  Subsumption          : 0.03
% 2.25/1.30  Abstraction          : 0.01
% 2.25/1.30  MUC search           : 0.00
% 2.25/1.30  Cooper               : 0.00
% 2.25/1.30  Total                : 0.58
% 2.25/1.30  Index Insertion      : 0.00
% 2.25/1.30  Index Deletion       : 0.00
% 2.25/1.30  Index Matching       : 0.00
% 2.25/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
