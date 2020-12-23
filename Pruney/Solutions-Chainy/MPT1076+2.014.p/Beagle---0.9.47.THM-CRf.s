%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:14 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 191 expanded)
%              Number of leaves         :   35 (  84 expanded)
%              Depth                    :   14
%              Number of atoms          :  211 ( 704 expanded)
%              Number of equality atoms :   33 (  83 expanded)
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

tff(f_151,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_124,axiom,(
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

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_30,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_55,plain,(
    ! [C_96,B_97,A_98] :
      ( v5_relat_1(C_96,B_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_63,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_55])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_45,plain,(
    ! [C_91,A_92,B_93] :
      ( v1_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_45])).

tff(c_62,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_55])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_64,plain,(
    ! [C_99,A_100,B_101] :
      ( v4_relat_1(C_99,A_100)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_71,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_64])).

tff(c_74,plain,(
    ! [B_103,A_104] :
      ( k1_relat_1(B_103) = A_104
      | ~ v1_partfun1(B_103,A_104)
      | ~ v4_relat_1(B_103,A_104)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_77,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_71,c_74])).

tff(c_83,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_77])).

tff(c_96,plain,(
    ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_38,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_98,plain,(
    ! [C_108,A_109,B_110] :
      ( v1_partfun1(C_108,A_109)
      | ~ v1_funct_2(C_108,A_109,B_110)
      | ~ v1_funct_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | v1_xboole_0(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_101,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_98])).

tff(c_107,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_101])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_96,c_107])).

tff(c_110,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_4,plain,(
    ! [B_4,C_6,A_3] :
      ( r2_hidden(k1_funct_1(B_4,C_6),A_3)
      | ~ r2_hidden(C_6,k1_relat_1(B_4))
      | ~ v1_funct_1(B_4)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_53,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_45])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_28,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_72,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_64])).

tff(c_80,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_74])).

tff(c_86,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_28,c_80])).

tff(c_137,plain,(
    ! [A_117,B_118,C_119] :
      ( k7_partfun1(A_117,B_118,C_119) = k1_funct_1(B_118,C_119)
      | ~ r2_hidden(C_119,k1_relat_1(B_118))
      | ~ v1_funct_1(B_118)
      | ~ v5_relat_1(B_118,A_117)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_144,plain,(
    ! [A_117,C_119] :
      ( k7_partfun1(A_117,'#skF_5',C_119) = k1_funct_1('#skF_5',C_119)
      | ~ r2_hidden(C_119,'#skF_1')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_117)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_137])).

tff(c_165,plain,(
    ! [A_122,C_123] :
      ( k7_partfun1(A_122,'#skF_5',C_123) = k1_funct_1('#skF_5',C_123)
      | ~ r2_hidden(C_123,'#skF_1')
      | ~ v5_relat_1('#skF_5',A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_34,c_144])).

tff(c_244,plain,(
    ! [A_145,B_146,C_147] :
      ( k7_partfun1(A_145,'#skF_5',k1_funct_1(B_146,C_147)) = k1_funct_1('#skF_5',k1_funct_1(B_146,C_147))
      | ~ v5_relat_1('#skF_5',A_145)
      | ~ r2_hidden(C_147,k1_relat_1(B_146))
      | ~ v1_funct_1(B_146)
      | ~ v5_relat_1(B_146,'#skF_1')
      | ~ v1_relat_1(B_146) ) ),
    inference(resolution,[status(thm)],[c_4,c_165])).

tff(c_249,plain,(
    ! [A_145,C_147] :
      ( k7_partfun1(A_145,'#skF_5',k1_funct_1('#skF_4',C_147)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',C_147))
      | ~ v5_relat_1('#skF_5',A_145)
      | ~ r2_hidden(C_147,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4','#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_244])).

tff(c_257,plain,(
    ! [A_145,C_147] :
      ( k7_partfun1(A_145,'#skF_5',k1_funct_1('#skF_4',C_147)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',C_147))
      | ~ v5_relat_1('#skF_5',A_145)
      | ~ r2_hidden(C_147,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_62,c_40,c_249])).

tff(c_176,plain,(
    ! [A_124,B_125,C_126,D_127] :
      ( k3_funct_2(A_124,B_125,C_126,D_127) = k1_funct_1(C_126,D_127)
      | ~ m1_subset_1(D_127,A_124)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ v1_funct_2(C_126,A_124,B_125)
      | ~ v1_funct_1(C_126)
      | v1_xboole_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_182,plain,(
    ! [B_125,C_126] :
      ( k3_funct_2('#skF_2',B_125,C_126,'#skF_6') = k1_funct_1(C_126,'#skF_6')
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_125)))
      | ~ v1_funct_2(C_126,'#skF_2',B_125)
      | ~ v1_funct_1(C_126)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_176])).

tff(c_206,plain,(
    ! [B_134,C_135] :
      ( k3_funct_2('#skF_2',B_134,C_135,'#skF_6') = k1_funct_1(C_135,'#skF_6')
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_134)))
      | ~ v1_funct_2(C_135,'#skF_2',B_134)
      | ~ v1_funct_1(C_135) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_182])).

tff(c_209,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_206])).

tff(c_212,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_209])).

tff(c_231,plain,(
    ! [B_140,C_143,D_141,A_144,F_139,E_142] :
      ( k3_funct_2(B_140,C_143,k8_funct_2(B_140,A_144,C_143,D_141,E_142),F_139) = k1_funct_1(E_142,k3_funct_2(B_140,A_144,D_141,F_139))
      | ~ v1_partfun1(E_142,A_144)
      | ~ m1_subset_1(F_139,B_140)
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_144,C_143)))
      | ~ v1_funct_1(E_142)
      | ~ m1_subset_1(D_141,k1_zfmisc_1(k2_zfmisc_1(B_140,A_144)))
      | ~ v1_funct_2(D_141,B_140,A_144)
      | ~ v1_funct_1(D_141)
      | v1_xboole_0(B_140)
      | v1_xboole_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_235,plain,(
    ! [B_140,D_141,F_139] :
      ( k3_funct_2(B_140,'#skF_3',k8_funct_2(B_140,'#skF_1','#skF_3',D_141,'#skF_5'),F_139) = k1_funct_1('#skF_5',k3_funct_2(B_140,'#skF_1',D_141,F_139))
      | ~ v1_partfun1('#skF_5','#skF_1')
      | ~ m1_subset_1(F_139,B_140)
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_141,k1_zfmisc_1(k2_zfmisc_1(B_140,'#skF_1')))
      | ~ v1_funct_2(D_141,B_140,'#skF_1')
      | ~ v1_funct_1(D_141)
      | v1_xboole_0(B_140)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_231])).

tff(c_242,plain,(
    ! [B_140,D_141,F_139] :
      ( k3_funct_2(B_140,'#skF_3',k8_funct_2(B_140,'#skF_1','#skF_3',D_141,'#skF_5'),F_139) = k1_funct_1('#skF_5',k3_funct_2(B_140,'#skF_1',D_141,F_139))
      | ~ m1_subset_1(F_139,B_140)
      | ~ m1_subset_1(D_141,k1_zfmisc_1(k2_zfmisc_1(B_140,'#skF_1')))
      | ~ v1_funct_2(D_141,B_140,'#skF_1')
      | ~ v1_funct_1(D_141)
      | v1_xboole_0(B_140)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_235])).

tff(c_317,plain,(
    ! [B_160,D_161,F_162] :
      ( k3_funct_2(B_160,'#skF_3',k8_funct_2(B_160,'#skF_1','#skF_3',D_161,'#skF_5'),F_162) = k1_funct_1('#skF_5',k3_funct_2(B_160,'#skF_1',D_161,F_162))
      | ~ m1_subset_1(F_162,B_160)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(B_160,'#skF_1')))
      | ~ v1_funct_2(D_161,B_160,'#skF_1')
      | ~ v1_funct_1(D_161)
      | v1_xboole_0(B_160) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_242])).

tff(c_319,plain,(
    ! [F_162] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_162) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_162))
      | ~ m1_subset_1(F_162,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_317])).

tff(c_322,plain,(
    ! [F_162] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_162) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_162))
      | ~ m1_subset_1(F_162,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_319])).

tff(c_324,plain,(
    ! [F_163] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_163) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_163))
      | ~ m1_subset_1(F_163,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_322])).

tff(c_26,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_213,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_26])).

tff(c_330,plain,
    ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_213])).

tff(c_336,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_212,c_330])).

tff(c_340,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_336])).

tff(c_343,plain,(
    ~ r2_hidden('#skF_6','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_340])).

tff(c_346,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_343])).

tff(c_349,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_346])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:04:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.41  
% 2.61/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.41  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.61/1.41  
% 2.61/1.41  %Foreground sorts:
% 2.61/1.41  
% 2.61/1.41  
% 2.61/1.41  %Background operators:
% 2.61/1.41  
% 2.61/1.41  
% 2.61/1.41  %Foreground operators:
% 2.61/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.61/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.41  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.61/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.61/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.61/1.41  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.61/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.61/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.41  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.61/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.61/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.61/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.61/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.61/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.61/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.41  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.61/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.61/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.41  
% 2.86/1.43  tff(f_151, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_funct_2)).
% 2.86/1.43  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.86/1.43  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.86/1.43  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.86/1.43  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 2.86/1.43  tff(f_66, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.86/1.43  tff(f_42, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 2.86/1.43  tff(f_85, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 2.86/1.43  tff(f_98, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.86/1.43  tff(f_124, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_funct_2)).
% 2.86/1.43  tff(c_42, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.86/1.43  tff(c_30, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.86/1.43  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.86/1.43  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.86/1.43  tff(c_55, plain, (![C_96, B_97, A_98]: (v5_relat_1(C_96, B_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.86/1.43  tff(c_63, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_55])).
% 2.86/1.43  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.86/1.43  tff(c_45, plain, (![C_91, A_92, B_93]: (v1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.86/1.43  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_45])).
% 2.86/1.43  tff(c_62, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_55])).
% 2.86/1.43  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.86/1.43  tff(c_44, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.86/1.43  tff(c_64, plain, (![C_99, A_100, B_101]: (v4_relat_1(C_99, A_100) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.86/1.43  tff(c_71, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_64])).
% 2.86/1.43  tff(c_74, plain, (![B_103, A_104]: (k1_relat_1(B_103)=A_104 | ~v1_partfun1(B_103, A_104) | ~v4_relat_1(B_103, A_104) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.86/1.43  tff(c_77, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_71, c_74])).
% 2.86/1.43  tff(c_83, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_77])).
% 2.86/1.43  tff(c_96, plain, (~v1_partfun1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_83])).
% 2.86/1.43  tff(c_38, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.86/1.43  tff(c_98, plain, (![C_108, A_109, B_110]: (v1_partfun1(C_108, A_109) | ~v1_funct_2(C_108, A_109, B_110) | ~v1_funct_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | v1_xboole_0(B_110))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.86/1.43  tff(c_101, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_98])).
% 2.86/1.43  tff(c_107, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_101])).
% 2.86/1.43  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_96, c_107])).
% 2.86/1.43  tff(c_110, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_83])).
% 2.86/1.43  tff(c_4, plain, (![B_4, C_6, A_3]: (r2_hidden(k1_funct_1(B_4, C_6), A_3) | ~r2_hidden(C_6, k1_relat_1(B_4)) | ~v1_funct_1(B_4) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.86/1.43  tff(c_53, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_45])).
% 2.86/1.43  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.86/1.43  tff(c_28, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.86/1.43  tff(c_72, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_64])).
% 2.86/1.43  tff(c_80, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_74])).
% 2.86/1.43  tff(c_86, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_53, c_28, c_80])).
% 2.86/1.43  tff(c_137, plain, (![A_117, B_118, C_119]: (k7_partfun1(A_117, B_118, C_119)=k1_funct_1(B_118, C_119) | ~r2_hidden(C_119, k1_relat_1(B_118)) | ~v1_funct_1(B_118) | ~v5_relat_1(B_118, A_117) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.86/1.43  tff(c_144, plain, (![A_117, C_119]: (k7_partfun1(A_117, '#skF_5', C_119)=k1_funct_1('#skF_5', C_119) | ~r2_hidden(C_119, '#skF_1') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_117) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_137])).
% 2.86/1.43  tff(c_165, plain, (![A_122, C_123]: (k7_partfun1(A_122, '#skF_5', C_123)=k1_funct_1('#skF_5', C_123) | ~r2_hidden(C_123, '#skF_1') | ~v5_relat_1('#skF_5', A_122))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_34, c_144])).
% 2.86/1.43  tff(c_244, plain, (![A_145, B_146, C_147]: (k7_partfun1(A_145, '#skF_5', k1_funct_1(B_146, C_147))=k1_funct_1('#skF_5', k1_funct_1(B_146, C_147)) | ~v5_relat_1('#skF_5', A_145) | ~r2_hidden(C_147, k1_relat_1(B_146)) | ~v1_funct_1(B_146) | ~v5_relat_1(B_146, '#skF_1') | ~v1_relat_1(B_146))), inference(resolution, [status(thm)], [c_4, c_165])).
% 2.86/1.43  tff(c_249, plain, (![A_145, C_147]: (k7_partfun1(A_145, '#skF_5', k1_funct_1('#skF_4', C_147))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', C_147)) | ~v5_relat_1('#skF_5', A_145) | ~r2_hidden(C_147, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_244])).
% 2.86/1.43  tff(c_257, plain, (![A_145, C_147]: (k7_partfun1(A_145, '#skF_5', k1_funct_1('#skF_4', C_147))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', C_147)) | ~v5_relat_1('#skF_5', A_145) | ~r2_hidden(C_147, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_62, c_40, c_249])).
% 2.86/1.43  tff(c_176, plain, (![A_124, B_125, C_126, D_127]: (k3_funct_2(A_124, B_125, C_126, D_127)=k1_funct_1(C_126, D_127) | ~m1_subset_1(D_127, A_124) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~v1_funct_2(C_126, A_124, B_125) | ~v1_funct_1(C_126) | v1_xboole_0(A_124))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.86/1.43  tff(c_182, plain, (![B_125, C_126]: (k3_funct_2('#skF_2', B_125, C_126, '#skF_6')=k1_funct_1(C_126, '#skF_6') | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_125))) | ~v1_funct_2(C_126, '#skF_2', B_125) | ~v1_funct_1(C_126) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_176])).
% 2.86/1.43  tff(c_206, plain, (![B_134, C_135]: (k3_funct_2('#skF_2', B_134, C_135, '#skF_6')=k1_funct_1(C_135, '#skF_6') | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_134))) | ~v1_funct_2(C_135, '#skF_2', B_134) | ~v1_funct_1(C_135))), inference(negUnitSimplification, [status(thm)], [c_42, c_182])).
% 2.86/1.43  tff(c_209, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_206])).
% 2.86/1.43  tff(c_212, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_209])).
% 2.86/1.43  tff(c_231, plain, (![B_140, C_143, D_141, A_144, F_139, E_142]: (k3_funct_2(B_140, C_143, k8_funct_2(B_140, A_144, C_143, D_141, E_142), F_139)=k1_funct_1(E_142, k3_funct_2(B_140, A_144, D_141, F_139)) | ~v1_partfun1(E_142, A_144) | ~m1_subset_1(F_139, B_140) | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_144, C_143))) | ~v1_funct_1(E_142) | ~m1_subset_1(D_141, k1_zfmisc_1(k2_zfmisc_1(B_140, A_144))) | ~v1_funct_2(D_141, B_140, A_144) | ~v1_funct_1(D_141) | v1_xboole_0(B_140) | v1_xboole_0(A_144))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.86/1.43  tff(c_235, plain, (![B_140, D_141, F_139]: (k3_funct_2(B_140, '#skF_3', k8_funct_2(B_140, '#skF_1', '#skF_3', D_141, '#skF_5'), F_139)=k1_funct_1('#skF_5', k3_funct_2(B_140, '#skF_1', D_141, F_139)) | ~v1_partfun1('#skF_5', '#skF_1') | ~m1_subset_1(F_139, B_140) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_141, k1_zfmisc_1(k2_zfmisc_1(B_140, '#skF_1'))) | ~v1_funct_2(D_141, B_140, '#skF_1') | ~v1_funct_1(D_141) | v1_xboole_0(B_140) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_231])).
% 2.86/1.43  tff(c_242, plain, (![B_140, D_141, F_139]: (k3_funct_2(B_140, '#skF_3', k8_funct_2(B_140, '#skF_1', '#skF_3', D_141, '#skF_5'), F_139)=k1_funct_1('#skF_5', k3_funct_2(B_140, '#skF_1', D_141, F_139)) | ~m1_subset_1(F_139, B_140) | ~m1_subset_1(D_141, k1_zfmisc_1(k2_zfmisc_1(B_140, '#skF_1'))) | ~v1_funct_2(D_141, B_140, '#skF_1') | ~v1_funct_1(D_141) | v1_xboole_0(B_140) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_235])).
% 2.86/1.43  tff(c_317, plain, (![B_160, D_161, F_162]: (k3_funct_2(B_160, '#skF_3', k8_funct_2(B_160, '#skF_1', '#skF_3', D_161, '#skF_5'), F_162)=k1_funct_1('#skF_5', k3_funct_2(B_160, '#skF_1', D_161, F_162)) | ~m1_subset_1(F_162, B_160) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(B_160, '#skF_1'))) | ~v1_funct_2(D_161, B_160, '#skF_1') | ~v1_funct_1(D_161) | v1_xboole_0(B_160))), inference(negUnitSimplification, [status(thm)], [c_44, c_242])).
% 2.86/1.43  tff(c_319, plain, (![F_162]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_162)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_162)) | ~m1_subset_1(F_162, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_317])).
% 2.86/1.43  tff(c_322, plain, (![F_162]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_162)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_162)) | ~m1_subset_1(F_162, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_319])).
% 2.86/1.43  tff(c_324, plain, (![F_163]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_163)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_163)) | ~m1_subset_1(F_163, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_322])).
% 2.86/1.43  tff(c_26, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.86/1.43  tff(c_213, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_26])).
% 2.86/1.43  tff(c_330, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_324, c_213])).
% 2.86/1.43  tff(c_336, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_212, c_330])).
% 2.86/1.43  tff(c_340, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~r2_hidden('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_257, c_336])).
% 2.86/1.43  tff(c_343, plain, (~r2_hidden('#skF_6', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_340])).
% 2.86/1.43  tff(c_346, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_2, c_343])).
% 2.86/1.43  tff(c_349, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_346])).
% 2.86/1.43  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_349])).
% 2.86/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.43  
% 2.86/1.43  Inference rules
% 2.86/1.43  ----------------------
% 2.86/1.43  #Ref     : 0
% 2.86/1.43  #Sup     : 63
% 2.86/1.43  #Fact    : 0
% 2.86/1.43  #Define  : 0
% 2.86/1.43  #Split   : 5
% 2.86/1.43  #Chain   : 0
% 2.86/1.43  #Close   : 0
% 2.86/1.43  
% 2.86/1.43  Ordering : KBO
% 2.86/1.43  
% 2.86/1.43  Simplification rules
% 2.86/1.43  ----------------------
% 2.86/1.43  #Subsume      : 4
% 2.86/1.43  #Demod        : 60
% 2.86/1.43  #Tautology    : 17
% 2.86/1.43  #SimpNegUnit  : 11
% 2.86/1.43  #BackRed      : 1
% 2.86/1.43  
% 2.86/1.43  #Partial instantiations: 0
% 2.86/1.43  #Strategies tried      : 1
% 2.86/1.43  
% 2.86/1.43  Timing (in seconds)
% 2.86/1.43  ----------------------
% 2.86/1.44  Preprocessing        : 0.35
% 2.86/1.44  Parsing              : 0.19
% 2.86/1.44  CNF conversion       : 0.03
% 2.86/1.44  Main loop            : 0.27
% 2.86/1.44  Inferencing          : 0.10
% 2.86/1.44  Reduction            : 0.08
% 2.86/1.44  Demodulation         : 0.06
% 2.86/1.44  BG Simplification    : 0.02
% 2.86/1.44  Subsumption          : 0.05
% 2.86/1.44  Abstraction          : 0.02
% 2.86/1.44  MUC search           : 0.00
% 2.86/1.44  Cooper               : 0.00
% 2.86/1.44  Total                : 0.66
% 2.86/1.44  Index Insertion      : 0.00
% 2.86/1.44  Index Deletion       : 0.00
% 2.86/1.44  Index Matching       : 0.00
% 2.86/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
