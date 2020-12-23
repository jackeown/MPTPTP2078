%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:13 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 218 expanded)
%              Number of leaves         :   35 (  93 expanded)
%              Depth                    :   16
%              Number of atoms          :  243 ( 820 expanded)
%              Number of equality atoms :   38 (  97 expanded)
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

tff(f_158,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_131,axiom,(
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

tff(c_36,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_77,plain,(
    ! [C_99,A_100,B_101] :
      ( v1_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_89,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_77])).

tff(c_91,plain,(
    ! [C_102,A_103,B_104] :
      ( v4_relat_1(C_102,A_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_103,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_91])).

tff(c_121,plain,(
    ! [B_109,A_110] :
      ( k1_relat_1(B_109) = A_110
      | ~ v1_partfun1(B_109,A_110)
      | ~ v4_relat_1(B_109,A_110)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_127,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_103,c_121])).

tff(c_133,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_127])).

tff(c_144,plain,(
    ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_150,plain,(
    ! [C_116,A_117,B_118] :
      ( v1_partfun1(C_116,A_117)
      | ~ v1_funct_2(C_116,A_117,B_118)
      | ~ v1_funct_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | v1_xboole_0(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_157,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_150])).

tff(c_164,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_157])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_144,c_164])).

tff(c_167,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_105,plain,(
    ! [C_105,B_106,A_107] :
      ( v5_relat_1(C_105,B_106)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_107,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_117,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_105])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_179,plain,(
    ! [B_119,C_120,A_121] :
      ( r2_hidden(k1_funct_1(B_119,C_120),A_121)
      | ~ r2_hidden(C_120,k1_relat_1(B_119))
      | ~ v1_funct_1(B_119)
      | ~ v5_relat_1(B_119,A_121)
      | ~ v1_relat_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( m1_subset_1(B_2,A_1)
      | ~ r2_hidden(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_270,plain,(
    ! [B_138,C_139,A_140] :
      ( m1_subset_1(k1_funct_1(B_138,C_139),A_140)
      | v1_xboole_0(A_140)
      | ~ r2_hidden(C_139,k1_relat_1(B_138))
      | ~ v1_funct_1(B_138)
      | ~ v5_relat_1(B_138,A_140)
      | ~ v1_relat_1(B_138) ) ),
    inference(resolution,[status(thm)],[c_179,c_2])).

tff(c_492,plain,(
    ! [B_165,B_166,A_167] :
      ( m1_subset_1(k1_funct_1(B_165,B_166),A_167)
      | v1_xboole_0(A_167)
      | ~ v1_funct_1(B_165)
      | ~ v5_relat_1(B_165,A_167)
      | ~ v1_relat_1(B_165)
      | ~ m1_subset_1(B_166,k1_relat_1(B_165))
      | v1_xboole_0(k1_relat_1(B_165)) ) ),
    inference(resolution,[status(thm)],[c_4,c_270])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_118,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_105])).

tff(c_90,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_77])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_34,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_104,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_91])).

tff(c_124,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_104,c_121])).

tff(c_130,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_34,c_124])).

tff(c_203,plain,(
    ! [A_125,B_126,C_127] :
      ( k7_partfun1(A_125,B_126,C_127) = k1_funct_1(B_126,C_127)
      | ~ r2_hidden(C_127,k1_relat_1(B_126))
      | ~ v1_funct_1(B_126)
      | ~ v5_relat_1(B_126,A_125)
      | ~ v1_relat_1(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_210,plain,(
    ! [A_125,C_127] :
      ( k7_partfun1(A_125,'#skF_5',C_127) = k1_funct_1('#skF_5',C_127)
      | ~ r2_hidden(C_127,'#skF_1')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_125)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_203])).

tff(c_231,plain,(
    ! [A_130,C_131] :
      ( k7_partfun1(A_130,'#skF_5',C_131) = k1_funct_1('#skF_5',C_131)
      | ~ r2_hidden(C_131,'#skF_1')
      | ~ v5_relat_1('#skF_5',A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_40,c_210])).

tff(c_237,plain,(
    ! [A_130,B_2] :
      ( k7_partfun1(A_130,'#skF_5',B_2) = k1_funct_1('#skF_5',B_2)
      | ~ v5_relat_1('#skF_5',A_130)
      | ~ m1_subset_1(B_2,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_4,c_231])).

tff(c_246,plain,(
    ! [A_134,B_135] :
      ( k7_partfun1(A_134,'#skF_5',B_135) = k1_funct_1('#skF_5',B_135)
      | ~ v5_relat_1('#skF_5',A_134)
      | ~ m1_subset_1(B_135,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_237])).

tff(c_249,plain,(
    ! [B_135] :
      ( k7_partfun1('#skF_3','#skF_5',B_135) = k1_funct_1('#skF_5',B_135)
      | ~ m1_subset_1(B_135,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_118,c_246])).

tff(c_505,plain,(
    ! [B_165,B_166] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1(B_165,B_166)) = k1_funct_1('#skF_5',k1_funct_1(B_165,B_166))
      | v1_xboole_0('#skF_1')
      | ~ v1_funct_1(B_165)
      | ~ v5_relat_1(B_165,'#skF_1')
      | ~ v1_relat_1(B_165)
      | ~ m1_subset_1(B_166,k1_relat_1(B_165))
      | v1_xboole_0(k1_relat_1(B_165)) ) ),
    inference(resolution,[status(thm)],[c_492,c_249])).

tff(c_556,plain,(
    ! [B_172,B_173] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1(B_172,B_173)) = k1_funct_1('#skF_5',k1_funct_1(B_172,B_173))
      | ~ v1_funct_1(B_172)
      | ~ v5_relat_1(B_172,'#skF_1')
      | ~ v1_relat_1(B_172)
      | ~ m1_subset_1(B_173,k1_relat_1(B_172))
      | v1_xboole_0(k1_relat_1(B_172)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_505])).

tff(c_571,plain,(
    ! [B_173] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',B_173)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',B_173))
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4','#skF_1')
      | ~ v1_relat_1('#skF_4')
      | ~ m1_subset_1(B_173,'#skF_2')
      | v1_xboole_0(k1_relat_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_556])).

tff(c_583,plain,(
    ! [B_173] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',B_173)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',B_173))
      | ~ m1_subset_1(B_173,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_89,c_117,c_46,c_571])).

tff(c_584,plain,(
    ! [B_173] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',B_173)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',B_173))
      | ~ m1_subset_1(B_173,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_583])).

tff(c_335,plain,(
    ! [A_143,B_144,C_145,D_146] :
      ( k3_funct_2(A_143,B_144,C_145,D_146) = k1_funct_1(C_145,D_146)
      | ~ m1_subset_1(D_146,A_143)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144)))
      | ~ v1_funct_2(C_145,A_143,B_144)
      | ~ v1_funct_1(C_145)
      | v1_xboole_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_345,plain,(
    ! [B_144,C_145] :
      ( k3_funct_2('#skF_2',B_144,C_145,'#skF_6') = k1_funct_1(C_145,'#skF_6')
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_144)))
      | ~ v1_funct_2(C_145,'#skF_2',B_144)
      | ~ v1_funct_1(C_145)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_335])).

tff(c_450,plain,(
    ! [B_160,C_161] :
      ( k3_funct_2('#skF_2',B_160,C_161,'#skF_6') = k1_funct_1(C_161,'#skF_6')
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_160)))
      | ~ v1_funct_2(C_161,'#skF_2',B_160)
      | ~ v1_funct_1(C_161) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_345])).

tff(c_465,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_450])).

tff(c_473,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_465])).

tff(c_420,plain,(
    ! [C_158,B_155,A_159,F_154,D_156,E_157] :
      ( k3_funct_2(B_155,C_158,k8_funct_2(B_155,A_159,C_158,D_156,E_157),F_154) = k1_funct_1(E_157,k3_funct_2(B_155,A_159,D_156,F_154))
      | ~ v1_partfun1(E_157,A_159)
      | ~ m1_subset_1(F_154,B_155)
      | ~ m1_subset_1(E_157,k1_zfmisc_1(k2_zfmisc_1(A_159,C_158)))
      | ~ v1_funct_1(E_157)
      | ~ m1_subset_1(D_156,k1_zfmisc_1(k2_zfmisc_1(B_155,A_159)))
      | ~ v1_funct_2(D_156,B_155,A_159)
      | ~ v1_funct_1(D_156)
      | v1_xboole_0(B_155)
      | v1_xboole_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_433,plain,(
    ! [B_155,D_156,F_154] :
      ( k3_funct_2(B_155,'#skF_3',k8_funct_2(B_155,'#skF_1','#skF_3',D_156,'#skF_5'),F_154) = k1_funct_1('#skF_5',k3_funct_2(B_155,'#skF_1',D_156,F_154))
      | ~ v1_partfun1('#skF_5','#skF_1')
      | ~ m1_subset_1(F_154,B_155)
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_156,k1_zfmisc_1(k2_zfmisc_1(B_155,'#skF_1')))
      | ~ v1_funct_2(D_156,B_155,'#skF_1')
      | ~ v1_funct_1(D_156)
      | v1_xboole_0(B_155)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_420])).

tff(c_445,plain,(
    ! [B_155,D_156,F_154] :
      ( k3_funct_2(B_155,'#skF_3',k8_funct_2(B_155,'#skF_1','#skF_3',D_156,'#skF_5'),F_154) = k1_funct_1('#skF_5',k3_funct_2(B_155,'#skF_1',D_156,F_154))
      | ~ m1_subset_1(F_154,B_155)
      | ~ m1_subset_1(D_156,k1_zfmisc_1(k2_zfmisc_1(B_155,'#skF_1')))
      | ~ v1_funct_2(D_156,B_155,'#skF_1')
      | ~ v1_funct_1(D_156)
      | v1_xboole_0(B_155)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_433])).

tff(c_735,plain,(
    ! [B_195,D_196,F_197] :
      ( k3_funct_2(B_195,'#skF_3',k8_funct_2(B_195,'#skF_1','#skF_3',D_196,'#skF_5'),F_197) = k1_funct_1('#skF_5',k3_funct_2(B_195,'#skF_1',D_196,F_197))
      | ~ m1_subset_1(F_197,B_195)
      | ~ m1_subset_1(D_196,k1_zfmisc_1(k2_zfmisc_1(B_195,'#skF_1')))
      | ~ v1_funct_2(D_196,B_195,'#skF_1')
      | ~ v1_funct_1(D_196)
      | v1_xboole_0(B_195) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_445])).

tff(c_749,plain,(
    ! [F_197] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_197) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_197))
      | ~ m1_subset_1(F_197,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_735])).

tff(c_760,plain,(
    ! [F_197] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_197) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_197))
      | ~ m1_subset_1(F_197,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_749])).

tff(c_762,plain,(
    ! [F_198] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_198) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_198))
      | ~ m1_subset_1(F_198,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_760])).

tff(c_32,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_474,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_32])).

tff(c_768,plain,
    ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_474])).

tff(c_774,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_473,c_768])).

tff(c_781,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_774])).

tff(c_791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_781])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:08:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.50  
% 3.18/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.50  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.18/1.50  
% 3.18/1.50  %Foreground sorts:
% 3.18/1.50  
% 3.18/1.50  
% 3.18/1.50  %Background operators:
% 3.18/1.50  
% 3.18/1.50  
% 3.18/1.50  %Foreground operators:
% 3.18/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.18/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.18/1.50  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.18/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.18/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.18/1.50  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.18/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.18/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.18/1.50  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.18/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.18/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.18/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.18/1.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.18/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.18/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.18/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.18/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.18/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.18/1.50  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.18/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.18/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.18/1.50  
% 3.18/1.52  tff(f_158, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_funct_2)).
% 3.18/1.52  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.18/1.52  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.18/1.52  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 3.18/1.52  tff(f_73, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.18/1.52  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.18/1.52  tff(f_49, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 3.18/1.52  tff(f_92, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 3.18/1.52  tff(f_105, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.18/1.52  tff(f_131, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_funct_2)).
% 3.18/1.52  tff(c_36, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.18/1.52  tff(c_48, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.18/1.52  tff(c_50, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.18/1.52  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.18/1.52  tff(c_77, plain, (![C_99, A_100, B_101]: (v1_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.18/1.52  tff(c_89, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_77])).
% 3.18/1.52  tff(c_91, plain, (![C_102, A_103, B_104]: (v4_relat_1(C_102, A_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.18/1.52  tff(c_103, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_91])).
% 3.18/1.52  tff(c_121, plain, (![B_109, A_110]: (k1_relat_1(B_109)=A_110 | ~v1_partfun1(B_109, A_110) | ~v4_relat_1(B_109, A_110) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.18/1.52  tff(c_127, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_103, c_121])).
% 3.18/1.52  tff(c_133, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_127])).
% 3.18/1.52  tff(c_144, plain, (~v1_partfun1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_133])).
% 3.18/1.52  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.18/1.52  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.18/1.52  tff(c_150, plain, (![C_116, A_117, B_118]: (v1_partfun1(C_116, A_117) | ~v1_funct_2(C_116, A_117, B_118) | ~v1_funct_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | v1_xboole_0(B_118))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.18/1.52  tff(c_157, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_150])).
% 3.18/1.52  tff(c_164, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_157])).
% 3.18/1.52  tff(c_166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_144, c_164])).
% 3.18/1.52  tff(c_167, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_133])).
% 3.18/1.52  tff(c_105, plain, (![C_105, B_106, A_107]: (v5_relat_1(C_105, B_106) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_107, B_106))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.18/1.52  tff(c_117, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_105])).
% 3.18/1.52  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.18/1.52  tff(c_179, plain, (![B_119, C_120, A_121]: (r2_hidden(k1_funct_1(B_119, C_120), A_121) | ~r2_hidden(C_120, k1_relat_1(B_119)) | ~v1_funct_1(B_119) | ~v5_relat_1(B_119, A_121) | ~v1_relat_1(B_119))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.18/1.52  tff(c_2, plain, (![B_2, A_1]: (m1_subset_1(B_2, A_1) | ~r2_hidden(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.18/1.52  tff(c_270, plain, (![B_138, C_139, A_140]: (m1_subset_1(k1_funct_1(B_138, C_139), A_140) | v1_xboole_0(A_140) | ~r2_hidden(C_139, k1_relat_1(B_138)) | ~v1_funct_1(B_138) | ~v5_relat_1(B_138, A_140) | ~v1_relat_1(B_138))), inference(resolution, [status(thm)], [c_179, c_2])).
% 3.18/1.52  tff(c_492, plain, (![B_165, B_166, A_167]: (m1_subset_1(k1_funct_1(B_165, B_166), A_167) | v1_xboole_0(A_167) | ~v1_funct_1(B_165) | ~v5_relat_1(B_165, A_167) | ~v1_relat_1(B_165) | ~m1_subset_1(B_166, k1_relat_1(B_165)) | v1_xboole_0(k1_relat_1(B_165)))), inference(resolution, [status(thm)], [c_4, c_270])).
% 3.18/1.52  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.18/1.52  tff(c_118, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_105])).
% 3.18/1.52  tff(c_90, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_77])).
% 3.18/1.52  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.18/1.52  tff(c_34, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.18/1.52  tff(c_104, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_91])).
% 3.18/1.52  tff(c_124, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_104, c_121])).
% 3.18/1.52  tff(c_130, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_34, c_124])).
% 3.18/1.52  tff(c_203, plain, (![A_125, B_126, C_127]: (k7_partfun1(A_125, B_126, C_127)=k1_funct_1(B_126, C_127) | ~r2_hidden(C_127, k1_relat_1(B_126)) | ~v1_funct_1(B_126) | ~v5_relat_1(B_126, A_125) | ~v1_relat_1(B_126))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.18/1.52  tff(c_210, plain, (![A_125, C_127]: (k7_partfun1(A_125, '#skF_5', C_127)=k1_funct_1('#skF_5', C_127) | ~r2_hidden(C_127, '#skF_1') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_125) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_130, c_203])).
% 3.18/1.52  tff(c_231, plain, (![A_130, C_131]: (k7_partfun1(A_130, '#skF_5', C_131)=k1_funct_1('#skF_5', C_131) | ~r2_hidden(C_131, '#skF_1') | ~v5_relat_1('#skF_5', A_130))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_40, c_210])).
% 3.18/1.52  tff(c_237, plain, (![A_130, B_2]: (k7_partfun1(A_130, '#skF_5', B_2)=k1_funct_1('#skF_5', B_2) | ~v5_relat_1('#skF_5', A_130) | ~m1_subset_1(B_2, '#skF_1') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_4, c_231])).
% 3.18/1.52  tff(c_246, plain, (![A_134, B_135]: (k7_partfun1(A_134, '#skF_5', B_135)=k1_funct_1('#skF_5', B_135) | ~v5_relat_1('#skF_5', A_134) | ~m1_subset_1(B_135, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_50, c_237])).
% 3.18/1.52  tff(c_249, plain, (![B_135]: (k7_partfun1('#skF_3', '#skF_5', B_135)=k1_funct_1('#skF_5', B_135) | ~m1_subset_1(B_135, '#skF_1'))), inference(resolution, [status(thm)], [c_118, c_246])).
% 3.18/1.52  tff(c_505, plain, (![B_165, B_166]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1(B_165, B_166))=k1_funct_1('#skF_5', k1_funct_1(B_165, B_166)) | v1_xboole_0('#skF_1') | ~v1_funct_1(B_165) | ~v5_relat_1(B_165, '#skF_1') | ~v1_relat_1(B_165) | ~m1_subset_1(B_166, k1_relat_1(B_165)) | v1_xboole_0(k1_relat_1(B_165)))), inference(resolution, [status(thm)], [c_492, c_249])).
% 3.18/1.52  tff(c_556, plain, (![B_172, B_173]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1(B_172, B_173))=k1_funct_1('#skF_5', k1_funct_1(B_172, B_173)) | ~v1_funct_1(B_172) | ~v5_relat_1(B_172, '#skF_1') | ~v1_relat_1(B_172) | ~m1_subset_1(B_173, k1_relat_1(B_172)) | v1_xboole_0(k1_relat_1(B_172)))), inference(negUnitSimplification, [status(thm)], [c_50, c_505])).
% 3.18/1.52  tff(c_571, plain, (![B_173]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', B_173))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', B_173)) | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4') | ~m1_subset_1(B_173, '#skF_2') | v1_xboole_0(k1_relat_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_167, c_556])).
% 3.18/1.52  tff(c_583, plain, (![B_173]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', B_173))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', B_173)) | ~m1_subset_1(B_173, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_89, c_117, c_46, c_571])).
% 3.18/1.52  tff(c_584, plain, (![B_173]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', B_173))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', B_173)) | ~m1_subset_1(B_173, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_583])).
% 3.18/1.52  tff(c_335, plain, (![A_143, B_144, C_145, D_146]: (k3_funct_2(A_143, B_144, C_145, D_146)=k1_funct_1(C_145, D_146) | ~m1_subset_1(D_146, A_143) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))) | ~v1_funct_2(C_145, A_143, B_144) | ~v1_funct_1(C_145) | v1_xboole_0(A_143))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.18/1.52  tff(c_345, plain, (![B_144, C_145]: (k3_funct_2('#skF_2', B_144, C_145, '#skF_6')=k1_funct_1(C_145, '#skF_6') | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_144))) | ~v1_funct_2(C_145, '#skF_2', B_144) | ~v1_funct_1(C_145) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_335])).
% 3.18/1.52  tff(c_450, plain, (![B_160, C_161]: (k3_funct_2('#skF_2', B_160, C_161, '#skF_6')=k1_funct_1(C_161, '#skF_6') | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_160))) | ~v1_funct_2(C_161, '#skF_2', B_160) | ~v1_funct_1(C_161))), inference(negUnitSimplification, [status(thm)], [c_48, c_345])).
% 3.18/1.52  tff(c_465, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_450])).
% 3.18/1.52  tff(c_473, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_465])).
% 3.18/1.52  tff(c_420, plain, (![C_158, B_155, A_159, F_154, D_156, E_157]: (k3_funct_2(B_155, C_158, k8_funct_2(B_155, A_159, C_158, D_156, E_157), F_154)=k1_funct_1(E_157, k3_funct_2(B_155, A_159, D_156, F_154)) | ~v1_partfun1(E_157, A_159) | ~m1_subset_1(F_154, B_155) | ~m1_subset_1(E_157, k1_zfmisc_1(k2_zfmisc_1(A_159, C_158))) | ~v1_funct_1(E_157) | ~m1_subset_1(D_156, k1_zfmisc_1(k2_zfmisc_1(B_155, A_159))) | ~v1_funct_2(D_156, B_155, A_159) | ~v1_funct_1(D_156) | v1_xboole_0(B_155) | v1_xboole_0(A_159))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.18/1.52  tff(c_433, plain, (![B_155, D_156, F_154]: (k3_funct_2(B_155, '#skF_3', k8_funct_2(B_155, '#skF_1', '#skF_3', D_156, '#skF_5'), F_154)=k1_funct_1('#skF_5', k3_funct_2(B_155, '#skF_1', D_156, F_154)) | ~v1_partfun1('#skF_5', '#skF_1') | ~m1_subset_1(F_154, B_155) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_156, k1_zfmisc_1(k2_zfmisc_1(B_155, '#skF_1'))) | ~v1_funct_2(D_156, B_155, '#skF_1') | ~v1_funct_1(D_156) | v1_xboole_0(B_155) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_420])).
% 3.18/1.52  tff(c_445, plain, (![B_155, D_156, F_154]: (k3_funct_2(B_155, '#skF_3', k8_funct_2(B_155, '#skF_1', '#skF_3', D_156, '#skF_5'), F_154)=k1_funct_1('#skF_5', k3_funct_2(B_155, '#skF_1', D_156, F_154)) | ~m1_subset_1(F_154, B_155) | ~m1_subset_1(D_156, k1_zfmisc_1(k2_zfmisc_1(B_155, '#skF_1'))) | ~v1_funct_2(D_156, B_155, '#skF_1') | ~v1_funct_1(D_156) | v1_xboole_0(B_155) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_433])).
% 3.18/1.52  tff(c_735, plain, (![B_195, D_196, F_197]: (k3_funct_2(B_195, '#skF_3', k8_funct_2(B_195, '#skF_1', '#skF_3', D_196, '#skF_5'), F_197)=k1_funct_1('#skF_5', k3_funct_2(B_195, '#skF_1', D_196, F_197)) | ~m1_subset_1(F_197, B_195) | ~m1_subset_1(D_196, k1_zfmisc_1(k2_zfmisc_1(B_195, '#skF_1'))) | ~v1_funct_2(D_196, B_195, '#skF_1') | ~v1_funct_1(D_196) | v1_xboole_0(B_195))), inference(negUnitSimplification, [status(thm)], [c_50, c_445])).
% 3.18/1.52  tff(c_749, plain, (![F_197]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_197)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_197)) | ~m1_subset_1(F_197, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_735])).
% 3.18/1.52  tff(c_760, plain, (![F_197]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_197)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_197)) | ~m1_subset_1(F_197, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_749])).
% 3.18/1.52  tff(c_762, plain, (![F_198]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_198)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_198)) | ~m1_subset_1(F_198, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_760])).
% 3.18/1.52  tff(c_32, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.18/1.52  tff(c_474, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_473, c_32])).
% 3.18/1.52  tff(c_768, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_762, c_474])).
% 3.18/1.52  tff(c_774, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_473, c_768])).
% 3.18/1.52  tff(c_781, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_584, c_774])).
% 3.18/1.52  tff(c_791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_781])).
% 3.18/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.52  
% 3.18/1.52  Inference rules
% 3.18/1.52  ----------------------
% 3.18/1.52  #Ref     : 0
% 3.18/1.52  #Sup     : 139
% 3.18/1.52  #Fact    : 0
% 3.18/1.52  #Define  : 0
% 3.18/1.52  #Split   : 9
% 3.18/1.52  #Chain   : 0
% 3.18/1.52  #Close   : 0
% 3.18/1.52  
% 3.18/1.52  Ordering : KBO
% 3.18/1.52  
% 3.18/1.52  Simplification rules
% 3.18/1.52  ----------------------
% 3.18/1.52  #Subsume      : 36
% 3.18/1.52  #Demod        : 74
% 3.18/1.52  #Tautology    : 35
% 3.18/1.52  #SimpNegUnit  : 46
% 3.18/1.52  #BackRed      : 1
% 3.18/1.52  
% 3.18/1.52  #Partial instantiations: 0
% 3.18/1.52  #Strategies tried      : 1
% 3.18/1.52  
% 3.18/1.52  Timing (in seconds)
% 3.18/1.52  ----------------------
% 3.18/1.52  Preprocessing        : 0.34
% 3.18/1.52  Parsing              : 0.17
% 3.18/1.52  CNF conversion       : 0.03
% 3.18/1.52  Main loop            : 0.36
% 3.18/1.52  Inferencing          : 0.13
% 3.18/1.52  Reduction            : 0.11
% 3.18/1.52  Demodulation         : 0.07
% 3.18/1.52  BG Simplification    : 0.02
% 3.18/1.52  Subsumption          : 0.08
% 3.18/1.52  Abstraction          : 0.02
% 3.18/1.52  MUC search           : 0.00
% 3.18/1.52  Cooper               : 0.00
% 3.18/1.52  Total                : 0.74
% 3.18/1.52  Index Insertion      : 0.00
% 3.18/1.52  Index Deletion       : 0.00
% 3.18/1.52  Index Matching       : 0.00
% 3.18/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
