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
% DateTime   : Thu Dec  3 10:17:41 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 930 expanded)
%              Number of leaves         :   42 ( 341 expanded)
%              Depth                    :   13
%              Number of atoms          :  262 (3795 expanded)
%              Number of equality atoms :   82 (1179 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_168,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_143,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & ~ v1_xboole_0(C)
              & v1_funct_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

tff(f_115,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( r1_tarski(k2_relset_1(A,B,D),k1_relset_1(B,C,E))
           => ( B = k1_xboole_0
              | k8_funct_2(A,B,C,D,E) = k1_partfun1(A,B,B,C,D,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_54,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_102,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_115,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_102])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_148,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_160,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_148])).

tff(c_209,plain,(
    ! [B_95,A_96,C_97] :
      ( k1_xboole_0 = B_95
      | k1_relset_1(A_96,B_95,C_97) = A_96
      | ~ v1_funct_2(C_97,A_96,B_95)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_216,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_209])).

tff(c_223,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_160,c_216])).

tff(c_226,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_114,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_102])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_289,plain,(
    ! [B_107,C_108,A_109] :
      ( k1_funct_1(k5_relat_1(B_107,C_108),A_109) = k1_funct_1(C_108,k1_funct_1(B_107,A_109))
      | ~ r2_hidden(A_109,k1_relat_1(B_107))
      | ~ v1_funct_1(C_108)
      | ~ v1_relat_1(C_108)
      | ~ v1_funct_1(B_107)
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_335,plain,(
    ! [B_118,C_119,A_120] :
      ( k1_funct_1(k5_relat_1(B_118,C_119),A_120) = k1_funct_1(C_119,k1_funct_1(B_118,A_120))
      | ~ v1_funct_1(C_119)
      | ~ v1_relat_1(C_119)
      | ~ v1_funct_1(B_118)
      | ~ v1_relat_1(B_118)
      | v1_xboole_0(k1_relat_1(B_118))
      | ~ m1_subset_1(A_120,k1_relat_1(B_118)) ) ),
    inference(resolution,[status(thm)],[c_12,c_289])).

tff(c_337,plain,(
    ! [C_119,A_120] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_119),A_120) = k1_funct_1(C_119,k1_funct_1('#skF_4',A_120))
      | ~ v1_funct_1(C_119)
      | ~ v1_relat_1(C_119)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_120,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_335])).

tff(c_339,plain,(
    ! [C_119,A_120] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_119),A_120) = k1_funct_1(C_119,k1_funct_1('#skF_4',A_120))
      | ~ v1_funct_1(C_119)
      | ~ v1_relat_1(C_119)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_120,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_114,c_64,c_337])).

tff(c_340,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_339])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_361,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_340,c_2])).

tff(c_366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_361])).

tff(c_367,plain,(
    ! [C_119,A_120] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_119),A_120) = k1_funct_1(C_119,k1_funct_1('#skF_4',A_120))
      | ~ v1_funct_1(C_119)
      | ~ v1_relat_1(C_119)
      | ~ m1_subset_1(A_120,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_386,plain,(
    ! [E_132,F_130,D_133,A_129,B_134,C_131] :
      ( k1_partfun1(A_129,B_134,C_131,D_133,E_132,F_130) = k5_relat_1(E_132,F_130)
      | ~ m1_subset_1(F_130,k1_zfmisc_1(k2_zfmisc_1(C_131,D_133)))
      | ~ v1_funct_1(F_130)
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(A_129,B_134)))
      | ~ v1_funct_1(E_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_393,plain,(
    ! [A_129,B_134,E_132] :
      ( k1_partfun1(A_129,B_134,'#skF_3','#skF_1',E_132,'#skF_5') = k5_relat_1(E_132,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(A_129,B_134)))
      | ~ v1_funct_1(E_132) ) ),
    inference(resolution,[status(thm)],[c_56,c_386])).

tff(c_440,plain,(
    ! [A_141,B_142,E_143] :
      ( k1_partfun1(A_141,B_142,'#skF_3','#skF_1',E_143,'#skF_5') = k5_relat_1(E_143,'#skF_5')
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ v1_funct_1(E_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_393])).

tff(c_447,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_440])).

tff(c_454,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_447])).

tff(c_161,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_148])).

tff(c_52,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_166,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_52])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_268,plain,(
    ! [C_104,A_105,B_106] :
      ( ~ v1_xboole_0(C_104)
      | ~ v1_funct_2(C_104,A_105,B_106)
      | ~ v1_funct_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | v1_xboole_0(B_106)
      | v1_xboole_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_275,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_268])).

tff(c_282,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_275])).

tff(c_283,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_282])).

tff(c_288,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_283])).

tff(c_458,plain,(
    ! [C_147,D_144,E_148,A_146,B_145] :
      ( k1_partfun1(A_146,B_145,B_145,C_147,D_144,E_148) = k8_funct_2(A_146,B_145,C_147,D_144,E_148)
      | k1_xboole_0 = B_145
      | ~ r1_tarski(k2_relset_1(A_146,B_145,D_144),k1_relset_1(B_145,C_147,E_148))
      | ~ m1_subset_1(E_148,k1_zfmisc_1(k2_zfmisc_1(B_145,C_147)))
      | ~ v1_funct_1(E_148)
      | ~ m1_subset_1(D_144,k1_zfmisc_1(k2_zfmisc_1(A_146,B_145)))
      | ~ v1_funct_2(D_144,A_146,B_145)
      | ~ v1_funct_1(D_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_464,plain,(
    ! [A_146,D_144] :
      ( k1_partfun1(A_146,'#skF_3','#skF_3','#skF_1',D_144,'#skF_5') = k8_funct_2(A_146,'#skF_3','#skF_1',D_144,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_146,'#skF_3',D_144),k1_relat_1('#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_144,k1_zfmisc_1(k2_zfmisc_1(A_146,'#skF_3')))
      | ~ v1_funct_2(D_144,A_146,'#skF_3')
      | ~ v1_funct_1(D_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_458])).

tff(c_469,plain,(
    ! [A_146,D_144] :
      ( k1_partfun1(A_146,'#skF_3','#skF_3','#skF_1',D_144,'#skF_5') = k8_funct_2(A_146,'#skF_3','#skF_1',D_144,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_146,'#skF_3',D_144),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_144,k1_zfmisc_1(k2_zfmisc_1(A_146,'#skF_3')))
      | ~ v1_funct_2(D_144,A_146,'#skF_3')
      | ~ v1_funct_1(D_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_464])).

tff(c_550,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_469])).

tff(c_566,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_50])).

tff(c_77,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_84,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_60,c_77])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_171,plain,(
    ! [C_80,A_81] :
      ( k1_xboole_0 = C_80
      | ~ v1_funct_2(C_80,A_81,k1_xboole_0)
      | k1_xboole_0 = A_81
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_176,plain,(
    ! [A_9,A_81] :
      ( k1_xboole_0 = A_9
      | ~ v1_funct_2(A_9,A_81,k1_xboole_0)
      | k1_xboole_0 = A_81
      | ~ r1_tarski(A_9,k2_zfmisc_1(A_81,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_16,c_171])).

tff(c_585,plain,(
    ! [A_178,A_179] :
      ( A_178 = '#skF_3'
      | ~ v1_funct_2(A_178,A_179,'#skF_3')
      | A_179 = '#skF_3'
      | ~ r1_tarski(A_178,k2_zfmisc_1(A_179,'#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_550,c_550,c_550,c_176])).

tff(c_588,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_84,c_585])).

tff(c_591,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_588])).

tff(c_592,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_566,c_591])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(k1_xboole_0,A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_564,plain,(
    ! [A_2] : k4_xboole_0('#skF_3',A_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_550,c_4])).

tff(c_597,plain,(
    ! [A_2] : k4_xboole_0('#skF_4',A_2) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_592,c_592,c_564])).

tff(c_622,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_592,c_84])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_96,plain,(
    ! [B_63,A_64] :
      ( ~ r1_xboole_0(B_63,A_64)
      | ~ r1_tarski(B_63,A_64)
      | v1_xboole_0(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_100,plain,(
    ! [A_5,B_6] :
      ( ~ r1_tarski(A_5,B_6)
      | v1_xboole_0(A_5)
      | k4_xboole_0(A_5,B_6) != A_5 ) ),
    inference(resolution,[status(thm)],[c_10,c_96])).

tff(c_685,plain,
    ( v1_xboole_0('#skF_4')
    | k4_xboole_0('#skF_4',k2_zfmisc_1('#skF_2','#skF_4')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_622,c_100])).

tff(c_700,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_685])).

tff(c_702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_700])).

tff(c_705,plain,(
    ! [A_184,D_185] :
      ( k1_partfun1(A_184,'#skF_3','#skF_3','#skF_1',D_185,'#skF_5') = k8_funct_2(A_184,'#skF_3','#skF_1',D_185,'#skF_5')
      | ~ r1_tarski(k2_relset_1(A_184,'#skF_3',D_185),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_185,k1_zfmisc_1(k2_zfmisc_1(A_184,'#skF_3')))
      | ~ v1_funct_2(D_185,A_184,'#skF_3')
      | ~ v1_funct_1(D_185) ) ),
    inference(splitRight,[status(thm)],[c_469])).

tff(c_708,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_166,c_705])).

tff(c_711,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_454,c_708])).

tff(c_48,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_712,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_711,c_48])).

tff(c_719,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_712])).

tff(c_726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_115,c_58,c_719])).

tff(c_727,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_734,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_727,c_2])).

tff(c_739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_734])).

tff(c_740,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_754,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_50])).

tff(c_792,plain,(
    ! [A_193,A_194] :
      ( A_193 = '#skF_3'
      | ~ v1_funct_2(A_193,A_194,'#skF_3')
      | A_194 = '#skF_3'
      | ~ r1_tarski(A_193,k2_zfmisc_1(A_194,'#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_740,c_740,c_740,c_176])).

tff(c_795,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_84,c_792])).

tff(c_798,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_795])).

tff(c_799,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_754,c_798])).

tff(c_822,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_66])).

tff(c_752,plain,(
    ! [A_2] : k4_xboole_0('#skF_3',A_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_740,c_4])).

tff(c_807,plain,(
    ! [A_2] : k4_xboole_0('#skF_4',A_2) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_799,c_752])).

tff(c_818,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_84])).

tff(c_863,plain,
    ( v1_xboole_0('#skF_4')
    | k4_xboole_0('#skF_4',k2_zfmisc_1('#skF_2','#skF_4')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_818,c_100])).

tff(c_870,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_807,c_863])).

tff(c_872,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_822,c_870])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.53  
% 3.43/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.54  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.43/1.54  
% 3.43/1.54  %Foreground sorts:
% 3.43/1.54  
% 3.43/1.54  
% 3.43/1.54  %Background operators:
% 3.43/1.54  
% 3.43/1.54  
% 3.43/1.54  %Foreground operators:
% 3.43/1.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.43/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.43/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.43/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.43/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.43/1.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.43/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.43/1.54  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.43/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.43/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.43/1.54  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.43/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.43/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.43/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.43/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.43/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.43/1.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.43/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.43/1.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.43/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.43/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.43/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.43/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.43/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.43/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.43/1.54  
% 3.52/1.56  tff(f_168, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 3.52/1.56  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.52/1.56  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.52/1.56  tff(f_133, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.52/1.56  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.52/1.56  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 3.52/1.56  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.52/1.56  tff(f_143, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.52/1.56  tff(f_98, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_funct_2)).
% 3.52/1.56  tff(f_115, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_2)).
% 3.52/1.56  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.52/1.56  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.52/1.56  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.52/1.56  tff(f_39, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.52/1.56  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.52/1.56  tff(c_54, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.52/1.56  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.52/1.56  tff(c_102, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.52/1.56  tff(c_115, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_102])).
% 3.52/1.56  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.52/1.56  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.52/1.56  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.52/1.56  tff(c_148, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.52/1.56  tff(c_160, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_148])).
% 3.52/1.56  tff(c_209, plain, (![B_95, A_96, C_97]: (k1_xboole_0=B_95 | k1_relset_1(A_96, B_95, C_97)=A_96 | ~v1_funct_2(C_97, A_96, B_95) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.52/1.56  tff(c_216, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_209])).
% 3.52/1.56  tff(c_223, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_160, c_216])).
% 3.52/1.56  tff(c_226, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_223])).
% 3.52/1.56  tff(c_114, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_102])).
% 3.52/1.56  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.52/1.56  tff(c_12, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.52/1.56  tff(c_289, plain, (![B_107, C_108, A_109]: (k1_funct_1(k5_relat_1(B_107, C_108), A_109)=k1_funct_1(C_108, k1_funct_1(B_107, A_109)) | ~r2_hidden(A_109, k1_relat_1(B_107)) | ~v1_funct_1(C_108) | ~v1_relat_1(C_108) | ~v1_funct_1(B_107) | ~v1_relat_1(B_107))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.52/1.56  tff(c_335, plain, (![B_118, C_119, A_120]: (k1_funct_1(k5_relat_1(B_118, C_119), A_120)=k1_funct_1(C_119, k1_funct_1(B_118, A_120)) | ~v1_funct_1(C_119) | ~v1_relat_1(C_119) | ~v1_funct_1(B_118) | ~v1_relat_1(B_118) | v1_xboole_0(k1_relat_1(B_118)) | ~m1_subset_1(A_120, k1_relat_1(B_118)))), inference(resolution, [status(thm)], [c_12, c_289])).
% 3.52/1.56  tff(c_337, plain, (![C_119, A_120]: (k1_funct_1(k5_relat_1('#skF_4', C_119), A_120)=k1_funct_1(C_119, k1_funct_1('#skF_4', A_120)) | ~v1_funct_1(C_119) | ~v1_relat_1(C_119) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1('#skF_4')) | ~m1_subset_1(A_120, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_226, c_335])).
% 3.52/1.56  tff(c_339, plain, (![C_119, A_120]: (k1_funct_1(k5_relat_1('#skF_4', C_119), A_120)=k1_funct_1(C_119, k1_funct_1('#skF_4', A_120)) | ~v1_funct_1(C_119) | ~v1_relat_1(C_119) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_120, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_114, c_64, c_337])).
% 3.52/1.56  tff(c_340, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_339])).
% 3.52/1.56  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.52/1.56  tff(c_361, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_340, c_2])).
% 3.52/1.56  tff(c_366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_361])).
% 3.52/1.56  tff(c_367, plain, (![C_119, A_120]: (k1_funct_1(k5_relat_1('#skF_4', C_119), A_120)=k1_funct_1(C_119, k1_funct_1('#skF_4', A_120)) | ~v1_funct_1(C_119) | ~v1_relat_1(C_119) | ~m1_subset_1(A_120, '#skF_2'))), inference(splitRight, [status(thm)], [c_339])).
% 3.52/1.56  tff(c_386, plain, (![E_132, F_130, D_133, A_129, B_134, C_131]: (k1_partfun1(A_129, B_134, C_131, D_133, E_132, F_130)=k5_relat_1(E_132, F_130) | ~m1_subset_1(F_130, k1_zfmisc_1(k2_zfmisc_1(C_131, D_133))) | ~v1_funct_1(F_130) | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(A_129, B_134))) | ~v1_funct_1(E_132))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.52/1.56  tff(c_393, plain, (![A_129, B_134, E_132]: (k1_partfun1(A_129, B_134, '#skF_3', '#skF_1', E_132, '#skF_5')=k5_relat_1(E_132, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(A_129, B_134))) | ~v1_funct_1(E_132))), inference(resolution, [status(thm)], [c_56, c_386])).
% 3.52/1.56  tff(c_440, plain, (![A_141, B_142, E_143]: (k1_partfun1(A_141, B_142, '#skF_3', '#skF_1', E_143, '#skF_5')=k5_relat_1(E_143, '#skF_5') | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | ~v1_funct_1(E_143))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_393])).
% 3.52/1.56  tff(c_447, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_440])).
% 3.52/1.56  tff(c_454, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_447])).
% 3.52/1.56  tff(c_161, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_148])).
% 3.52/1.56  tff(c_52, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.52/1.56  tff(c_166, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_52])).
% 3.52/1.56  tff(c_66, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.52/1.56  tff(c_268, plain, (![C_104, A_105, B_106]: (~v1_xboole_0(C_104) | ~v1_funct_2(C_104, A_105, B_106) | ~v1_funct_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))) | v1_xboole_0(B_106) | v1_xboole_0(A_105))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.52/1.56  tff(c_275, plain, (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_268])).
% 3.52/1.56  tff(c_282, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_275])).
% 3.52/1.56  tff(c_283, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_66, c_282])).
% 3.52/1.56  tff(c_288, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_283])).
% 3.52/1.56  tff(c_458, plain, (![C_147, D_144, E_148, A_146, B_145]: (k1_partfun1(A_146, B_145, B_145, C_147, D_144, E_148)=k8_funct_2(A_146, B_145, C_147, D_144, E_148) | k1_xboole_0=B_145 | ~r1_tarski(k2_relset_1(A_146, B_145, D_144), k1_relset_1(B_145, C_147, E_148)) | ~m1_subset_1(E_148, k1_zfmisc_1(k2_zfmisc_1(B_145, C_147))) | ~v1_funct_1(E_148) | ~m1_subset_1(D_144, k1_zfmisc_1(k2_zfmisc_1(A_146, B_145))) | ~v1_funct_2(D_144, A_146, B_145) | ~v1_funct_1(D_144))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.52/1.56  tff(c_464, plain, (![A_146, D_144]: (k1_partfun1(A_146, '#skF_3', '#skF_3', '#skF_1', D_144, '#skF_5')=k8_funct_2(A_146, '#skF_3', '#skF_1', D_144, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_146, '#skF_3', D_144), k1_relat_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_144, k1_zfmisc_1(k2_zfmisc_1(A_146, '#skF_3'))) | ~v1_funct_2(D_144, A_146, '#skF_3') | ~v1_funct_1(D_144))), inference(superposition, [status(thm), theory('equality')], [c_161, c_458])).
% 3.52/1.56  tff(c_469, plain, (![A_146, D_144]: (k1_partfun1(A_146, '#skF_3', '#skF_3', '#skF_1', D_144, '#skF_5')=k8_funct_2(A_146, '#skF_3', '#skF_1', D_144, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_146, '#skF_3', D_144), k1_relat_1('#skF_5')) | ~m1_subset_1(D_144, k1_zfmisc_1(k2_zfmisc_1(A_146, '#skF_3'))) | ~v1_funct_2(D_144, A_146, '#skF_3') | ~v1_funct_1(D_144))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_464])).
% 3.52/1.56  tff(c_550, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_469])).
% 3.52/1.56  tff(c_566, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_550, c_50])).
% 3.52/1.56  tff(c_77, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.52/1.56  tff(c_84, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_60, c_77])).
% 3.52/1.56  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.52/1.56  tff(c_171, plain, (![C_80, A_81]: (k1_xboole_0=C_80 | ~v1_funct_2(C_80, A_81, k1_xboole_0) | k1_xboole_0=A_81 | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.52/1.56  tff(c_176, plain, (![A_9, A_81]: (k1_xboole_0=A_9 | ~v1_funct_2(A_9, A_81, k1_xboole_0) | k1_xboole_0=A_81 | ~r1_tarski(A_9, k2_zfmisc_1(A_81, k1_xboole_0)))), inference(resolution, [status(thm)], [c_16, c_171])).
% 3.52/1.56  tff(c_585, plain, (![A_178, A_179]: (A_178='#skF_3' | ~v1_funct_2(A_178, A_179, '#skF_3') | A_179='#skF_3' | ~r1_tarski(A_178, k2_zfmisc_1(A_179, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_550, c_550, c_550, c_550, c_176])).
% 3.52/1.56  tff(c_588, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_84, c_585])).
% 3.52/1.56  tff(c_591, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_588])).
% 3.52/1.56  tff(c_592, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_566, c_591])).
% 3.52/1.56  tff(c_4, plain, (![A_2]: (k4_xboole_0(k1_xboole_0, A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.52/1.56  tff(c_564, plain, (![A_2]: (k4_xboole_0('#skF_3', A_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_550, c_550, c_4])).
% 3.52/1.56  tff(c_597, plain, (![A_2]: (k4_xboole_0('#skF_4', A_2)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_592, c_592, c_564])).
% 3.52/1.56  tff(c_622, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_592, c_84])).
% 3.52/1.56  tff(c_10, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k4_xboole_0(A_5, B_6)!=A_5)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.52/1.56  tff(c_96, plain, (![B_63, A_64]: (~r1_xboole_0(B_63, A_64) | ~r1_tarski(B_63, A_64) | v1_xboole_0(B_63))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.52/1.56  tff(c_100, plain, (![A_5, B_6]: (~r1_tarski(A_5, B_6) | v1_xboole_0(A_5) | k4_xboole_0(A_5, B_6)!=A_5)), inference(resolution, [status(thm)], [c_10, c_96])).
% 3.52/1.56  tff(c_685, plain, (v1_xboole_0('#skF_4') | k4_xboole_0('#skF_4', k2_zfmisc_1('#skF_2', '#skF_4'))!='#skF_4'), inference(resolution, [status(thm)], [c_622, c_100])).
% 3.52/1.56  tff(c_700, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_597, c_685])).
% 3.52/1.56  tff(c_702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_288, c_700])).
% 3.52/1.56  tff(c_705, plain, (![A_184, D_185]: (k1_partfun1(A_184, '#skF_3', '#skF_3', '#skF_1', D_185, '#skF_5')=k8_funct_2(A_184, '#skF_3', '#skF_1', D_185, '#skF_5') | ~r1_tarski(k2_relset_1(A_184, '#skF_3', D_185), k1_relat_1('#skF_5')) | ~m1_subset_1(D_185, k1_zfmisc_1(k2_zfmisc_1(A_184, '#skF_3'))) | ~v1_funct_2(D_185, A_184, '#skF_3') | ~v1_funct_1(D_185))), inference(splitRight, [status(thm)], [c_469])).
% 3.52/1.56  tff(c_708, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_166, c_705])).
% 3.52/1.56  tff(c_711, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_454, c_708])).
% 3.52/1.56  tff(c_48, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.52/1.56  tff(c_712, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_711, c_48])).
% 3.52/1.56  tff(c_719, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_367, c_712])).
% 3.52/1.56  tff(c_726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_115, c_58, c_719])).
% 3.52/1.56  tff(c_727, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_283])).
% 3.52/1.56  tff(c_734, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_727, c_2])).
% 3.52/1.56  tff(c_739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_734])).
% 3.52/1.56  tff(c_740, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_223])).
% 3.52/1.56  tff(c_754, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_740, c_50])).
% 3.52/1.56  tff(c_792, plain, (![A_193, A_194]: (A_193='#skF_3' | ~v1_funct_2(A_193, A_194, '#skF_3') | A_194='#skF_3' | ~r1_tarski(A_193, k2_zfmisc_1(A_194, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_740, c_740, c_740, c_740, c_176])).
% 3.52/1.56  tff(c_795, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_84, c_792])).
% 3.52/1.56  tff(c_798, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_795])).
% 3.52/1.56  tff(c_799, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_754, c_798])).
% 3.52/1.56  tff(c_822, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_799, c_66])).
% 3.52/1.56  tff(c_752, plain, (![A_2]: (k4_xboole_0('#skF_3', A_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_740, c_740, c_4])).
% 3.52/1.56  tff(c_807, plain, (![A_2]: (k4_xboole_0('#skF_4', A_2)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_799, c_799, c_752])).
% 3.52/1.56  tff(c_818, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_799, c_84])).
% 3.52/1.56  tff(c_863, plain, (v1_xboole_0('#skF_4') | k4_xboole_0('#skF_4', k2_zfmisc_1('#skF_2', '#skF_4'))!='#skF_4'), inference(resolution, [status(thm)], [c_818, c_100])).
% 3.52/1.56  tff(c_870, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_807, c_863])).
% 3.52/1.56  tff(c_872, plain, $false, inference(negUnitSimplification, [status(thm)], [c_822, c_870])).
% 3.52/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.56  
% 3.52/1.56  Inference rules
% 3.52/1.56  ----------------------
% 3.52/1.56  #Ref     : 0
% 3.52/1.56  #Sup     : 147
% 3.52/1.56  #Fact    : 0
% 3.52/1.56  #Define  : 0
% 3.52/1.56  #Split   : 11
% 3.52/1.56  #Chain   : 0
% 3.52/1.56  #Close   : 0
% 3.52/1.56  
% 3.52/1.56  Ordering : KBO
% 3.52/1.56  
% 3.52/1.56  Simplification rules
% 3.52/1.56  ----------------------
% 3.52/1.56  #Subsume      : 14
% 3.52/1.56  #Demod        : 262
% 3.52/1.56  #Tautology    : 67
% 3.52/1.56  #SimpNegUnit  : 16
% 3.52/1.56  #BackRed      : 88
% 3.52/1.56  
% 3.52/1.56  #Partial instantiations: 0
% 3.52/1.56  #Strategies tried      : 1
% 3.52/1.56  
% 3.52/1.56  Timing (in seconds)
% 3.52/1.56  ----------------------
% 3.52/1.56  Preprocessing        : 0.37
% 3.52/1.56  Parsing              : 0.20
% 3.52/1.56  CNF conversion       : 0.03
% 3.52/1.56  Main loop            : 0.39
% 3.52/1.56  Inferencing          : 0.13
% 3.52/1.56  Reduction            : 0.13
% 3.52/1.56  Demodulation         : 0.09
% 3.52/1.56  BG Simplification    : 0.03
% 3.52/1.56  Subsumption          : 0.07
% 3.52/1.56  Abstraction          : 0.02
% 3.52/1.56  MUC search           : 0.00
% 3.52/1.56  Cooper               : 0.00
% 3.52/1.56  Total                : 0.81
% 3.52/1.56  Index Insertion      : 0.00
% 3.52/1.56  Index Deletion       : 0.00
% 3.52/1.56  Index Matching       : 0.00
% 3.52/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
