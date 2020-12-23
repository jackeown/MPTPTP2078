%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:53 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 337 expanded)
%              Number of leaves         :   45 ( 136 expanded)
%              Depth                    :   14
%              Number of atoms          :  231 (1130 expanded)
%              Number of equality atoms :   53 ( 262 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_164,negated_conjecture,(
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
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_139,axiom,(
    ! [A,B,C] :
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_104,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_52,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_56,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_144,plain,(
    ! [A_89,B_90,C_91] :
      ( k2_relset_1(A_89,B_90,C_91) = k2_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_151,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_144])).

tff(c_126,plain,(
    ! [A_86,B_87,C_88] :
      ( k1_relset_1(A_86,B_87,C_88) = k1_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_134,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_126])).

tff(c_50,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_139,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_50])).

tff(c_153,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_139])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_62,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_60,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_343,plain,(
    ! [C_126,D_122,B_125,A_123,F_121,E_124] :
      ( k1_funct_1(k8_funct_2(B_125,C_126,A_123,D_122,E_124),F_121) = k1_funct_1(E_124,k1_funct_1(D_122,F_121))
      | k1_xboole_0 = B_125
      | ~ r1_tarski(k2_relset_1(B_125,C_126,D_122),k1_relset_1(C_126,A_123,E_124))
      | ~ m1_subset_1(F_121,B_125)
      | ~ m1_subset_1(E_124,k1_zfmisc_1(k2_zfmisc_1(C_126,A_123)))
      | ~ v1_funct_1(E_124)
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(B_125,C_126)))
      | ~ v1_funct_2(D_122,B_125,C_126)
      | ~ v1_funct_1(D_122)
      | v1_xboole_0(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_349,plain,(
    ! [A_123,E_124,F_121] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_123,'#skF_6',E_124),F_121) = k1_funct_1(E_124,k1_funct_1('#skF_6',F_121))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_123,E_124))
      | ~ m1_subset_1(F_121,'#skF_4')
      | ~ m1_subset_1(E_124,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_123)))
      | ~ v1_funct_1(E_124)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_343])).

tff(c_358,plain,(
    ! [A_123,E_124,F_121] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_123,'#skF_6',E_124),F_121) = k1_funct_1(E_124,k1_funct_1('#skF_6',F_121))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_123,E_124))
      | ~ m1_subset_1(F_121,'#skF_4')
      | ~ m1_subset_1(E_124,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_123)))
      | ~ v1_funct_1(E_124)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_349])).

tff(c_380,plain,(
    ! [A_130,E_131,F_132] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_130,'#skF_6',E_131),F_132) = k1_funct_1(E_131,k1_funct_1('#skF_6',F_132))
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_130,E_131))
      | ~ m1_subset_1(F_132,'#skF_4')
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_130)))
      | ~ v1_funct_1(E_131) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_48,c_358])).

tff(c_382,plain,(
    ! [F_132] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_132) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_132))
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_132,'#skF_4')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_380])).

tff(c_387,plain,(
    ! [F_132] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_132) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_132))
      | ~ m1_subset_1(F_132,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_153,c_382])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_88,plain,(
    ! [B_73,A_74] :
      ( v1_relat_1(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_91,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_58,c_88])).

tff(c_97,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_91])).

tff(c_133,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_126])).

tff(c_210,plain,(
    ! [B_106,A_107,C_108] :
      ( k1_xboole_0 = B_106
      | k1_relset_1(A_107,B_106,C_108) = A_107
      | ~ v1_funct_2(C_108,A_107,B_106)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_107,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_213,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_210])).

tff(c_219,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_133,c_213])).

tff(c_222,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_263,plain,(
    ! [A_113,B_114,C_115] :
      ( k7_partfun1(A_113,B_114,C_115) = k1_funct_1(B_114,C_115)
      | ~ r2_hidden(C_115,k1_relat_1(B_114))
      | ~ v1_funct_1(B_114)
      | ~ v5_relat_1(B_114,A_113)
      | ~ v1_relat_1(B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_265,plain,(
    ! [A_113,C_115] :
      ( k7_partfun1(A_113,'#skF_6',C_115) = k1_funct_1('#skF_6',C_115)
      | ~ r2_hidden(C_115,'#skF_4')
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_113)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_263])).

tff(c_305,plain,(
    ! [A_118,C_119] :
      ( k7_partfun1(A_118,'#skF_6',C_119) = k1_funct_1('#skF_6',C_119)
      | ~ r2_hidden(C_119,'#skF_4')
      | ~ v5_relat_1('#skF_6',A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_62,c_265])).

tff(c_320,plain,(
    ! [A_118] :
      ( k7_partfun1(A_118,'#skF_6','#skF_1'('#skF_4')) = k1_funct_1('#skF_6','#skF_1'('#skF_4'))
      | ~ v5_relat_1('#skF_6',A_118)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4,c_305])).

tff(c_333,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_320])).

tff(c_67,plain,(
    ! [A_68] :
      ( r2_hidden('#skF_2'(A_68),A_68)
      | k1_xboole_0 = A_68 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_68] :
      ( ~ v1_xboole_0(A_68)
      | k1_xboole_0 = A_68 ) ),
    inference(resolution,[status(thm)],[c_67,c_2])).

tff(c_336,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_333,c_71])).

tff(c_340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_336])).

tff(c_342,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_111,plain,(
    ! [C_80,B_81,A_82] :
      ( v5_relat_1(C_80,B_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_119,plain,(
    v5_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_111])).

tff(c_94,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_88])).

tff(c_100,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_94])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( v5_relat_1(B_13,A_12)
      | ~ r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_161,plain,
    ( v5_relat_1('#skF_6',k1_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_153,c_14])).

tff(c_164,plain,(
    v5_relat_1('#skF_6',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_161])).

tff(c_20,plain,(
    ! [B_17,C_19,A_16] :
      ( r2_hidden(k1_funct_1(B_17,C_19),A_16)
      | ~ r2_hidden(C_19,k1_relat_1(B_17))
      | ~ v1_funct_1(B_17)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_604,plain,(
    ! [A_156,B_157,B_158,C_159] :
      ( k7_partfun1(A_156,B_157,k1_funct_1(B_158,C_159)) = k1_funct_1(B_157,k1_funct_1(B_158,C_159))
      | ~ v1_funct_1(B_157)
      | ~ v5_relat_1(B_157,A_156)
      | ~ v1_relat_1(B_157)
      | ~ r2_hidden(C_159,k1_relat_1(B_158))
      | ~ v1_funct_1(B_158)
      | ~ v5_relat_1(B_158,k1_relat_1(B_157))
      | ~ v1_relat_1(B_158) ) ),
    inference(resolution,[status(thm)],[c_20,c_263])).

tff(c_606,plain,(
    ! [A_156,B_157,C_159] :
      ( k7_partfun1(A_156,B_157,k1_funct_1('#skF_6',C_159)) = k1_funct_1(B_157,k1_funct_1('#skF_6',C_159))
      | ~ v1_funct_1(B_157)
      | ~ v5_relat_1(B_157,A_156)
      | ~ v1_relat_1(B_157)
      | ~ r2_hidden(C_159,'#skF_4')
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',k1_relat_1(B_157))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_604])).

tff(c_625,plain,(
    ! [A_160,B_161,C_162] :
      ( k7_partfun1(A_160,B_161,k1_funct_1('#skF_6',C_162)) = k1_funct_1(B_161,k1_funct_1('#skF_6',C_162))
      | ~ v1_funct_1(B_161)
      | ~ v5_relat_1(B_161,A_160)
      | ~ v1_relat_1(B_161)
      | ~ r2_hidden(C_162,'#skF_4')
      | ~ v5_relat_1('#skF_6',k1_relat_1(B_161)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_62,c_606])).

tff(c_629,plain,(
    ! [A_160,C_162] :
      ( k7_partfun1(A_160,'#skF_7',k1_funct_1('#skF_6',C_162)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',C_162))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_160)
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_162,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_164,c_625])).

tff(c_635,plain,(
    ! [A_163,C_164] :
      ( k7_partfun1(A_163,'#skF_7',k1_funct_1('#skF_6',C_164)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',C_164))
      | ~ v5_relat_1('#skF_7',A_163)
      | ~ r2_hidden(C_164,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_56,c_629])).

tff(c_46,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_641,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ v5_relat_1('#skF_7','#skF_3')
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_46])).

tff(c_647,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_641])).

tff(c_649,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_647])).

tff(c_652,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_649])).

tff(c_655,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_652])).

tff(c_657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_655])).

tff(c_658,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_647])).

tff(c_695,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_658])).

tff(c_699,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_695])).

tff(c_700,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_709,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_700,c_6])).

tff(c_712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_709])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:51:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.42  
% 2.99/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.42  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4
% 2.99/1.42  
% 2.99/1.42  %Foreground sorts:
% 2.99/1.42  
% 2.99/1.42  
% 2.99/1.42  %Background operators:
% 2.99/1.42  
% 2.99/1.42  
% 2.99/1.42  %Foreground operators:
% 2.99/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.99/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.99/1.42  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.99/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.99/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.99/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.99/1.42  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.99/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.99/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.99/1.42  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.99/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.99/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.99/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.99/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.99/1.42  tff('#skF_8', type, '#skF_8': $i).
% 2.99/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.99/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.99/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.99/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.99/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.99/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.99/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.42  
% 3.20/1.44  tff(f_164, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 3.20/1.44  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.20/1.44  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.20/1.44  tff(f_139, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 3.20/1.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.20/1.44  tff(f_61, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.20/1.44  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.20/1.44  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.20/1.44  tff(f_115, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 3.20/1.44  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.20/1.44  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.20/1.44  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.20/1.44  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.20/1.44  tff(f_72, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 3.20/1.44  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.20/1.44  tff(c_64, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.20/1.44  tff(c_52, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.20/1.44  tff(c_56, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.20/1.44  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.20/1.44  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.20/1.44  tff(c_144, plain, (![A_89, B_90, C_91]: (k2_relset_1(A_89, B_90, C_91)=k2_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.20/1.44  tff(c_151, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_144])).
% 3.20/1.44  tff(c_126, plain, (![A_86, B_87, C_88]: (k1_relset_1(A_86, B_87, C_88)=k1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.20/1.44  tff(c_134, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_54, c_126])).
% 3.20/1.44  tff(c_50, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.20/1.44  tff(c_139, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_50])).
% 3.20/1.44  tff(c_153, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_139])).
% 3.20/1.44  tff(c_48, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.20/1.44  tff(c_62, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.20/1.44  tff(c_60, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.20/1.44  tff(c_343, plain, (![C_126, D_122, B_125, A_123, F_121, E_124]: (k1_funct_1(k8_funct_2(B_125, C_126, A_123, D_122, E_124), F_121)=k1_funct_1(E_124, k1_funct_1(D_122, F_121)) | k1_xboole_0=B_125 | ~r1_tarski(k2_relset_1(B_125, C_126, D_122), k1_relset_1(C_126, A_123, E_124)) | ~m1_subset_1(F_121, B_125) | ~m1_subset_1(E_124, k1_zfmisc_1(k2_zfmisc_1(C_126, A_123))) | ~v1_funct_1(E_124) | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(B_125, C_126))) | ~v1_funct_2(D_122, B_125, C_126) | ~v1_funct_1(D_122) | v1_xboole_0(C_126))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.20/1.44  tff(c_349, plain, (![A_123, E_124, F_121]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_123, '#skF_6', E_124), F_121)=k1_funct_1(E_124, k1_funct_1('#skF_6', F_121)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_123, E_124)) | ~m1_subset_1(F_121, '#skF_4') | ~m1_subset_1(E_124, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_123))) | ~v1_funct_1(E_124) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_343])).
% 3.20/1.44  tff(c_358, plain, (![A_123, E_124, F_121]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_123, '#skF_6', E_124), F_121)=k1_funct_1(E_124, k1_funct_1('#skF_6', F_121)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_123, E_124)) | ~m1_subset_1(F_121, '#skF_4') | ~m1_subset_1(E_124, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_123))) | ~v1_funct_1(E_124) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_349])).
% 3.20/1.44  tff(c_380, plain, (![A_130, E_131, F_132]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_130, '#skF_6', E_131), F_132)=k1_funct_1(E_131, k1_funct_1('#skF_6', F_132)) | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_130, E_131)) | ~m1_subset_1(F_132, '#skF_4') | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_130))) | ~v1_funct_1(E_131))), inference(negUnitSimplification, [status(thm)], [c_64, c_48, c_358])).
% 3.20/1.44  tff(c_382, plain, (![F_132]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_132)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_132)) | ~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~m1_subset_1(F_132, '#skF_4') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_380])).
% 3.20/1.44  tff(c_387, plain, (![F_132]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_132)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_132)) | ~m1_subset_1(F_132, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_153, c_382])).
% 3.20/1.44  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.44  tff(c_18, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.20/1.44  tff(c_88, plain, (![B_73, A_74]: (v1_relat_1(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.20/1.44  tff(c_91, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_58, c_88])).
% 3.20/1.44  tff(c_97, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_91])).
% 3.20/1.44  tff(c_133, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_126])).
% 3.20/1.44  tff(c_210, plain, (![B_106, A_107, C_108]: (k1_xboole_0=B_106 | k1_relset_1(A_107, B_106, C_108)=A_107 | ~v1_funct_2(C_108, A_107, B_106) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_107, B_106))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.20/1.44  tff(c_213, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_210])).
% 3.20/1.44  tff(c_219, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_133, c_213])).
% 3.20/1.44  tff(c_222, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_219])).
% 3.20/1.44  tff(c_263, plain, (![A_113, B_114, C_115]: (k7_partfun1(A_113, B_114, C_115)=k1_funct_1(B_114, C_115) | ~r2_hidden(C_115, k1_relat_1(B_114)) | ~v1_funct_1(B_114) | ~v5_relat_1(B_114, A_113) | ~v1_relat_1(B_114))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.20/1.44  tff(c_265, plain, (![A_113, C_115]: (k7_partfun1(A_113, '#skF_6', C_115)=k1_funct_1('#skF_6', C_115) | ~r2_hidden(C_115, '#skF_4') | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_113) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_222, c_263])).
% 3.20/1.44  tff(c_305, plain, (![A_118, C_119]: (k7_partfun1(A_118, '#skF_6', C_119)=k1_funct_1('#skF_6', C_119) | ~r2_hidden(C_119, '#skF_4') | ~v5_relat_1('#skF_6', A_118))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_62, c_265])).
% 3.20/1.44  tff(c_320, plain, (![A_118]: (k7_partfun1(A_118, '#skF_6', '#skF_1'('#skF_4'))=k1_funct_1('#skF_6', '#skF_1'('#skF_4')) | ~v5_relat_1('#skF_6', A_118) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_305])).
% 3.20/1.44  tff(c_333, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_320])).
% 3.20/1.44  tff(c_67, plain, (![A_68]: (r2_hidden('#skF_2'(A_68), A_68) | k1_xboole_0=A_68)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.20/1.44  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.44  tff(c_71, plain, (![A_68]: (~v1_xboole_0(A_68) | k1_xboole_0=A_68)), inference(resolution, [status(thm)], [c_67, c_2])).
% 3.20/1.44  tff(c_336, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_333, c_71])).
% 3.20/1.44  tff(c_340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_336])).
% 3.20/1.44  tff(c_342, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_320])).
% 3.20/1.44  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.20/1.44  tff(c_111, plain, (![C_80, B_81, A_82]: (v5_relat_1(C_80, B_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.20/1.44  tff(c_119, plain, (v5_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_111])).
% 3.20/1.44  tff(c_94, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_88])).
% 3.20/1.44  tff(c_100, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_94])).
% 3.20/1.44  tff(c_14, plain, (![B_13, A_12]: (v5_relat_1(B_13, A_12) | ~r1_tarski(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.20/1.44  tff(c_161, plain, (v5_relat_1('#skF_6', k1_relat_1('#skF_7')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_153, c_14])).
% 3.20/1.44  tff(c_164, plain, (v5_relat_1('#skF_6', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_161])).
% 3.20/1.44  tff(c_20, plain, (![B_17, C_19, A_16]: (r2_hidden(k1_funct_1(B_17, C_19), A_16) | ~r2_hidden(C_19, k1_relat_1(B_17)) | ~v1_funct_1(B_17) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.20/1.44  tff(c_604, plain, (![A_156, B_157, B_158, C_159]: (k7_partfun1(A_156, B_157, k1_funct_1(B_158, C_159))=k1_funct_1(B_157, k1_funct_1(B_158, C_159)) | ~v1_funct_1(B_157) | ~v5_relat_1(B_157, A_156) | ~v1_relat_1(B_157) | ~r2_hidden(C_159, k1_relat_1(B_158)) | ~v1_funct_1(B_158) | ~v5_relat_1(B_158, k1_relat_1(B_157)) | ~v1_relat_1(B_158))), inference(resolution, [status(thm)], [c_20, c_263])).
% 3.20/1.44  tff(c_606, plain, (![A_156, B_157, C_159]: (k7_partfun1(A_156, B_157, k1_funct_1('#skF_6', C_159))=k1_funct_1(B_157, k1_funct_1('#skF_6', C_159)) | ~v1_funct_1(B_157) | ~v5_relat_1(B_157, A_156) | ~v1_relat_1(B_157) | ~r2_hidden(C_159, '#skF_4') | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', k1_relat_1(B_157)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_222, c_604])).
% 3.20/1.44  tff(c_625, plain, (![A_160, B_161, C_162]: (k7_partfun1(A_160, B_161, k1_funct_1('#skF_6', C_162))=k1_funct_1(B_161, k1_funct_1('#skF_6', C_162)) | ~v1_funct_1(B_161) | ~v5_relat_1(B_161, A_160) | ~v1_relat_1(B_161) | ~r2_hidden(C_162, '#skF_4') | ~v5_relat_1('#skF_6', k1_relat_1(B_161)))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_62, c_606])).
% 3.20/1.44  tff(c_629, plain, (![A_160, C_162]: (k7_partfun1(A_160, '#skF_7', k1_funct_1('#skF_6', C_162))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', C_162)) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_160) | ~v1_relat_1('#skF_7') | ~r2_hidden(C_162, '#skF_4'))), inference(resolution, [status(thm)], [c_164, c_625])).
% 3.20/1.44  tff(c_635, plain, (![A_163, C_164]: (k7_partfun1(A_163, '#skF_7', k1_funct_1('#skF_6', C_164))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', C_164)) | ~v5_relat_1('#skF_7', A_163) | ~r2_hidden(C_164, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_56, c_629])).
% 3.20/1.44  tff(c_46, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.20/1.44  tff(c_641, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', '#skF_3') | ~r2_hidden('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_635, c_46])).
% 3.20/1.44  tff(c_647, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~r2_hidden('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_641])).
% 3.20/1.44  tff(c_649, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(splitLeft, [status(thm)], [c_647])).
% 3.20/1.44  tff(c_652, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_10, c_649])).
% 3.20/1.44  tff(c_655, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_652])).
% 3.20/1.44  tff(c_657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_342, c_655])).
% 3.20/1.44  tff(c_658, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_647])).
% 3.20/1.44  tff(c_695, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_387, c_658])).
% 3.20/1.44  tff(c_699, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_695])).
% 3.20/1.44  tff(c_700, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_219])).
% 3.20/1.44  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.20/1.44  tff(c_709, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_700, c_6])).
% 3.20/1.44  tff(c_712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_709])).
% 3.20/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.44  
% 3.20/1.44  Inference rules
% 3.20/1.44  ----------------------
% 3.20/1.44  #Ref     : 0
% 3.20/1.44  #Sup     : 128
% 3.20/1.44  #Fact    : 0
% 3.20/1.44  #Define  : 0
% 3.20/1.44  #Split   : 9
% 3.20/1.44  #Chain   : 0
% 3.20/1.44  #Close   : 0
% 3.20/1.44  
% 3.20/1.44  Ordering : KBO
% 3.20/1.44  
% 3.20/1.44  Simplification rules
% 3.20/1.44  ----------------------
% 3.20/1.44  #Subsume      : 19
% 3.20/1.44  #Demod        : 148
% 3.20/1.44  #Tautology    : 50
% 3.20/1.44  #SimpNegUnit  : 22
% 3.20/1.44  #BackRed      : 12
% 3.20/1.44  
% 3.20/1.44  #Partial instantiations: 0
% 3.20/1.44  #Strategies tried      : 1
% 3.20/1.44  
% 3.20/1.44  Timing (in seconds)
% 3.20/1.44  ----------------------
% 3.20/1.44  Preprocessing        : 0.35
% 3.20/1.44  Parsing              : 0.18
% 3.20/1.44  CNF conversion       : 0.03
% 3.20/1.44  Main loop            : 0.35
% 3.20/1.44  Inferencing          : 0.13
% 3.20/1.44  Reduction            : 0.12
% 3.20/1.44  Demodulation         : 0.08
% 3.20/1.44  BG Simplification    : 0.02
% 3.20/1.44  Subsumption          : 0.06
% 3.20/1.44  Abstraction          : 0.02
% 3.20/1.44  MUC search           : 0.00
% 3.20/1.44  Cooper               : 0.00
% 3.20/1.44  Total                : 0.74
% 3.20/1.44  Index Insertion      : 0.00
% 3.20/1.44  Index Deletion       : 0.00
% 3.20/1.44  Index Matching       : 0.00
% 3.20/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
