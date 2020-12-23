%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:40 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 235 expanded)
%              Number of leaves         :   34 (  91 expanded)
%              Depth                    :   10
%              Number of atoms          :  177 ( 591 expanded)
%              Number of equality atoms :   16 (  97 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => v1_xboole_0(k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_109,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(c_70,plain,(
    r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_136,plain,(
    ! [A_70,B_71,D_72] :
      ( '#skF_5'(A_70,B_71,k1_funct_2(A_70,B_71),D_72) = D_72
      | ~ r2_hidden(D_72,k1_funct_2(A_70,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_143,plain,(
    '#skF_5'('#skF_6','#skF_7',k1_funct_2('#skF_6','#skF_7'),'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_70,c_136])).

tff(c_148,plain,(
    ! [A_73,B_74,D_75] :
      ( v1_relat_1('#skF_5'(A_73,B_74,k1_funct_2(A_73,B_74),D_75))
      | ~ r2_hidden(D_75,k1_funct_2(A_73,B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_151,plain,
    ( v1_relat_1('#skF_8')
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_148])).

tff(c_153,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_151])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_181,plain,(
    ! [A_86,B_87,D_88] :
      ( k1_relat_1('#skF_5'(A_86,B_87,k1_funct_2(A_86,B_87),D_88)) = A_86
      | ~ r2_hidden(D_88,k1_funct_2(A_86,B_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_205,plain,
    ( k1_relat_1('#skF_8') = '#skF_6'
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_181])).

tff(c_209,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_205])).

tff(c_210,plain,(
    ! [A_89,B_90,D_91] :
      ( r1_tarski(k2_relat_1('#skF_5'(A_89,B_90,k1_funct_2(A_89,B_90),D_91)),B_90)
      | ~ r2_hidden(D_91,k1_funct_2(A_89,B_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_218,plain,
    ( r1_tarski(k2_relat_1('#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_210])).

tff(c_222,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_218])).

tff(c_394,plain,(
    ! [C_119,A_120,B_121] :
      ( m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ r1_tarski(k2_relat_1(C_119),B_121)
      | ~ r1_tarski(k1_relat_1(C_119),A_120)
      | ~ v1_relat_1(C_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_68,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_96,plain,(
    ~ v1_funct_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_105,plain,(
    ! [A_58,B_59,D_60] :
      ( '#skF_5'(A_58,B_59,k1_funct_2(A_58,B_59),D_60) = D_60
      | ~ r2_hidden(D_60,k1_funct_2(A_58,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_112,plain,(
    '#skF_5'('#skF_6','#skF_7',k1_funct_2('#skF_6','#skF_7'),'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_70,c_105])).

tff(c_117,plain,(
    ! [A_61,B_62,D_63] :
      ( v1_funct_1('#skF_5'(A_61,B_62,k1_funct_2(A_61,B_62),D_63))
      | ~ r2_hidden(D_63,k1_funct_2(A_61,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_120,plain,
    ( v1_funct_1('#skF_8')
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_117])).

tff(c_122,plain,(
    v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_120])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_122])).

tff(c_125,plain,
    ( ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_127,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_403,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7')
    | ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_6')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_394,c_127])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_10,c_209,c_222,c_403])).

tff(c_410,plain,(
    ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_126,plain,(
    v1_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_411,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_413,plain,(
    ! [C_123,A_124,B_125] :
      ( v1_partfun1(C_123,A_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ v1_xboole_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_417,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_411,c_413])).

tff(c_418,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_417])).

tff(c_60,plain,(
    ! [A_41,B_42] :
      ( v1_xboole_0(k1_funct_2(A_41,B_42))
      | ~ v1_xboole_0(B_42)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_425,plain,(
    ! [A_128,B_129,D_130] :
      ( '#skF_5'(A_128,B_129,k1_funct_2(A_128,B_129),D_130) = D_130
      | ~ r2_hidden(D_130,k1_funct_2(A_128,B_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_432,plain,(
    '#skF_5'('#skF_6','#skF_7',k1_funct_2('#skF_6','#skF_7'),'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_70,c_425])).

tff(c_443,plain,(
    ! [A_134,B_135,D_136] :
      ( v1_relat_1('#skF_5'(A_134,B_135,k1_funct_2(A_134,B_135),D_136))
      | ~ r2_hidden(D_136,k1_funct_2(A_134,B_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_446,plain,
    ( v1_relat_1('#skF_8')
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_443])).

tff(c_448,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_446])).

tff(c_469,plain,(
    ! [A_143,B_144,D_145] :
      ( k1_relat_1('#skF_5'(A_143,B_144,k1_funct_2(A_143,B_144),D_145)) = A_143
      | ~ r2_hidden(D_145,k1_funct_2(A_143,B_144)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_493,plain,
    ( k1_relat_1('#skF_8') = '#skF_6'
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_469])).

tff(c_497,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_493])).

tff(c_449,plain,(
    ! [E_137,B_138] :
      ( r2_hidden(E_137,k1_funct_2(k1_relat_1(E_137),B_138))
      | ~ r1_tarski(k2_relat_1(E_137),B_138)
      | ~ v1_funct_1(E_137)
      | ~ v1_relat_1(E_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_456,plain,(
    ! [E_137,B_138] :
      ( ~ v1_xboole_0(k1_funct_2(k1_relat_1(E_137),B_138))
      | ~ r1_tarski(k2_relat_1(E_137),B_138)
      | ~ v1_funct_1(E_137)
      | ~ v1_relat_1(E_137) ) ),
    inference(resolution,[status(thm)],[c_449,c_2])).

tff(c_501,plain,(
    ! [B_138] :
      ( ~ v1_xboole_0(k1_funct_2('#skF_6',B_138))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_138)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_456])).

tff(c_531,plain,(
    ! [B_146] :
      ( ~ v1_xboole_0(k1_funct_2('#skF_6',B_146))
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_126,c_501])).

tff(c_536,plain,(
    ~ v1_xboole_0(k1_funct_2('#skF_6',k2_relat_1('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_10,c_531])).

tff(c_539,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_8'))
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_536])).

tff(c_542,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_418,c_539])).

tff(c_609,plain,(
    ! [C_153,A_154,B_155] :
      ( v1_funct_2(C_153,A_154,B_155)
      | ~ v1_partfun1(C_153,A_154)
      | ~ v1_funct_1(C_153)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_618,plain,
    ( v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ v1_partfun1('#skF_8','#skF_6')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_411,c_609])).

tff(c_625,plain,
    ( v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ v1_partfun1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_618])).

tff(c_626,plain,(
    ~ v1_partfun1('#skF_8','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_410,c_625])).

tff(c_64,plain,(
    ! [A_43] :
      ( v1_funct_2(A_43,k1_relat_1(A_43),k2_relat_1(A_43))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_513,plain,
    ( v1_funct_2('#skF_8','#skF_6',k2_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_64])).

tff(c_525,plain,(
    v1_funct_2('#skF_8','#skF_6',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_126,c_513])).

tff(c_62,plain,(
    ! [A_43] :
      ( m1_subset_1(A_43,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_43),k2_relat_1(A_43))))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_510,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8'))))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_62])).

tff(c_523,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_126,c_510])).

tff(c_748,plain,(
    ! [C_187,A_188,B_189] :
      ( v1_partfun1(C_187,A_188)
      | ~ v1_funct_2(C_187,A_188,B_189)
      | ~ v1_funct_1(C_187)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189)))
      | v1_xboole_0(B_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_754,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | ~ v1_funct_2('#skF_8','#skF_6',k2_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_523,c_748])).

tff(c_764,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_525,c_754])).

tff(c_766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_542,c_626,c_764])).

tff(c_767,plain,(
    v1_partfun1('#skF_8','#skF_6') ),
    inference(splitRight,[status(thm)],[c_417])).

tff(c_917,plain,(
    ! [C_211,A_212,B_213] :
      ( v1_funct_2(C_211,A_212,B_213)
      | ~ v1_partfun1(C_211,A_212)
      | ~ v1_funct_1(C_211)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_212,B_213))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_926,plain,
    ( v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ v1_partfun1('#skF_8','#skF_6')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_411,c_917])).

tff(c_933,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_767,c_926])).

tff(c_935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_410,c_933])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.77  
% 3.53/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.77  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_5 > #skF_3
% 3.53/1.77  
% 3.53/1.77  %Foreground sorts:
% 3.53/1.77  
% 3.53/1.77  
% 3.53/1.77  %Background operators:
% 3.53/1.77  
% 3.53/1.77  
% 3.53/1.77  %Foreground operators:
% 3.53/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.53/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.53/1.77  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.53/1.77  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.53/1.77  tff('#skF_7', type, '#skF_7': $i).
% 3.53/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.53/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.53/1.77  tff('#skF_6', type, '#skF_6': $i).
% 3.53/1.77  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.53/1.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.53/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.77  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 3.53/1.77  tff('#skF_8', type, '#skF_8': $i).
% 3.53/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.77  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.53/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.53/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.53/1.77  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.53/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.53/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.53/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.77  
% 3.53/1.80  tff(f_118, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 3.53/1.80  tff(f_92, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 3.53/1.80  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.53/1.80  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.53/1.80  tff(f_62, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 3.53/1.80  tff(f_99, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_2)).
% 3.53/1.80  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.53/1.80  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 3.53/1.80  tff(f_109, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 3.53/1.80  tff(f_76, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.53/1.80  tff(c_70, plain, (r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.53/1.80  tff(c_136, plain, (![A_70, B_71, D_72]: ('#skF_5'(A_70, B_71, k1_funct_2(A_70, B_71), D_72)=D_72 | ~r2_hidden(D_72, k1_funct_2(A_70, B_71)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.53/1.80  tff(c_143, plain, ('#skF_5'('#skF_6', '#skF_7', k1_funct_2('#skF_6', '#skF_7'), '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_70, c_136])).
% 3.53/1.80  tff(c_148, plain, (![A_73, B_74, D_75]: (v1_relat_1('#skF_5'(A_73, B_74, k1_funct_2(A_73, B_74), D_75)) | ~r2_hidden(D_75, k1_funct_2(A_73, B_74)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.53/1.80  tff(c_151, plain, (v1_relat_1('#skF_8') | ~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_143, c_148])).
% 3.53/1.80  tff(c_153, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_151])).
% 3.53/1.80  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.53/1.80  tff(c_181, plain, (![A_86, B_87, D_88]: (k1_relat_1('#skF_5'(A_86, B_87, k1_funct_2(A_86, B_87), D_88))=A_86 | ~r2_hidden(D_88, k1_funct_2(A_86, B_87)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.53/1.80  tff(c_205, plain, (k1_relat_1('#skF_8')='#skF_6' | ~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_143, c_181])).
% 3.53/1.80  tff(c_209, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_205])).
% 3.53/1.80  tff(c_210, plain, (![A_89, B_90, D_91]: (r1_tarski(k2_relat_1('#skF_5'(A_89, B_90, k1_funct_2(A_89, B_90), D_91)), B_90) | ~r2_hidden(D_91, k1_funct_2(A_89, B_90)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.53/1.80  tff(c_218, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7') | ~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_143, c_210])).
% 3.53/1.80  tff(c_222, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_218])).
% 3.53/1.80  tff(c_394, plain, (![C_119, A_120, B_121]: (m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | ~r1_tarski(k2_relat_1(C_119), B_121) | ~r1_tarski(k1_relat_1(C_119), A_120) | ~v1_relat_1(C_119))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.53/1.80  tff(c_68, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.53/1.80  tff(c_96, plain, (~v1_funct_1('#skF_8')), inference(splitLeft, [status(thm)], [c_68])).
% 3.53/1.80  tff(c_105, plain, (![A_58, B_59, D_60]: ('#skF_5'(A_58, B_59, k1_funct_2(A_58, B_59), D_60)=D_60 | ~r2_hidden(D_60, k1_funct_2(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.53/1.80  tff(c_112, plain, ('#skF_5'('#skF_6', '#skF_7', k1_funct_2('#skF_6', '#skF_7'), '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_70, c_105])).
% 3.53/1.80  tff(c_117, plain, (![A_61, B_62, D_63]: (v1_funct_1('#skF_5'(A_61, B_62, k1_funct_2(A_61, B_62), D_63)) | ~r2_hidden(D_63, k1_funct_2(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.53/1.80  tff(c_120, plain, (v1_funct_1('#skF_8') | ~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_117])).
% 3.53/1.80  tff(c_122, plain, (v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_120])).
% 3.53/1.80  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_122])).
% 3.53/1.80  tff(c_125, plain, (~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(splitRight, [status(thm)], [c_68])).
% 3.53/1.80  tff(c_127, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(splitLeft, [status(thm)], [c_125])).
% 3.53/1.80  tff(c_403, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7') | ~r1_tarski(k1_relat_1('#skF_8'), '#skF_6') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_394, c_127])).
% 3.53/1.80  tff(c_409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_153, c_10, c_209, c_222, c_403])).
% 3.53/1.80  tff(c_410, plain, (~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_125])).
% 3.53/1.80  tff(c_126, plain, (v1_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_68])).
% 3.53/1.80  tff(c_411, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(splitRight, [status(thm)], [c_125])).
% 3.53/1.80  tff(c_413, plain, (![C_123, A_124, B_125]: (v1_partfun1(C_123, A_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~v1_xboole_0(A_124))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.53/1.80  tff(c_417, plain, (v1_partfun1('#skF_8', '#skF_6') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_411, c_413])).
% 3.53/1.80  tff(c_418, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_417])).
% 3.53/1.80  tff(c_60, plain, (![A_41, B_42]: (v1_xboole_0(k1_funct_2(A_41, B_42)) | ~v1_xboole_0(B_42) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.53/1.80  tff(c_425, plain, (![A_128, B_129, D_130]: ('#skF_5'(A_128, B_129, k1_funct_2(A_128, B_129), D_130)=D_130 | ~r2_hidden(D_130, k1_funct_2(A_128, B_129)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.53/1.80  tff(c_432, plain, ('#skF_5'('#skF_6', '#skF_7', k1_funct_2('#skF_6', '#skF_7'), '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_70, c_425])).
% 3.53/1.80  tff(c_443, plain, (![A_134, B_135, D_136]: (v1_relat_1('#skF_5'(A_134, B_135, k1_funct_2(A_134, B_135), D_136)) | ~r2_hidden(D_136, k1_funct_2(A_134, B_135)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.53/1.80  tff(c_446, plain, (v1_relat_1('#skF_8') | ~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_432, c_443])).
% 3.53/1.80  tff(c_448, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_446])).
% 3.53/1.80  tff(c_469, plain, (![A_143, B_144, D_145]: (k1_relat_1('#skF_5'(A_143, B_144, k1_funct_2(A_143, B_144), D_145))=A_143 | ~r2_hidden(D_145, k1_funct_2(A_143, B_144)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.53/1.80  tff(c_493, plain, (k1_relat_1('#skF_8')='#skF_6' | ~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_432, c_469])).
% 3.53/1.80  tff(c_497, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_493])).
% 3.53/1.80  tff(c_449, plain, (![E_137, B_138]: (r2_hidden(E_137, k1_funct_2(k1_relat_1(E_137), B_138)) | ~r1_tarski(k2_relat_1(E_137), B_138) | ~v1_funct_1(E_137) | ~v1_relat_1(E_137))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.53/1.80  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.80  tff(c_456, plain, (![E_137, B_138]: (~v1_xboole_0(k1_funct_2(k1_relat_1(E_137), B_138)) | ~r1_tarski(k2_relat_1(E_137), B_138) | ~v1_funct_1(E_137) | ~v1_relat_1(E_137))), inference(resolution, [status(thm)], [c_449, c_2])).
% 3.53/1.80  tff(c_501, plain, (![B_138]: (~v1_xboole_0(k1_funct_2('#skF_6', B_138)) | ~r1_tarski(k2_relat_1('#skF_8'), B_138) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_497, c_456])).
% 3.53/1.80  tff(c_531, plain, (![B_146]: (~v1_xboole_0(k1_funct_2('#skF_6', B_146)) | ~r1_tarski(k2_relat_1('#skF_8'), B_146))), inference(demodulation, [status(thm), theory('equality')], [c_448, c_126, c_501])).
% 3.53/1.80  tff(c_536, plain, (~v1_xboole_0(k1_funct_2('#skF_6', k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_10, c_531])).
% 3.53/1.80  tff(c_539, plain, (~v1_xboole_0(k2_relat_1('#skF_8')) | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_60, c_536])).
% 3.53/1.80  tff(c_542, plain, (~v1_xboole_0(k2_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_418, c_539])).
% 3.53/1.80  tff(c_609, plain, (![C_153, A_154, B_155]: (v1_funct_2(C_153, A_154, B_155) | ~v1_partfun1(C_153, A_154) | ~v1_funct_1(C_153) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.53/1.80  tff(c_618, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_411, c_609])).
% 3.53/1.80  tff(c_625, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~v1_partfun1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_618])).
% 3.53/1.80  tff(c_626, plain, (~v1_partfun1('#skF_8', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_410, c_625])).
% 3.53/1.80  tff(c_64, plain, (![A_43]: (v1_funct_2(A_43, k1_relat_1(A_43), k2_relat_1(A_43)) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.53/1.80  tff(c_513, plain, (v1_funct_2('#skF_8', '#skF_6', k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_497, c_64])).
% 3.53/1.80  tff(c_525, plain, (v1_funct_2('#skF_8', '#skF_6', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_448, c_126, c_513])).
% 3.53/1.80  tff(c_62, plain, (![A_43]: (m1_subset_1(A_43, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_43), k2_relat_1(A_43)))) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.53/1.80  tff(c_510, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8')))) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_497, c_62])).
% 3.53/1.80  tff(c_523, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_448, c_126, c_510])).
% 3.53/1.80  tff(c_748, plain, (![C_187, A_188, B_189]: (v1_partfun1(C_187, A_188) | ~v1_funct_2(C_187, A_188, B_189) | ~v1_funct_1(C_187) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))) | v1_xboole_0(B_189))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.53/1.80  tff(c_754, plain, (v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_2('#skF_8', '#skF_6', k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | v1_xboole_0(k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_523, c_748])).
% 3.53/1.80  tff(c_764, plain, (v1_partfun1('#skF_8', '#skF_6') | v1_xboole_0(k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_525, c_754])).
% 3.53/1.80  tff(c_766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_542, c_626, c_764])).
% 3.53/1.80  tff(c_767, plain, (v1_partfun1('#skF_8', '#skF_6')), inference(splitRight, [status(thm)], [c_417])).
% 3.53/1.80  tff(c_917, plain, (![C_211, A_212, B_213]: (v1_funct_2(C_211, A_212, B_213) | ~v1_partfun1(C_211, A_212) | ~v1_funct_1(C_211) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_212, B_213))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.53/1.80  tff(c_926, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_411, c_917])).
% 3.53/1.80  tff(c_933, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_767, c_926])).
% 3.53/1.80  tff(c_935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_410, c_933])).
% 3.53/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.80  
% 3.53/1.80  Inference rules
% 3.53/1.80  ----------------------
% 3.53/1.80  #Ref     : 0
% 3.53/1.80  #Sup     : 195
% 3.53/1.80  #Fact    : 0
% 3.53/1.80  #Define  : 0
% 3.53/1.80  #Split   : 7
% 3.53/1.80  #Chain   : 0
% 3.53/1.80  #Close   : 0
% 3.53/1.80  
% 3.53/1.80  Ordering : KBO
% 3.53/1.80  
% 3.53/1.80  Simplification rules
% 3.53/1.80  ----------------------
% 3.53/1.80  #Subsume      : 20
% 3.53/1.80  #Demod        : 96
% 3.53/1.80  #Tautology    : 58
% 3.53/1.80  #SimpNegUnit  : 8
% 3.53/1.80  #BackRed      : 0
% 3.53/1.80  
% 3.53/1.80  #Partial instantiations: 0
% 3.53/1.80  #Strategies tried      : 1
% 3.53/1.80  
% 3.53/1.80  Timing (in seconds)
% 3.53/1.80  ----------------------
% 3.53/1.81  Preprocessing        : 0.47
% 3.53/1.81  Parsing              : 0.23
% 3.53/1.81  CNF conversion       : 0.03
% 3.53/1.81  Main loop            : 0.48
% 3.53/1.81  Inferencing          : 0.19
% 3.53/1.81  Reduction            : 0.14
% 3.53/1.81  Demodulation         : 0.10
% 3.53/1.81  BG Simplification    : 0.04
% 3.53/1.81  Subsumption          : 0.08
% 3.53/1.81  Abstraction          : 0.03
% 3.53/1.81  MUC search           : 0.00
% 3.53/1.81  Cooper               : 0.00
% 3.53/1.81  Total                : 1.01
% 3.53/1.81  Index Insertion      : 0.00
% 3.53/1.81  Index Deletion       : 0.00
% 3.53/1.81  Index Matching       : 0.00
% 3.53/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
