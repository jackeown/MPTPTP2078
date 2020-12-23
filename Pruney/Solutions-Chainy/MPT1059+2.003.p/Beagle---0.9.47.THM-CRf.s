%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:33 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 120 expanded)
%              Number of leaves         :   36 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :  134 ( 297 expanded)
%              Number of equality atoms :   34 (  66 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_159,negated_conjecture,(
    ~ ! [A] :
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_139,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_63,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_115,axiom,(
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

tff(f_126,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_27,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_54,plain,(
    m1_subset_1('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_424,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( k3_funct_2(A_119,B_120,C_121,D_122) = k1_funct_1(C_121,D_122)
      | ~ m1_subset_1(D_122,A_119)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ v1_funct_2(C_121,A_119,B_120)
      | ~ v1_funct_1(C_121)
      | v1_xboole_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_432,plain,(
    ! [B_120,C_121] :
      ( k3_funct_2('#skF_2',B_120,C_121,'#skF_5') = k1_funct_1(C_121,'#skF_5')
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_120)))
      | ~ v1_funct_2(C_121,'#skF_2',B_120)
      | ~ v1_funct_1(C_121)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_424])).

tff(c_443,plain,(
    ! [B_124,C_125] :
      ( k3_funct_2('#skF_2',B_124,C_125,'#skF_5') = k1_funct_1(C_125,'#skF_5')
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_124)))
      | ~ v1_funct_2(C_125,'#skF_2',B_124)
      | ~ v1_funct_1(C_125) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_432])).

tff(c_446,plain,
    ( k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_443])).

tff(c_457,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_446])).

tff(c_52,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') != k7_partfun1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_461,plain,(
    k7_partfun1('#skF_3','#skF_4','#skF_5') != k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_52])).

tff(c_178,plain,(
    ! [C_72,B_73,A_74] :
      ( v5_relat_1(C_72,B_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_192,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_178])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_124,plain,(
    ! [B_59,A_60] :
      ( v1_relat_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_127,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_124])).

tff(c_133,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_127])).

tff(c_229,plain,(
    ! [A_87,B_88,C_89] :
      ( k1_relset_1(A_87,B_88,C_89) = k1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_243,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_229])).

tff(c_319,plain,(
    ! [B_105,A_106,C_107] :
      ( k1_xboole_0 = B_105
      | k1_relset_1(A_106,B_105,C_107) = A_106
      | ~ v1_funct_2(C_107,A_106,B_105)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_322,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_319])).

tff(c_335,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_243,c_322])).

tff(c_339,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_335])).

tff(c_372,plain,(
    ! [A_111,B_112,C_113] :
      ( k7_partfun1(A_111,B_112,C_113) = k1_funct_1(B_112,C_113)
      | ~ r2_hidden(C_113,k1_relat_1(B_112))
      | ~ v1_funct_1(B_112)
      | ~ v5_relat_1(B_112,A_111)
      | ~ v1_relat_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_374,plain,(
    ! [A_111,C_113] :
      ( k7_partfun1(A_111,'#skF_4',C_113) = k1_funct_1('#skF_4',C_113)
      | ~ r2_hidden(C_113,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_111)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_372])).

tff(c_535,plain,(
    ! [A_130,C_131] :
      ( k7_partfun1(A_130,'#skF_4',C_131) = k1_funct_1('#skF_4',C_131)
      | ~ r2_hidden(C_131,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_60,c_374])).

tff(c_538,plain,(
    ! [A_130,A_7] :
      ( k7_partfun1(A_130,'#skF_4',A_7) = k1_funct_1('#skF_4',A_7)
      | ~ v5_relat_1('#skF_4',A_130)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_7,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_535])).

tff(c_542,plain,(
    ! [A_132,A_133] :
      ( k7_partfun1(A_132,'#skF_4',A_133) = k1_funct_1('#skF_4',A_133)
      | ~ v5_relat_1('#skF_4',A_132)
      | ~ m1_subset_1(A_133,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_538])).

tff(c_546,plain,(
    ! [A_134] :
      ( k7_partfun1('#skF_3','#skF_4',A_134) = k1_funct_1('#skF_4',A_134)
      | ~ m1_subset_1(A_134,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_192,c_542])).

tff(c_549,plain,(
    k7_partfun1('#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_546])).

tff(c_553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_461,c_549])).

tff(c_554,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_10,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_105,plain,(
    ! [B_57,A_58] :
      ( v1_xboole_0(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_113,plain,(
    ! [A_3] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_10,c_105])).

tff(c_114,plain,(
    ! [A_3] : ~ v1_xboole_0(A_3) ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_2,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_2])).

tff(c_118,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_596,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_118])).

tff(c_603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_596])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.42  
% 2.81/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.42  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.81/1.42  
% 2.81/1.42  %Foreground sorts:
% 2.81/1.42  
% 2.81/1.42  
% 2.81/1.42  %Background operators:
% 2.81/1.42  
% 2.81/1.42  
% 2.81/1.42  %Foreground operators:
% 2.81/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.81/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.42  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.81/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.81/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.81/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.81/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.81/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.81/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.81/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.81/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.81/1.42  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.81/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.81/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.42  
% 2.81/1.44  tff(f_159, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 2.81/1.44  tff(f_139, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.81/1.44  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.81/1.44  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.81/1.44  tff(f_63, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.81/1.44  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.81/1.44  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.81/1.44  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.81/1.44  tff(f_126, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 2.81/1.44  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.81/1.44  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.81/1.44  tff(f_27, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.81/1.44  tff(c_62, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.81/1.44  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.81/1.44  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.81/1.44  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.81/1.44  tff(c_64, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.81/1.44  tff(c_54, plain, (m1_subset_1('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.81/1.44  tff(c_424, plain, (![A_119, B_120, C_121, D_122]: (k3_funct_2(A_119, B_120, C_121, D_122)=k1_funct_1(C_121, D_122) | ~m1_subset_1(D_122, A_119) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~v1_funct_2(C_121, A_119, B_120) | ~v1_funct_1(C_121) | v1_xboole_0(A_119))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.81/1.44  tff(c_432, plain, (![B_120, C_121]: (k3_funct_2('#skF_2', B_120, C_121, '#skF_5')=k1_funct_1(C_121, '#skF_5') | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_120))) | ~v1_funct_2(C_121, '#skF_2', B_120) | ~v1_funct_1(C_121) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_424])).
% 2.81/1.44  tff(c_443, plain, (![B_124, C_125]: (k3_funct_2('#skF_2', B_124, C_125, '#skF_5')=k1_funct_1(C_125, '#skF_5') | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_124))) | ~v1_funct_2(C_125, '#skF_2', B_124) | ~v1_funct_1(C_125))), inference(negUnitSimplification, [status(thm)], [c_64, c_432])).
% 2.81/1.44  tff(c_446, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_443])).
% 2.81/1.44  tff(c_457, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_446])).
% 2.81/1.44  tff(c_52, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k7_partfun1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.81/1.44  tff(c_461, plain, (k7_partfun1('#skF_3', '#skF_4', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_457, c_52])).
% 2.81/1.44  tff(c_178, plain, (![C_72, B_73, A_74]: (v5_relat_1(C_72, B_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.81/1.44  tff(c_192, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_178])).
% 2.81/1.44  tff(c_14, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.81/1.44  tff(c_20, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.81/1.44  tff(c_124, plain, (![B_59, A_60]: (v1_relat_1(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.81/1.44  tff(c_127, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_124])).
% 2.81/1.44  tff(c_133, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_127])).
% 2.81/1.44  tff(c_229, plain, (![A_87, B_88, C_89]: (k1_relset_1(A_87, B_88, C_89)=k1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.81/1.44  tff(c_243, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_229])).
% 2.81/1.44  tff(c_319, plain, (![B_105, A_106, C_107]: (k1_xboole_0=B_105 | k1_relset_1(A_106, B_105, C_107)=A_106 | ~v1_funct_2(C_107, A_106, B_105) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.81/1.44  tff(c_322, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_319])).
% 2.81/1.44  tff(c_335, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_243, c_322])).
% 2.81/1.44  tff(c_339, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_335])).
% 2.81/1.44  tff(c_372, plain, (![A_111, B_112, C_113]: (k7_partfun1(A_111, B_112, C_113)=k1_funct_1(B_112, C_113) | ~r2_hidden(C_113, k1_relat_1(B_112)) | ~v1_funct_1(B_112) | ~v5_relat_1(B_112, A_111) | ~v1_relat_1(B_112))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.81/1.44  tff(c_374, plain, (![A_111, C_113]: (k7_partfun1(A_111, '#skF_4', C_113)=k1_funct_1('#skF_4', C_113) | ~r2_hidden(C_113, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_111) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_339, c_372])).
% 2.81/1.44  tff(c_535, plain, (![A_130, C_131]: (k7_partfun1(A_130, '#skF_4', C_131)=k1_funct_1('#skF_4', C_131) | ~r2_hidden(C_131, '#skF_2') | ~v5_relat_1('#skF_4', A_130))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_60, c_374])).
% 2.81/1.44  tff(c_538, plain, (![A_130, A_7]: (k7_partfun1(A_130, '#skF_4', A_7)=k1_funct_1('#skF_4', A_7) | ~v5_relat_1('#skF_4', A_130) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_7, '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_535])).
% 2.81/1.44  tff(c_542, plain, (![A_132, A_133]: (k7_partfun1(A_132, '#skF_4', A_133)=k1_funct_1('#skF_4', A_133) | ~v5_relat_1('#skF_4', A_132) | ~m1_subset_1(A_133, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_64, c_538])).
% 2.81/1.44  tff(c_546, plain, (![A_134]: (k7_partfun1('#skF_3', '#skF_4', A_134)=k1_funct_1('#skF_4', A_134) | ~m1_subset_1(A_134, '#skF_2'))), inference(resolution, [status(thm)], [c_192, c_542])).
% 2.81/1.44  tff(c_549, plain, (k7_partfun1('#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_546])).
% 2.81/1.44  tff(c_553, plain, $false, inference(negUnitSimplification, [status(thm)], [c_461, c_549])).
% 2.81/1.44  tff(c_554, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_335])).
% 2.81/1.44  tff(c_10, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.81/1.44  tff(c_105, plain, (![B_57, A_58]: (v1_xboole_0(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.81/1.44  tff(c_113, plain, (![A_3]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_10, c_105])).
% 2.81/1.44  tff(c_114, plain, (![A_3]: (~v1_xboole_0(A_3))), inference(splitLeft, [status(thm)], [c_113])).
% 2.81/1.44  tff(c_2, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.81/1.44  tff(c_117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_2])).
% 2.81/1.44  tff(c_118, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_113])).
% 2.81/1.44  tff(c_596, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_554, c_118])).
% 2.81/1.44  tff(c_603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_596])).
% 2.81/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.44  
% 2.81/1.44  Inference rules
% 2.81/1.44  ----------------------
% 2.81/1.44  #Ref     : 0
% 2.81/1.44  #Sup     : 96
% 2.81/1.44  #Fact    : 0
% 2.81/1.44  #Define  : 0
% 2.81/1.44  #Split   : 7
% 2.81/1.44  #Chain   : 0
% 2.81/1.44  #Close   : 0
% 2.81/1.44  
% 2.81/1.44  Ordering : KBO
% 2.81/1.44  
% 2.81/1.44  Simplification rules
% 2.81/1.44  ----------------------
% 2.81/1.44  #Subsume      : 10
% 2.81/1.44  #Demod        : 155
% 2.81/1.44  #Tautology    : 45
% 2.81/1.44  #SimpNegUnit  : 13
% 2.81/1.44  #BackRed      : 58
% 2.81/1.44  
% 2.81/1.44  #Partial instantiations: 0
% 2.81/1.44  #Strategies tried      : 1
% 2.81/1.44  
% 2.81/1.44  Timing (in seconds)
% 2.81/1.44  ----------------------
% 2.81/1.44  Preprocessing        : 0.35
% 2.81/1.44  Parsing              : 0.19
% 2.81/1.44  CNF conversion       : 0.02
% 2.81/1.44  Main loop            : 0.33
% 2.81/1.44  Inferencing          : 0.10
% 2.81/1.44  Reduction            : 0.11
% 2.81/1.44  Demodulation         : 0.08
% 2.81/1.44  BG Simplification    : 0.02
% 2.81/1.44  Subsumption          : 0.06
% 2.81/1.44  Abstraction          : 0.01
% 2.81/1.44  MUC search           : 0.00
% 2.81/1.44  Cooper               : 0.00
% 2.81/1.44  Total                : 0.71
% 2.81/1.44  Index Insertion      : 0.00
% 2.81/1.44  Index Deletion       : 0.00
% 2.81/1.44  Index Matching       : 0.00
% 2.81/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
