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
% DateTime   : Thu Dec  3 10:16:58 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 669 expanded)
%              Number of leaves         :   29 ( 223 expanded)
%              Depth                    :   15
%              Number of atoms          :  310 (2408 expanded)
%              Number of equality atoms :   81 ( 858 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ( B = k1_xboole_0
               => A = k1_xboole_0 )
             => ( r1_partfun1(C,D)
              <=> ! [E] :
                    ( r2_hidden(E,k1_relset_1(A,B,C))
                   => k1_funct_1(C,E) = k1_funct_1(D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_2)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
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

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
           => ( r1_partfun1(A,B)
            <=> ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).

tff(c_44,plain,
    ( r2_hidden('#skF_6',k1_relset_1('#skF_2','#skF_3','#skF_4'))
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_63,plain,(
    ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_69,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_81,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_69])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_82,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_69])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_102,plain,(
    ! [A_46,B_47,C_48] :
      ( k1_relset_1(A_46,B_47,C_48) = k1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_114,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_102])).

tff(c_126,plain,(
    ! [A_50,B_51,C_52] :
      ( m1_subset_1(k1_relset_1(A_50,B_51,C_52),k1_zfmisc_1(A_50))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_143,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_126])).

tff(c_150,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_143])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_158,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_150,c_2])).

tff(c_30,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_53,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_34,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_115,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_102])).

tff(c_302,plain,(
    ! [B_85,A_86,C_87] :
      ( k1_xboole_0 = B_85
      | k1_relset_1(A_86,B_85,C_87) = A_86
      | ~ v1_funct_2(C_87,A_86,B_85)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_86,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_316,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_302])).

tff(c_324,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_115,c_316])).

tff(c_325,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_324])).

tff(c_392,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_1'(A_94,B_95),k1_relat_1(A_94))
      | r1_partfun1(A_94,B_95)
      | ~ r1_tarski(k1_relat_1(A_94),k1_relat_1(B_95))
      | ~ v1_funct_1(B_95)
      | ~ v1_relat_1(B_95)
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_52,plain,(
    ! [E_32] :
      ( r1_partfun1('#skF_4','#skF_5')
      | k1_funct_1('#skF_5',E_32) = k1_funct_1('#skF_4',E_32)
      | ~ r2_hidden(E_32,k1_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_99,plain,(
    ! [E_32] :
      ( k1_funct_1('#skF_5',E_32) = k1_funct_1('#skF_4',E_32)
      | ~ r2_hidden(E_32,k1_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_52])).

tff(c_116,plain,(
    ! [E_32] :
      ( k1_funct_1('#skF_5',E_32) = k1_funct_1('#skF_4',E_32)
      | ~ r2_hidden(E_32,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_99])).

tff(c_396,plain,(
    ! [B_95] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_95)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_95))
      | r1_partfun1('#skF_4',B_95)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_95))
      | ~ v1_funct_1(B_95)
      | ~ v1_relat_1(B_95)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_392,c_116])).

tff(c_447,plain,(
    ! [B_101] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_101)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_101))
      | r1_partfun1('#skF_4',B_101)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_101))
      | ~ v1_funct_1(B_101)
      | ~ v1_relat_1(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_396])).

tff(c_450,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_447])).

tff(c_452,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_36,c_158,c_450])).

tff(c_453,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_452])).

tff(c_481,plain,(
    ! [B_120,A_121] :
      ( k1_funct_1(B_120,'#skF_1'(A_121,B_120)) != k1_funct_1(A_121,'#skF_1'(A_121,B_120))
      | r1_partfun1(A_121,B_120)
      | ~ r1_tarski(k1_relat_1(A_121),k1_relat_1(B_120))
      | ~ v1_funct_1(B_120)
      | ~ v1_relat_1(B_120)
      | ~ v1_funct_1(A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_483,plain,
    ( r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_453,c_481])).

tff(c_486,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_82,c_36,c_158,c_325,c_483])).

tff(c_488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_486])).

tff(c_490,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,
    ( k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_492,plain,(
    k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_42])).

tff(c_498,plain,(
    ! [C_124,A_125,B_126] :
      ( v1_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_511,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_498])).

tff(c_529,plain,(
    ! [A_132,B_133,C_134] :
      ( k1_relset_1(A_132,B_133,C_134) = k1_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_541,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_529])).

tff(c_564,plain,(
    ! [A_138,B_139,C_140] :
      ( m1_subset_1(k1_relset_1(A_138,B_139,C_140),k1_zfmisc_1(A_138))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_581,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_564])).

tff(c_588,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_581])).

tff(c_607,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_588,c_2])).

tff(c_542,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_529])).

tff(c_747,plain,(
    ! [B_173,A_174,C_175] :
      ( k1_xboole_0 = B_173
      | k1_relset_1(A_174,B_173,C_175) = A_174
      | ~ v1_funct_2(C_175,A_174,B_173)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_174,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_761,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_747])).

tff(c_769,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_542,c_761])).

tff(c_770,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_769])).

tff(c_510,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_498])).

tff(c_489,plain,(
    r2_hidden('#skF_6',k1_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_543,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_489])).

tff(c_881,plain,(
    ! [B_189,C_190,A_191] :
      ( k1_funct_1(B_189,C_190) = k1_funct_1(A_191,C_190)
      | ~ r2_hidden(C_190,k1_relat_1(A_191))
      | ~ r1_partfun1(A_191,B_189)
      | ~ r1_tarski(k1_relat_1(A_191),k1_relat_1(B_189))
      | ~ v1_funct_1(B_189)
      | ~ v1_relat_1(B_189)
      | ~ v1_funct_1(A_191)
      | ~ v1_relat_1(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_887,plain,(
    ! [B_189] :
      ( k1_funct_1(B_189,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_189)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_189))
      | ~ v1_funct_1(B_189)
      | ~ v1_relat_1(B_189)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_543,c_881])).

tff(c_894,plain,(
    ! [B_192] :
      ( k1_funct_1(B_192,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_192)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_192))
      | ~ v1_funct_1(B_192)
      | ~ v1_relat_1(B_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_40,c_887])).

tff(c_897,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_770,c_894])).

tff(c_899,plain,(
    k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_36,c_607,c_490,c_897])).

tff(c_901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_492,c_899])).

tff(c_903,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_902,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_908,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_903,c_902])).

tff(c_929,plain,
    ( r2_hidden('#skF_6',k1_relset_1('#skF_3','#skF_3','#skF_4'))
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_908,c_44])).

tff(c_930,plain,(
    ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_929])).

tff(c_919,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_908,c_38])).

tff(c_936,plain,(
    ! [C_197,A_198,B_199] :
      ( v1_relat_1(C_197)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_948,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_919,c_936])).

tff(c_918,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_908,c_32])).

tff(c_949,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_918,c_936])).

tff(c_971,plain,(
    ! [A_206,B_207,C_208] :
      ( k1_relset_1(A_206,B_207,C_208) = k1_relat_1(C_208)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_983,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_919,c_971])).

tff(c_995,plain,(
    ! [A_210,B_211,C_212] :
      ( m1_subset_1(k1_relset_1(A_210,B_211,C_212),k1_zfmisc_1(A_210))
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1012,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_983,c_995])).

tff(c_1019,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_919,c_1012])).

tff(c_1027,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1019,c_2])).

tff(c_913,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_908,c_34])).

tff(c_984,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_918,c_971])).

tff(c_20,plain,(
    ! [B_13,C_14] :
      ( k1_relset_1(k1_xboole_0,B_13,C_14) = k1_xboole_0
      | ~ v1_funct_2(C_14,k1_xboole_0,B_13)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1103,plain,(
    ! [B_224,C_225] :
      ( k1_relset_1('#skF_3',B_224,C_225) = '#skF_3'
      | ~ v1_funct_2(C_225,'#skF_3',B_224)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_224))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_903,c_903,c_903,c_903,c_20])).

tff(c_1117,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_918,c_1103])).

tff(c_1124,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_913,c_984,c_1117])).

tff(c_1375,plain,(
    ! [A_258,B_259] :
      ( r2_hidden('#skF_1'(A_258,B_259),k1_relat_1(A_258))
      | r1_partfun1(A_258,B_259)
      | ~ r1_tarski(k1_relat_1(A_258),k1_relat_1(B_259))
      | ~ v1_funct_1(B_259)
      | ~ v1_relat_1(B_259)
      | ~ v1_funct_1(A_258)
      | ~ v1_relat_1(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_967,plain,(
    ! [E_32] :
      ( r1_partfun1('#skF_4','#skF_5')
      | k1_funct_1('#skF_5',E_32) = k1_funct_1('#skF_4',E_32)
      | ~ r2_hidden(E_32,k1_relset_1('#skF_3','#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_908,c_52])).

tff(c_968,plain,(
    ! [E_32] :
      ( k1_funct_1('#skF_5',E_32) = k1_funct_1('#skF_4',E_32)
      | ~ r2_hidden(E_32,k1_relset_1('#skF_3','#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_930,c_967])).

tff(c_985,plain,(
    ! [E_32] :
      ( k1_funct_1('#skF_5',E_32) = k1_funct_1('#skF_4',E_32)
      | ~ r2_hidden(E_32,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_968])).

tff(c_1379,plain,(
    ! [B_259] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_259)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_259))
      | r1_partfun1('#skF_4',B_259)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_259))
      | ~ v1_funct_1(B_259)
      | ~ v1_relat_1(B_259)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1375,c_985])).

tff(c_1389,plain,(
    ! [B_261] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_261)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_261))
      | r1_partfun1('#skF_4',B_261)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_261))
      | ~ v1_funct_1(B_261)
      | ~ v1_relat_1(B_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_948,c_40,c_1379])).

tff(c_1392,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1124,c_1389])).

tff(c_1394,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_949,c_36,c_1027,c_1392])).

tff(c_1395,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_930,c_1394])).

tff(c_1403,plain,(
    ! [B_262,A_263] :
      ( k1_funct_1(B_262,'#skF_1'(A_263,B_262)) != k1_funct_1(A_263,'#skF_1'(A_263,B_262))
      | r1_partfun1(A_263,B_262)
      | ~ r1_tarski(k1_relat_1(A_263),k1_relat_1(B_262))
      | ~ v1_funct_1(B_262)
      | ~ v1_relat_1(B_262)
      | ~ v1_funct_1(A_263)
      | ~ v1_relat_1(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1405,plain,
    ( r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1395,c_1403])).

tff(c_1408,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_948,c_40,c_949,c_36,c_1027,c_1124,c_1405])).

tff(c_1410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_930,c_1408])).

tff(c_1412,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_929])).

tff(c_1433,plain,(
    k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1412,c_42])).

tff(c_1418,plain,(
    ! [C_266,A_267,B_268] :
      ( v1_relat_1(C_266)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_267,B_268))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1431,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_918,c_1418])).

tff(c_1453,plain,(
    ! [A_274,B_275,C_276] :
      ( k1_relset_1(A_274,B_275,C_276) = k1_relat_1(C_276)
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(A_274,B_275))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1465,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_919,c_1453])).

tff(c_1472,plain,(
    ! [A_277,B_278,C_279] :
      ( m1_subset_1(k1_relset_1(A_277,B_278,C_279),k1_zfmisc_1(A_277))
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(A_277,B_278))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1486,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1465,c_1472])).

tff(c_1491,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_919,c_1486])).

tff(c_1495,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1491,c_2])).

tff(c_1466,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_918,c_1453])).

tff(c_1608,plain,(
    ! [B_297,C_298] :
      ( k1_relset_1('#skF_3',B_297,C_298) = '#skF_3'
      | ~ v1_funct_2(C_298,'#skF_3',B_297)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_297))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_903,c_903,c_903,c_903,c_20])).

tff(c_1622,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_918,c_1608])).

tff(c_1629,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_913,c_1466,c_1622])).

tff(c_1430,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_919,c_1418])).

tff(c_1411,plain,(
    r2_hidden('#skF_6',k1_relset_1('#skF_3','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_929])).

tff(c_1467,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1465,c_1411])).

tff(c_1874,plain,(
    ! [B_332,C_333,A_334] :
      ( k1_funct_1(B_332,C_333) = k1_funct_1(A_334,C_333)
      | ~ r2_hidden(C_333,k1_relat_1(A_334))
      | ~ r1_partfun1(A_334,B_332)
      | ~ r1_tarski(k1_relat_1(A_334),k1_relat_1(B_332))
      | ~ v1_funct_1(B_332)
      | ~ v1_relat_1(B_332)
      | ~ v1_funct_1(A_334)
      | ~ v1_relat_1(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1880,plain,(
    ! [B_332] :
      ( k1_funct_1(B_332,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_332)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_332))
      | ~ v1_funct_1(B_332)
      | ~ v1_relat_1(B_332)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1467,c_1874])).

tff(c_1887,plain,(
    ! [B_335] :
      ( k1_funct_1(B_335,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_335)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_335))
      | ~ v1_funct_1(B_335)
      | ~ v1_relat_1(B_335) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1430,c_40,c_1880])).

tff(c_1890,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1629,c_1887])).

tff(c_1892,plain,(
    k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1431,c_36,c_1495,c_1412,c_1890])).

tff(c_1894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1433,c_1892])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:30:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.88/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.67  
% 3.88/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.67  %$ v1_funct_2 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.88/1.67  
% 3.88/1.67  %Foreground sorts:
% 3.88/1.67  
% 3.88/1.67  
% 3.88/1.67  %Background operators:
% 3.88/1.67  
% 3.88/1.67  
% 3.88/1.67  %Foreground operators:
% 3.88/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.88/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.88/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.88/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.88/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.88/1.67  tff('#skF_6', type, '#skF_6': $i).
% 3.88/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.88/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.88/1.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.88/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.88/1.67  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.88/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.88/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.88/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.88/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.88/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.88/1.67  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 3.88/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.88/1.67  
% 4.04/1.70  tff(f_100, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (r1_partfun1(C, D) <=> (![E]: (r2_hidden(E, k1_relset_1(A, B, C)) => (k1_funct_1(C, E) = k1_funct_1(D, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_2)).
% 4.04/1.70  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.04/1.70  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.04/1.70  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.04/1.70  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.04/1.70  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.04/1.70  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) => (r1_partfun1(A, B) <=> (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_partfun1)).
% 4.04/1.70  tff(c_44, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.04/1.70  tff(c_63, plain, (~r1_partfun1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_44])).
% 4.04/1.70  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.04/1.70  tff(c_69, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.04/1.70  tff(c_81, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_69])).
% 4.04/1.70  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.04/1.70  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.04/1.70  tff(c_82, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_69])).
% 4.04/1.70  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.04/1.70  tff(c_102, plain, (![A_46, B_47, C_48]: (k1_relset_1(A_46, B_47, C_48)=k1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.04/1.70  tff(c_114, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_102])).
% 4.04/1.70  tff(c_126, plain, (![A_50, B_51, C_52]: (m1_subset_1(k1_relset_1(A_50, B_51, C_52), k1_zfmisc_1(A_50)) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.04/1.70  tff(c_143, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_114, c_126])).
% 4.04/1.70  tff(c_150, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_143])).
% 4.04/1.70  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.04/1.70  tff(c_158, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_150, c_2])).
% 4.04/1.70  tff(c_30, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.04/1.70  tff(c_53, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_30])).
% 4.04/1.70  tff(c_34, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.04/1.70  tff(c_115, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_102])).
% 4.04/1.70  tff(c_302, plain, (![B_85, A_86, C_87]: (k1_xboole_0=B_85 | k1_relset_1(A_86, B_85, C_87)=A_86 | ~v1_funct_2(C_87, A_86, B_85) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_86, B_85))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.04/1.70  tff(c_316, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_302])).
% 4.04/1.70  tff(c_324, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_115, c_316])).
% 4.04/1.70  tff(c_325, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_53, c_324])).
% 4.04/1.70  tff(c_392, plain, (![A_94, B_95]: (r2_hidden('#skF_1'(A_94, B_95), k1_relat_1(A_94)) | r1_partfun1(A_94, B_95) | ~r1_tarski(k1_relat_1(A_94), k1_relat_1(B_95)) | ~v1_funct_1(B_95) | ~v1_relat_1(B_95) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.04/1.70  tff(c_52, plain, (![E_32]: (r1_partfun1('#skF_4', '#skF_5') | k1_funct_1('#skF_5', E_32)=k1_funct_1('#skF_4', E_32) | ~r2_hidden(E_32, k1_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.04/1.70  tff(c_99, plain, (![E_32]: (k1_funct_1('#skF_5', E_32)=k1_funct_1('#skF_4', E_32) | ~r2_hidden(E_32, k1_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_63, c_52])).
% 4.04/1.70  tff(c_116, plain, (![E_32]: (k1_funct_1('#skF_5', E_32)=k1_funct_1('#skF_4', E_32) | ~r2_hidden(E_32, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_99])).
% 4.04/1.70  tff(c_396, plain, (![B_95]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_95))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_95)) | r1_partfun1('#skF_4', B_95) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_95)) | ~v1_funct_1(B_95) | ~v1_relat_1(B_95) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_392, c_116])).
% 4.04/1.70  tff(c_447, plain, (![B_101]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_101))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_101)) | r1_partfun1('#skF_4', B_101) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_101)) | ~v1_funct_1(B_101) | ~v1_relat_1(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_40, c_396])).
% 4.04/1.70  tff(c_450, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_325, c_447])).
% 4.04/1.70  tff(c_452, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_36, c_158, c_450])).
% 4.04/1.70  tff(c_453, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_63, c_452])).
% 4.04/1.70  tff(c_481, plain, (![B_120, A_121]: (k1_funct_1(B_120, '#skF_1'(A_121, B_120))!=k1_funct_1(A_121, '#skF_1'(A_121, B_120)) | r1_partfun1(A_121, B_120) | ~r1_tarski(k1_relat_1(A_121), k1_relat_1(B_120)) | ~v1_funct_1(B_120) | ~v1_relat_1(B_120) | ~v1_funct_1(A_121) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.04/1.70  tff(c_483, plain, (r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_453, c_481])).
% 4.04/1.70  tff(c_486, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_40, c_82, c_36, c_158, c_325, c_483])).
% 4.04/1.70  tff(c_488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_486])).
% 4.04/1.70  tff(c_490, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_44])).
% 4.04/1.70  tff(c_42, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.04/1.70  tff(c_492, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_490, c_42])).
% 4.04/1.70  tff(c_498, plain, (![C_124, A_125, B_126]: (v1_relat_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.04/1.70  tff(c_511, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_498])).
% 4.04/1.70  tff(c_529, plain, (![A_132, B_133, C_134]: (k1_relset_1(A_132, B_133, C_134)=k1_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.04/1.70  tff(c_541, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_529])).
% 4.04/1.70  tff(c_564, plain, (![A_138, B_139, C_140]: (m1_subset_1(k1_relset_1(A_138, B_139, C_140), k1_zfmisc_1(A_138)) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.04/1.70  tff(c_581, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_541, c_564])).
% 4.04/1.70  tff(c_588, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_581])).
% 4.04/1.70  tff(c_607, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_588, c_2])).
% 4.04/1.70  tff(c_542, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_529])).
% 4.04/1.70  tff(c_747, plain, (![B_173, A_174, C_175]: (k1_xboole_0=B_173 | k1_relset_1(A_174, B_173, C_175)=A_174 | ~v1_funct_2(C_175, A_174, B_173) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_174, B_173))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.04/1.70  tff(c_761, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_747])).
% 4.04/1.70  tff(c_769, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_542, c_761])).
% 4.04/1.70  tff(c_770, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_53, c_769])).
% 4.04/1.70  tff(c_510, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_498])).
% 4.04/1.70  tff(c_489, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_44])).
% 4.04/1.70  tff(c_543, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_541, c_489])).
% 4.04/1.70  tff(c_881, plain, (![B_189, C_190, A_191]: (k1_funct_1(B_189, C_190)=k1_funct_1(A_191, C_190) | ~r2_hidden(C_190, k1_relat_1(A_191)) | ~r1_partfun1(A_191, B_189) | ~r1_tarski(k1_relat_1(A_191), k1_relat_1(B_189)) | ~v1_funct_1(B_189) | ~v1_relat_1(B_189) | ~v1_funct_1(A_191) | ~v1_relat_1(A_191))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.04/1.70  tff(c_887, plain, (![B_189]: (k1_funct_1(B_189, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_189) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_189)) | ~v1_funct_1(B_189) | ~v1_relat_1(B_189) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_543, c_881])).
% 4.04/1.70  tff(c_894, plain, (![B_192]: (k1_funct_1(B_192, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_192) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_192)) | ~v1_funct_1(B_192) | ~v1_relat_1(B_192))), inference(demodulation, [status(thm), theory('equality')], [c_510, c_40, c_887])).
% 4.04/1.70  tff(c_897, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_770, c_894])).
% 4.04/1.70  tff(c_899, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_511, c_36, c_607, c_490, c_897])).
% 4.04/1.70  tff(c_901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_492, c_899])).
% 4.04/1.70  tff(c_903, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 4.04/1.70  tff(c_902, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 4.04/1.70  tff(c_908, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_903, c_902])).
% 4.04/1.70  tff(c_929, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_3', '#skF_3', '#skF_4')) | ~r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_908, c_44])).
% 4.04/1.70  tff(c_930, plain, (~r1_partfun1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_929])).
% 4.04/1.70  tff(c_919, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_908, c_38])).
% 4.04/1.70  tff(c_936, plain, (![C_197, A_198, B_199]: (v1_relat_1(C_197) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.04/1.70  tff(c_948, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_919, c_936])).
% 4.04/1.70  tff(c_918, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_908, c_32])).
% 4.04/1.70  tff(c_949, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_918, c_936])).
% 4.04/1.70  tff(c_971, plain, (![A_206, B_207, C_208]: (k1_relset_1(A_206, B_207, C_208)=k1_relat_1(C_208) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.04/1.70  tff(c_983, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_919, c_971])).
% 4.04/1.70  tff(c_995, plain, (![A_210, B_211, C_212]: (m1_subset_1(k1_relset_1(A_210, B_211, C_212), k1_zfmisc_1(A_210)) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.04/1.70  tff(c_1012, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_983, c_995])).
% 4.04/1.70  tff(c_1019, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_919, c_1012])).
% 4.04/1.70  tff(c_1027, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1019, c_2])).
% 4.04/1.70  tff(c_913, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_908, c_34])).
% 4.04/1.70  tff(c_984, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_918, c_971])).
% 4.04/1.70  tff(c_20, plain, (![B_13, C_14]: (k1_relset_1(k1_xboole_0, B_13, C_14)=k1_xboole_0 | ~v1_funct_2(C_14, k1_xboole_0, B_13) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_13))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.04/1.70  tff(c_1103, plain, (![B_224, C_225]: (k1_relset_1('#skF_3', B_224, C_225)='#skF_3' | ~v1_funct_2(C_225, '#skF_3', B_224) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_224))))), inference(demodulation, [status(thm), theory('equality')], [c_903, c_903, c_903, c_903, c_20])).
% 4.04/1.70  tff(c_1117, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_918, c_1103])).
% 4.04/1.70  tff(c_1124, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_913, c_984, c_1117])).
% 4.04/1.70  tff(c_1375, plain, (![A_258, B_259]: (r2_hidden('#skF_1'(A_258, B_259), k1_relat_1(A_258)) | r1_partfun1(A_258, B_259) | ~r1_tarski(k1_relat_1(A_258), k1_relat_1(B_259)) | ~v1_funct_1(B_259) | ~v1_relat_1(B_259) | ~v1_funct_1(A_258) | ~v1_relat_1(A_258))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.04/1.70  tff(c_967, plain, (![E_32]: (r1_partfun1('#skF_4', '#skF_5') | k1_funct_1('#skF_5', E_32)=k1_funct_1('#skF_4', E_32) | ~r2_hidden(E_32, k1_relset_1('#skF_3', '#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_908, c_52])).
% 4.04/1.70  tff(c_968, plain, (![E_32]: (k1_funct_1('#skF_5', E_32)=k1_funct_1('#skF_4', E_32) | ~r2_hidden(E_32, k1_relset_1('#skF_3', '#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_930, c_967])).
% 4.04/1.70  tff(c_985, plain, (![E_32]: (k1_funct_1('#skF_5', E_32)=k1_funct_1('#skF_4', E_32) | ~r2_hidden(E_32, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_983, c_968])).
% 4.04/1.70  tff(c_1379, plain, (![B_259]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_259))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_259)) | r1_partfun1('#skF_4', B_259) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_259)) | ~v1_funct_1(B_259) | ~v1_relat_1(B_259) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1375, c_985])).
% 4.04/1.70  tff(c_1389, plain, (![B_261]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_261))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_261)) | r1_partfun1('#skF_4', B_261) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_261)) | ~v1_funct_1(B_261) | ~v1_relat_1(B_261))), inference(demodulation, [status(thm), theory('equality')], [c_948, c_40, c_1379])).
% 4.04/1.70  tff(c_1392, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1124, c_1389])).
% 4.04/1.70  tff(c_1394, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_949, c_36, c_1027, c_1392])).
% 4.04/1.70  tff(c_1395, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_930, c_1394])).
% 4.04/1.70  tff(c_1403, plain, (![B_262, A_263]: (k1_funct_1(B_262, '#skF_1'(A_263, B_262))!=k1_funct_1(A_263, '#skF_1'(A_263, B_262)) | r1_partfun1(A_263, B_262) | ~r1_tarski(k1_relat_1(A_263), k1_relat_1(B_262)) | ~v1_funct_1(B_262) | ~v1_relat_1(B_262) | ~v1_funct_1(A_263) | ~v1_relat_1(A_263))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.04/1.70  tff(c_1405, plain, (r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1395, c_1403])).
% 4.04/1.70  tff(c_1408, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_948, c_40, c_949, c_36, c_1027, c_1124, c_1405])).
% 4.04/1.70  tff(c_1410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_930, c_1408])).
% 4.04/1.70  tff(c_1412, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_929])).
% 4.04/1.70  tff(c_1433, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1412, c_42])).
% 4.04/1.70  tff(c_1418, plain, (![C_266, A_267, B_268]: (v1_relat_1(C_266) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(A_267, B_268))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.04/1.70  tff(c_1431, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_918, c_1418])).
% 4.04/1.70  tff(c_1453, plain, (![A_274, B_275, C_276]: (k1_relset_1(A_274, B_275, C_276)=k1_relat_1(C_276) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(A_274, B_275))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.04/1.70  tff(c_1465, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_919, c_1453])).
% 4.04/1.70  tff(c_1472, plain, (![A_277, B_278, C_279]: (m1_subset_1(k1_relset_1(A_277, B_278, C_279), k1_zfmisc_1(A_277)) | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(A_277, B_278))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.04/1.70  tff(c_1486, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1465, c_1472])).
% 4.04/1.70  tff(c_1491, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_919, c_1486])).
% 4.04/1.70  tff(c_1495, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1491, c_2])).
% 4.04/1.70  tff(c_1466, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_918, c_1453])).
% 4.04/1.70  tff(c_1608, plain, (![B_297, C_298]: (k1_relset_1('#skF_3', B_297, C_298)='#skF_3' | ~v1_funct_2(C_298, '#skF_3', B_297) | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_297))))), inference(demodulation, [status(thm), theory('equality')], [c_903, c_903, c_903, c_903, c_20])).
% 4.04/1.70  tff(c_1622, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_918, c_1608])).
% 4.04/1.70  tff(c_1629, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_913, c_1466, c_1622])).
% 4.04/1.70  tff(c_1430, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_919, c_1418])).
% 4.04/1.70  tff(c_1411, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_3', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_929])).
% 4.04/1.70  tff(c_1467, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1465, c_1411])).
% 4.04/1.70  tff(c_1874, plain, (![B_332, C_333, A_334]: (k1_funct_1(B_332, C_333)=k1_funct_1(A_334, C_333) | ~r2_hidden(C_333, k1_relat_1(A_334)) | ~r1_partfun1(A_334, B_332) | ~r1_tarski(k1_relat_1(A_334), k1_relat_1(B_332)) | ~v1_funct_1(B_332) | ~v1_relat_1(B_332) | ~v1_funct_1(A_334) | ~v1_relat_1(A_334))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.04/1.70  tff(c_1880, plain, (![B_332]: (k1_funct_1(B_332, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_332) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_332)) | ~v1_funct_1(B_332) | ~v1_relat_1(B_332) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1467, c_1874])).
% 4.04/1.70  tff(c_1887, plain, (![B_335]: (k1_funct_1(B_335, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_335) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_335)) | ~v1_funct_1(B_335) | ~v1_relat_1(B_335))), inference(demodulation, [status(thm), theory('equality')], [c_1430, c_40, c_1880])).
% 4.04/1.70  tff(c_1890, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1629, c_1887])).
% 4.04/1.70  tff(c_1892, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1431, c_36, c_1495, c_1412, c_1890])).
% 4.04/1.70  tff(c_1894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1433, c_1892])).
% 4.04/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.70  
% 4.04/1.70  Inference rules
% 4.04/1.70  ----------------------
% 4.04/1.70  #Ref     : 3
% 4.04/1.70  #Sup     : 352
% 4.04/1.70  #Fact    : 0
% 4.04/1.70  #Define  : 0
% 4.04/1.70  #Split   : 7
% 4.04/1.70  #Chain   : 0
% 4.04/1.70  #Close   : 0
% 4.04/1.70  
% 4.04/1.70  Ordering : KBO
% 4.04/1.70  
% 4.04/1.70  Simplification rules
% 4.04/1.70  ----------------------
% 4.04/1.70  #Subsume      : 31
% 4.04/1.70  #Demod        : 303
% 4.04/1.70  #Tautology    : 123
% 4.04/1.70  #SimpNegUnit  : 38
% 4.04/1.70  #BackRed      : 18
% 4.04/1.70  
% 4.04/1.70  #Partial instantiations: 0
% 4.04/1.70  #Strategies tried      : 1
% 4.04/1.70  
% 4.04/1.70  Timing (in seconds)
% 4.04/1.70  ----------------------
% 4.04/1.70  Preprocessing        : 0.33
% 4.04/1.70  Parsing              : 0.17
% 4.04/1.70  CNF conversion       : 0.02
% 4.04/1.70  Main loop            : 0.57
% 4.04/1.70  Inferencing          : 0.23
% 4.04/1.70  Reduction            : 0.16
% 4.04/1.70  Demodulation         : 0.11
% 4.04/1.70  BG Simplification    : 0.03
% 4.04/1.70  Subsumption          : 0.09
% 4.04/1.70  Abstraction          : 0.03
% 4.04/1.70  MUC search           : 0.00
% 4.04/1.70  Cooper               : 0.00
% 4.04/1.70  Total                : 0.96
% 4.04/1.70  Index Insertion      : 0.00
% 4.04/1.70  Index Deletion       : 0.00
% 4.04/1.70  Index Matching       : 0.00
% 4.04/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
