%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:56 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 245 expanded)
%              Number of leaves         :   31 (  91 expanded)
%              Depth                    :   10
%              Number of atoms          :  153 ( 851 expanded)
%              Number of equality atoms :   27 ( 216 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_76,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_186,plain,(
    ! [A_70,B_71,C_72,D_73] :
      ( r2_relset_1(A_70,B_71,C_72,C_72)
      | ~ m1_subset_1(D_73,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_209,plain,(
    ! [C_74] :
      ( r2_relset_1('#skF_3','#skF_4',C_74,C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_46,c_186])).

tff(c_225,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_209])).

tff(c_36,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_48,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_283,plain,(
    ! [C_84,A_85,B_86] :
      ( v1_partfun1(C_84,A_85)
      | ~ v1_funct_2(C_84,A_85,B_86)
      | ~ v1_funct_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | v1_xboole_0(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_290,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_283])).

tff(c_311,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_290])).

tff(c_318,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_311])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_321,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_318,c_4])).

tff(c_325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_321])).

tff(c_326,plain,(
    v1_partfun1('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_311])).

tff(c_327,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_311])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_42,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_293,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_283])).

tff(c_314,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_293])).

tff(c_328,plain,(
    v1_partfun1('#skF_6','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_327,c_314])).

tff(c_38,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_363,plain,(
    ! [D_91,C_92,A_93,B_94] :
      ( D_91 = C_92
      | ~ r1_partfun1(C_92,D_91)
      | ~ v1_partfun1(D_91,A_93)
      | ~ v1_partfun1(C_92,A_93)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ v1_funct_1(D_91)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ v1_funct_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_365,plain,(
    ! [A_93,B_94] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_93)
      | ~ v1_partfun1('#skF_5',A_93)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_363])).

tff(c_368,plain,(
    ! [A_93,B_94] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_93)
      | ~ v1_partfun1('#skF_5',A_93)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_365])).

tff(c_493,plain,(
    ! [A_110,B_111] :
      ( ~ v1_partfun1('#skF_6',A_110)
      | ~ v1_partfun1('#skF_5',A_110)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_496,plain,
    ( ~ v1_partfun1('#skF_6','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_46,c_493])).

tff(c_506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_326,c_328,c_496])).

tff(c_507,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_34,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_512,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_34])).

tff(c_521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_512])).

tff(c_523,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_522,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_532,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_522])).

tff(c_14,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_524,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_14])).

tff(c_575,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_524])).

tff(c_767,plain,(
    ! [A_149,B_150,C_151,D_152] :
      ( r2_relset_1(A_149,B_150,C_151,C_151)
      | ~ m1_subset_1(D_152,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150)))
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_784,plain,(
    ! [A_153,B_154,C_155] :
      ( r2_relset_1(A_153,B_154,C_155,C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(resolution,[status(thm)],[c_575,c_767])).

tff(c_799,plain,(
    ! [A_153,B_154] : r2_relset_1(A_153,B_154,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_575,c_784])).

tff(c_22,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_2'(A_17),A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_580,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_2'(A_17),A_17)
      | A_17 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_22])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_527,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_2])).

tff(c_537,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_527])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_551,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_4',B_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_523,c_10])).

tff(c_578,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_532,c_46])).

tff(c_594,plain,(
    ! [C_119,B_120,A_121] :
      ( ~ v1_xboole_0(C_119)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(C_119))
      | ~ r2_hidden(A_121,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_598,plain,(
    ! [A_121] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_121,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_578,c_594])).

tff(c_629,plain,(
    ! [A_123] : ~ r2_hidden(A_123,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_598])).

tff(c_634,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_580,c_629])).

tff(c_579,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_532,c_40])).

tff(c_596,plain,(
    ! [A_121] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_121,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_579,c_594])).

tff(c_612,plain,(
    ! [A_122] : ~ r2_hidden(A_122,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_596])).

tff(c_617,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_580,c_612])).

tff(c_577,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_34])).

tff(c_620,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_577])).

tff(c_659,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_620])).

tff(c_803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_659])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n006.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 17:23:37 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.41  
% 2.79/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.42  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.79/1.42  
% 2.79/1.42  %Foreground sorts:
% 2.79/1.42  
% 2.79/1.42  
% 2.79/1.42  %Background operators:
% 2.79/1.42  
% 2.79/1.42  
% 2.79/1.42  %Foreground operators:
% 2.79/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.79/1.42  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.42  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.79/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.79/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.79/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.79/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.79/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.79/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.79/1.42  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.79/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.79/1.42  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.79/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.42  
% 2.79/1.43  tff(f_130, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_2)).
% 2.79/1.43  tff(f_60, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.79/1.43  tff(f_90, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.79/1.43  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.79/1.43  tff(f_107, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 2.79/1.43  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.79/1.43  tff(f_76, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.79/1.43  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.79/1.43  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.79/1.43  tff(f_54, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.79/1.43  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.79/1.43  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.79/1.43  tff(c_186, plain, (![A_70, B_71, C_72, D_73]: (r2_relset_1(A_70, B_71, C_72, C_72) | ~m1_subset_1(D_73, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.79/1.43  tff(c_209, plain, (![C_74]: (r2_relset_1('#skF_3', '#skF_4', C_74, C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_46, c_186])).
% 2.79/1.43  tff(c_225, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_40, c_209])).
% 2.79/1.43  tff(c_36, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.79/1.43  tff(c_66, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_36])).
% 2.79/1.43  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.79/1.43  tff(c_48, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.79/1.43  tff(c_283, plain, (![C_84, A_85, B_86]: (v1_partfun1(C_84, A_85) | ~v1_funct_2(C_84, A_85, B_86) | ~v1_funct_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | v1_xboole_0(B_86))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.79/1.43  tff(c_290, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_283])).
% 2.79/1.43  tff(c_311, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_290])).
% 2.79/1.43  tff(c_318, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_311])).
% 2.79/1.43  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.79/1.43  tff(c_321, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_318, c_4])).
% 2.79/1.43  tff(c_325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_321])).
% 2.79/1.43  tff(c_326, plain, (v1_partfun1('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_311])).
% 2.79/1.43  tff(c_327, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_311])).
% 2.79/1.43  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.79/1.43  tff(c_42, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.79/1.43  tff(c_293, plain, (v1_partfun1('#skF_6', '#skF_3') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_283])).
% 2.79/1.43  tff(c_314, plain, (v1_partfun1('#skF_6', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_293])).
% 2.79/1.43  tff(c_328, plain, (v1_partfun1('#skF_6', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_327, c_314])).
% 2.79/1.43  tff(c_38, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.79/1.43  tff(c_363, plain, (![D_91, C_92, A_93, B_94]: (D_91=C_92 | ~r1_partfun1(C_92, D_91) | ~v1_partfun1(D_91, A_93) | ~v1_partfun1(C_92, A_93) | ~m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~v1_funct_1(D_91) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~v1_funct_1(C_92))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.79/1.43  tff(c_365, plain, (![A_93, B_94]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_93) | ~v1_partfun1('#skF_5', A_93) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_363])).
% 3.08/1.43  tff(c_368, plain, (![A_93, B_94]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_93) | ~v1_partfun1('#skF_5', A_93) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_365])).
% 3.08/1.43  tff(c_493, plain, (![A_110, B_111]: (~v1_partfun1('#skF_6', A_110) | ~v1_partfun1('#skF_5', A_110) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(splitLeft, [status(thm)], [c_368])).
% 3.08/1.43  tff(c_496, plain, (~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_46, c_493])).
% 3.08/1.43  tff(c_506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_326, c_328, c_496])).
% 3.08/1.43  tff(c_507, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_368])).
% 3.08/1.43  tff(c_34, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.08/1.43  tff(c_512, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_507, c_34])).
% 3.08/1.43  tff(c_521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_225, c_512])).
% 3.08/1.43  tff(c_523, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 3.08/1.43  tff(c_522, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 3.08/1.43  tff(c_532, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_523, c_522])).
% 3.08/1.43  tff(c_14, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.08/1.43  tff(c_524, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_522, c_14])).
% 3.08/1.43  tff(c_575, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_532, c_524])).
% 3.08/1.43  tff(c_767, plain, (![A_149, B_150, C_151, D_152]: (r2_relset_1(A_149, B_150, C_151, C_151) | ~m1_subset_1(D_152, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.08/1.43  tff(c_784, plain, (![A_153, B_154, C_155]: (r2_relset_1(A_153, B_154, C_155, C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(resolution, [status(thm)], [c_575, c_767])).
% 3.08/1.43  tff(c_799, plain, (![A_153, B_154]: (r2_relset_1(A_153, B_154, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_575, c_784])).
% 3.08/1.43  tff(c_22, plain, (![A_17]: (r2_hidden('#skF_2'(A_17), A_17) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.08/1.43  tff(c_580, plain, (![A_17]: (r2_hidden('#skF_2'(A_17), A_17) | A_17='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_523, c_22])).
% 3.08/1.43  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.08/1.43  tff(c_527, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_522, c_2])).
% 3.08/1.43  tff(c_537, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_532, c_527])).
% 3.08/1.43  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.08/1.43  tff(c_551, plain, (![B_3]: (k2_zfmisc_1('#skF_4', B_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_523, c_523, c_10])).
% 3.08/1.43  tff(c_578, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_551, c_532, c_46])).
% 3.08/1.43  tff(c_594, plain, (![C_119, B_120, A_121]: (~v1_xboole_0(C_119) | ~m1_subset_1(B_120, k1_zfmisc_1(C_119)) | ~r2_hidden(A_121, B_120))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.08/1.43  tff(c_598, plain, (![A_121]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_121, '#skF_5'))), inference(resolution, [status(thm)], [c_578, c_594])).
% 3.08/1.43  tff(c_629, plain, (![A_123]: (~r2_hidden(A_123, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_537, c_598])).
% 3.08/1.43  tff(c_634, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_580, c_629])).
% 3.08/1.43  tff(c_579, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_551, c_532, c_40])).
% 3.08/1.43  tff(c_596, plain, (![A_121]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_121, '#skF_6'))), inference(resolution, [status(thm)], [c_579, c_594])).
% 3.08/1.43  tff(c_612, plain, (![A_122]: (~r2_hidden(A_122, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_537, c_596])).
% 3.08/1.43  tff(c_617, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_580, c_612])).
% 3.08/1.43  tff(c_577, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_532, c_34])).
% 3.08/1.43  tff(c_620, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_617, c_577])).
% 3.08/1.43  tff(c_659, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_634, c_620])).
% 3.08/1.43  tff(c_803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_799, c_659])).
% 3.08/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.43  
% 3.08/1.43  Inference rules
% 3.08/1.43  ----------------------
% 3.08/1.43  #Ref     : 0
% 3.08/1.43  #Sup     : 165
% 3.08/1.43  #Fact    : 0
% 3.08/1.43  #Define  : 0
% 3.08/1.43  #Split   : 6
% 3.08/1.43  #Chain   : 0
% 3.08/1.43  #Close   : 0
% 3.08/1.43  
% 3.08/1.43  Ordering : KBO
% 3.08/1.43  
% 3.08/1.43  Simplification rules
% 3.08/1.43  ----------------------
% 3.08/1.43  #Subsume      : 31
% 3.08/1.43  #Demod        : 116
% 3.08/1.43  #Tautology    : 71
% 3.08/1.43  #SimpNegUnit  : 2
% 3.08/1.43  #BackRed      : 26
% 3.08/1.43  
% 3.08/1.43  #Partial instantiations: 0
% 3.08/1.43  #Strategies tried      : 1
% 3.08/1.43  
% 3.08/1.43  Timing (in seconds)
% 3.08/1.43  ----------------------
% 3.08/1.44  Preprocessing        : 0.32
% 3.08/1.44  Parsing              : 0.17
% 3.08/1.44  CNF conversion       : 0.02
% 3.08/1.44  Main loop            : 0.36
% 3.08/1.44  Inferencing          : 0.12
% 3.08/1.44  Reduction            : 0.12
% 3.08/1.44  Demodulation         : 0.08
% 3.08/1.44  BG Simplification    : 0.02
% 3.08/1.44  Subsumption          : 0.06
% 3.08/1.44  Abstraction          : 0.01
% 3.08/1.44  MUC search           : 0.00
% 3.08/1.44  Cooper               : 0.00
% 3.08/1.44  Total                : 0.71
% 3.08/1.44  Index Insertion      : 0.00
% 3.08/1.44  Index Deletion       : 0.00
% 3.08/1.44  Index Matching       : 0.00
% 3.08/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
