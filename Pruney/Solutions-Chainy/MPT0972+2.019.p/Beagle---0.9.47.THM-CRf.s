%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:37 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 311 expanded)
%              Number of leaves         :   35 ( 120 expanded)
%              Depth                    :   11
%              Number of atoms          :  174 ( 920 expanded)
%              Number of equality atoms :   55 ( 215 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
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

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_118,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_195,plain,(
    ! [C_77,B_78,A_79] :
      ( v1_xboole_0(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(B_78,A_79)))
      | ~ v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_216,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_195])).

tff(c_222,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_434,plain,(
    ! [A_102,B_103,C_104,D_105] :
      ( r2_relset_1(A_102,B_103,C_104,C_104)
      | ~ m1_subset_1(D_105,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103)))
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_482,plain,(
    ! [C_108] :
      ( r2_relset_1('#skF_3','#skF_4',C_108,C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_56,c_434])).

tff(c_495,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_482])).

tff(c_132,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_152,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_132])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_64,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_223,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_244,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_223])).

tff(c_697,plain,(
    ! [B_134,A_135,C_136] :
      ( k1_xboole_0 = B_134
      | k1_relset_1(A_135,B_134,C_136) = A_135
      | ~ v1_funct_2(C_136,A_135,B_134)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_135,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_703,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_697])).

tff(c_722,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_244,c_703])).

tff(c_729,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_722])).

tff(c_153,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_132])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_58,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_245,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_223])).

tff(c_706,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_697])).

tff(c_725,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_245,c_706])).

tff(c_735,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_725])).

tff(c_811,plain,(
    ! [A_144,B_145] :
      ( r2_hidden('#skF_1'(A_144,B_145),k1_relat_1(A_144))
      | B_145 = A_144
      | k1_relat_1(B_145) != k1_relat_1(A_144)
      | ~ v1_funct_1(B_145)
      | ~ v1_relat_1(B_145)
      | ~ v1_funct_1(A_144)
      | ~ v1_relat_1(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_817,plain,(
    ! [B_145] :
      ( r2_hidden('#skF_1'('#skF_6',B_145),'#skF_3')
      | B_145 = '#skF_6'
      | k1_relat_1(B_145) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_145)
      | ~ v1_relat_1(B_145)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_735,c_811])).

tff(c_1006,plain,(
    ! [B_176] :
      ( r2_hidden('#skF_1'('#skF_6',B_176),'#skF_3')
      | B_176 = '#skF_6'
      | k1_relat_1(B_176) != '#skF_3'
      | ~ v1_funct_1(B_176)
      | ~ v1_relat_1(B_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_60,c_735,c_817])).

tff(c_54,plain,(
    ! [E_39] :
      ( k1_funct_1('#skF_5',E_39) = k1_funct_1('#skF_6',E_39)
      | ~ r2_hidden(E_39,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1321,plain,(
    ! [B_191] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_6',B_191)) = k1_funct_1('#skF_6','#skF_1'('#skF_6',B_191))
      | B_191 = '#skF_6'
      | k1_relat_1(B_191) != '#skF_3'
      | ~ v1_funct_1(B_191)
      | ~ v1_relat_1(B_191) ) ),
    inference(resolution,[status(thm)],[c_1006,c_54])).

tff(c_16,plain,(
    ! [B_13,A_9] :
      ( k1_funct_1(B_13,'#skF_1'(A_9,B_13)) != k1_funct_1(A_9,'#skF_1'(A_9,B_13))
      | B_13 = A_9
      | k1_relat_1(B_13) != k1_relat_1(A_9)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1328,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1321,c_16])).

tff(c_1335,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_66,c_729,c_153,c_60,c_729,c_735,c_1328])).

tff(c_52,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1347,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1335,c_52])).

tff(c_1357,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_1347])).

tff(c_1358,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_725])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1391,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1358,c_2])).

tff(c_1393,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_1391])).

tff(c_1394,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_722])).

tff(c_1427,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1394,c_2])).

tff(c_1429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_1427])).

tff(c_1431,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_99,plain,(
    ! [B_51,A_52] :
      ( ~ v1_xboole_0(B_51)
      | B_51 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_102,plain,(
    ! [A_52] :
      ( k1_xboole_0 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_2,c_99])).

tff(c_1444,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1431,c_102])).

tff(c_1430,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_1437,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1430,c_102])).

tff(c_1479,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1444,c_1437])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1469,plain,(
    ! [A_5] : m1_subset_1('#skF_5',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_12])).

tff(c_1581,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1479,c_1469])).

tff(c_50,plain,(
    ! [A_32,B_33] : m1_subset_1('#skF_2'(A_32,B_33),k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1946,plain,(
    ! [A_235,B_236,C_237,D_238] :
      ( r2_relset_1(A_235,B_236,C_237,C_237)
      | ~ m1_subset_1(D_238,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236)))
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2261,plain,(
    ! [A_280,B_281,C_282] :
      ( r2_relset_1(A_280,B_281,C_282,C_282)
      | ~ m1_subset_1(C_282,k1_zfmisc_1(k2_zfmisc_1(A_280,B_281))) ) ),
    inference(resolution,[status(thm)],[c_50,c_1946])).

tff(c_2271,plain,(
    ! [A_280,B_281] : r2_relset_1(A_280,B_281,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1581,c_2261])).

tff(c_217,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_195])).

tff(c_1498,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1431,c_217])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1438,plain,(
    ! [A_1] :
      ( A_1 = '#skF_5'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_1430,c_4])).

tff(c_1503,plain,(
    ! [A_194] :
      ( A_194 = '#skF_4'
      | ~ v1_xboole_0(A_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1479,c_1438])).

tff(c_1510,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1498,c_1503])).

tff(c_1489,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1479,c_52])).

tff(c_1604,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1510,c_1489])).

tff(c_2275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2271,c_1604])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.96/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.77  
% 3.96/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.31/1.77  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.31/1.77  
% 4.31/1.77  %Foreground sorts:
% 4.31/1.77  
% 4.31/1.77  
% 4.31/1.77  %Background operators:
% 4.31/1.77  
% 4.31/1.77  
% 4.31/1.77  %Foreground operators:
% 4.31/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.31/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.31/1.77  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.31/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.31/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.31/1.77  tff('#skF_5', type, '#skF_5': $i).
% 4.31/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.31/1.77  tff('#skF_6', type, '#skF_6': $i).
% 4.31/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.31/1.77  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.31/1.77  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.31/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.31/1.77  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.31/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.31/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.31/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.31/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.31/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.31/1.77  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.31/1.77  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.31/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.31/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.31/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.31/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.31/1.77  
% 4.37/1.79  tff(f_139, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 4.37/1.79  tff(f_77, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.37/1.79  tff(f_87, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 4.37/1.79  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.37/1.79  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.37/1.79  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.37/1.79  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 4.37/1.79  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.37/1.79  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 4.37/1.79  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.37/1.79  tff(f_118, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 4.37/1.79  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.37/1.79  tff(c_195, plain, (![C_77, B_78, A_79]: (v1_xboole_0(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(B_78, A_79))) | ~v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.37/1.79  tff(c_216, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_195])).
% 4.37/1.79  tff(c_222, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_216])).
% 4.37/1.79  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.37/1.79  tff(c_434, plain, (![A_102, B_103, C_104, D_105]: (r2_relset_1(A_102, B_103, C_104, C_104) | ~m1_subset_1(D_105, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.37/1.79  tff(c_482, plain, (![C_108]: (r2_relset_1('#skF_3', '#skF_4', C_108, C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_56, c_434])).
% 4.37/1.79  tff(c_495, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_482])).
% 4.37/1.79  tff(c_132, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.37/1.79  tff(c_152, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_132])).
% 4.37/1.79  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.37/1.79  tff(c_64, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.37/1.79  tff(c_223, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.37/1.79  tff(c_244, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_223])).
% 4.37/1.79  tff(c_697, plain, (![B_134, A_135, C_136]: (k1_xboole_0=B_134 | k1_relset_1(A_135, B_134, C_136)=A_135 | ~v1_funct_2(C_136, A_135, B_134) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_135, B_134))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.37/1.79  tff(c_703, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_697])).
% 4.37/1.79  tff(c_722, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_244, c_703])).
% 4.37/1.79  tff(c_729, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_722])).
% 4.37/1.79  tff(c_153, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_132])).
% 4.37/1.79  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.37/1.79  tff(c_58, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.37/1.79  tff(c_245, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_223])).
% 4.37/1.79  tff(c_706, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_697])).
% 4.37/1.79  tff(c_725, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_245, c_706])).
% 4.37/1.79  tff(c_735, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_725])).
% 4.37/1.79  tff(c_811, plain, (![A_144, B_145]: (r2_hidden('#skF_1'(A_144, B_145), k1_relat_1(A_144)) | B_145=A_144 | k1_relat_1(B_145)!=k1_relat_1(A_144) | ~v1_funct_1(B_145) | ~v1_relat_1(B_145) | ~v1_funct_1(A_144) | ~v1_relat_1(A_144))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.37/1.79  tff(c_817, plain, (![B_145]: (r2_hidden('#skF_1'('#skF_6', B_145), '#skF_3') | B_145='#skF_6' | k1_relat_1(B_145)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_145) | ~v1_relat_1(B_145) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_735, c_811])).
% 4.37/1.79  tff(c_1006, plain, (![B_176]: (r2_hidden('#skF_1'('#skF_6', B_176), '#skF_3') | B_176='#skF_6' | k1_relat_1(B_176)!='#skF_3' | ~v1_funct_1(B_176) | ~v1_relat_1(B_176))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_60, c_735, c_817])).
% 4.37/1.79  tff(c_54, plain, (![E_39]: (k1_funct_1('#skF_5', E_39)=k1_funct_1('#skF_6', E_39) | ~r2_hidden(E_39, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.37/1.79  tff(c_1321, plain, (![B_191]: (k1_funct_1('#skF_5', '#skF_1'('#skF_6', B_191))=k1_funct_1('#skF_6', '#skF_1'('#skF_6', B_191)) | B_191='#skF_6' | k1_relat_1(B_191)!='#skF_3' | ~v1_funct_1(B_191) | ~v1_relat_1(B_191))), inference(resolution, [status(thm)], [c_1006, c_54])).
% 4.37/1.79  tff(c_16, plain, (![B_13, A_9]: (k1_funct_1(B_13, '#skF_1'(A_9, B_13))!=k1_funct_1(A_9, '#skF_1'(A_9, B_13)) | B_13=A_9 | k1_relat_1(B_13)!=k1_relat_1(A_9) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.37/1.79  tff(c_1328, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1321, c_16])).
% 4.37/1.79  tff(c_1335, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_66, c_729, c_153, c_60, c_729, c_735, c_1328])).
% 4.37/1.79  tff(c_52, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.37/1.79  tff(c_1347, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1335, c_52])).
% 4.37/1.79  tff(c_1357, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_495, c_1347])).
% 4.37/1.79  tff(c_1358, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_725])).
% 4.37/1.79  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.37/1.79  tff(c_1391, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1358, c_2])).
% 4.37/1.79  tff(c_1393, plain, $false, inference(negUnitSimplification, [status(thm)], [c_222, c_1391])).
% 4.37/1.79  tff(c_1394, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_722])).
% 4.37/1.79  tff(c_1427, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1394, c_2])).
% 4.37/1.79  tff(c_1429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_222, c_1427])).
% 4.37/1.79  tff(c_1431, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_216])).
% 4.37/1.79  tff(c_99, plain, (![B_51, A_52]: (~v1_xboole_0(B_51) | B_51=A_52 | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.37/1.79  tff(c_102, plain, (![A_52]: (k1_xboole_0=A_52 | ~v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_2, c_99])).
% 4.37/1.79  tff(c_1444, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1431, c_102])).
% 4.37/1.79  tff(c_1430, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_216])).
% 4.37/1.79  tff(c_1437, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1430, c_102])).
% 4.37/1.79  tff(c_1479, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1444, c_1437])).
% 4.37/1.79  tff(c_12, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.37/1.79  tff(c_1469, plain, (![A_5]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_1437, c_12])).
% 4.37/1.79  tff(c_1581, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_1479, c_1469])).
% 4.37/1.79  tff(c_50, plain, (![A_32, B_33]: (m1_subset_1('#skF_2'(A_32, B_33), k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.37/1.79  tff(c_1946, plain, (![A_235, B_236, C_237, D_238]: (r2_relset_1(A_235, B_236, C_237, C_237) | ~m1_subset_1(D_238, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.37/1.79  tff(c_2261, plain, (![A_280, B_281, C_282]: (r2_relset_1(A_280, B_281, C_282, C_282) | ~m1_subset_1(C_282, k1_zfmisc_1(k2_zfmisc_1(A_280, B_281))))), inference(resolution, [status(thm)], [c_50, c_1946])).
% 4.37/1.79  tff(c_2271, plain, (![A_280, B_281]: (r2_relset_1(A_280, B_281, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_1581, c_2261])).
% 4.37/1.79  tff(c_217, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_195])).
% 4.37/1.79  tff(c_1498, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1431, c_217])).
% 4.37/1.79  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.37/1.79  tff(c_1438, plain, (![A_1]: (A_1='#skF_5' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_1430, c_4])).
% 4.37/1.79  tff(c_1503, plain, (![A_194]: (A_194='#skF_4' | ~v1_xboole_0(A_194))), inference(demodulation, [status(thm), theory('equality')], [c_1479, c_1438])).
% 4.37/1.79  tff(c_1510, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_1498, c_1503])).
% 4.37/1.79  tff(c_1489, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1479, c_52])).
% 4.37/1.79  tff(c_1604, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1510, c_1489])).
% 4.37/1.79  tff(c_2275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2271, c_1604])).
% 4.37/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.79  
% 4.37/1.79  Inference rules
% 4.37/1.79  ----------------------
% 4.37/1.79  #Ref     : 2
% 4.37/1.79  #Sup     : 493
% 4.37/1.79  #Fact    : 0
% 4.37/1.79  #Define  : 0
% 4.37/1.79  #Split   : 5
% 4.37/1.79  #Chain   : 0
% 4.37/1.79  #Close   : 0
% 4.37/1.79  
% 4.37/1.79  Ordering : KBO
% 4.37/1.79  
% 4.37/1.79  Simplification rules
% 4.37/1.79  ----------------------
% 4.37/1.79  #Subsume      : 104
% 4.37/1.79  #Demod        : 602
% 4.37/1.79  #Tautology    : 287
% 4.37/1.79  #SimpNegUnit  : 6
% 4.37/1.79  #BackRed      : 120
% 4.37/1.79  
% 4.37/1.79  #Partial instantiations: 0
% 4.37/1.79  #Strategies tried      : 1
% 4.37/1.79  
% 4.37/1.79  Timing (in seconds)
% 4.37/1.79  ----------------------
% 4.37/1.79  Preprocessing        : 0.36
% 4.37/1.79  Parsing              : 0.19
% 4.37/1.79  CNF conversion       : 0.02
% 4.37/1.79  Main loop            : 0.61
% 4.37/1.79  Inferencing          : 0.21
% 4.37/1.79  Reduction            : 0.21
% 4.37/1.79  Demodulation         : 0.16
% 4.37/1.79  BG Simplification    : 0.03
% 4.37/1.79  Subsumption          : 0.11
% 4.37/1.79  Abstraction          : 0.03
% 4.37/1.79  MUC search           : 0.00
% 4.37/1.79  Cooper               : 0.00
% 4.37/1.79  Total                : 1.01
% 4.37/1.79  Index Insertion      : 0.00
% 4.37/1.79  Index Deletion       : 0.00
% 4.37/1.79  Index Matching       : 0.00
% 4.37/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
