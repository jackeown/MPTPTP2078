%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:59 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 990 expanded)
%              Number of leaves         :   34 ( 322 expanded)
%              Depth                    :   14
%              Number of atoms          :  335 (3329 expanded)
%              Number of equality atoms :   83 (1077 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_117,negated_conjecture,(
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

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_76,axiom,(
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

tff(f_94,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_70,plain,(
    ! [B_42,A_43] :
      ( v1_relat_1(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_73,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_70])).

tff(c_79,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_73])).

tff(c_399,plain,(
    ! [C_93,A_94,B_95] :
      ( v4_relat_1(C_93,A_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_406,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_399])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(B_8),A_7)
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,
    ( r2_hidden('#skF_6',k1_relset_1('#skF_2','#skF_3','#skF_4'))
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_124,plain,(
    ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_76,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_70])).

tff(c_82,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_76])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_137,plain,(
    ! [C_56,A_57,B_58] :
      ( v4_relat_1(C_56,A_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_144,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_137])).

tff(c_42,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_46,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_146,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_154,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_146])).

tff(c_208,plain,(
    ! [B_78,A_79,C_80] :
      ( k1_xboole_0 = B_78
      | k1_relset_1(A_79,B_78,C_80) = A_79
      | ~ v1_funct_2(C_80,A_79,B_78)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_214,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_208])).

tff(c_220,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_154,c_214])).

tff(c_221,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_220])).

tff(c_323,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_1'(A_85,B_86),k1_relat_1(A_85))
      | r1_partfun1(A_85,B_86)
      | ~ r1_tarski(k1_relat_1(A_85),k1_relat_1(B_86))
      | ~ v1_funct_1(B_86)
      | ~ v1_relat_1(B_86)
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_153,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_146])).

tff(c_64,plain,(
    ! [E_37] :
      ( r1_partfun1('#skF_4','#skF_5')
      | k1_funct_1('#skF_5',E_37) = k1_funct_1('#skF_4',E_37)
      | ~ r2_hidden(E_37,k1_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_155,plain,(
    ! [E_37] :
      ( k1_funct_1('#skF_5',E_37) = k1_funct_1('#skF_4',E_37)
      | ~ r2_hidden(E_37,k1_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_64])).

tff(c_157,plain,(
    ! [E_37] :
      ( k1_funct_1('#skF_5',E_37) = k1_funct_1('#skF_4',E_37)
      | ~ r2_hidden(E_37,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_155])).

tff(c_327,plain,(
    ! [B_86] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_86)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_86))
      | r1_partfun1('#skF_4',B_86)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_86))
      | ~ v1_funct_1(B_86)
      | ~ v1_relat_1(B_86)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_323,c_157])).

tff(c_337,plain,(
    ! [B_88] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_88)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_88))
      | r1_partfun1('#skF_4',B_88)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_88))
      | ~ v1_funct_1(B_88)
      | ~ v1_relat_1(B_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_52,c_327])).

tff(c_340,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_337])).

tff(c_349,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_48,c_340])).

tff(c_350,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_349])).

tff(c_365,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_368,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_365])).

tff(c_372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_144,c_368])).

tff(c_374,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_373,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_38,plain,(
    ! [B_26,A_20] :
      ( k1_funct_1(B_26,'#skF_1'(A_20,B_26)) != k1_funct_1(A_20,'#skF_1'(A_20,B_26))
      | r1_partfun1(A_20,B_26)
      | ~ r1_tarski(k1_relat_1(A_20),k1_relat_1(B_26))
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_388,plain,
    ( r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_38])).

tff(c_393,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_52,c_82,c_48,c_374,c_221,c_388])).

tff(c_395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_393])).

tff(c_397,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,
    ( k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_409,plain,(
    k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_54])).

tff(c_422,plain,(
    ! [A_100,B_101,C_102] :
      ( k1_relset_1(A_100,B_101,C_102) = k1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_430,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_422])).

tff(c_466,plain,(
    ! [B_113,A_114,C_115] :
      ( k1_xboole_0 = B_113
      | k1_relset_1(A_114,B_113,C_115) = A_114
      | ~ v1_funct_2(C_115,A_114,B_113)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_114,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_472,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_466])).

tff(c_478,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_430,c_472])).

tff(c_479,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_478])).

tff(c_429,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_422])).

tff(c_396,plain,(
    r2_hidden('#skF_6',k1_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_432,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_396])).

tff(c_604,plain,(
    ! [B_126,C_127,A_128] :
      ( k1_funct_1(B_126,C_127) = k1_funct_1(A_128,C_127)
      | ~ r2_hidden(C_127,k1_relat_1(A_128))
      | ~ r1_partfun1(A_128,B_126)
      | ~ r1_tarski(k1_relat_1(A_128),k1_relat_1(B_126))
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_610,plain,(
    ! [B_126] :
      ( k1_funct_1(B_126,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_126)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_126))
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_432,c_604])).

tff(c_617,plain,(
    ! [B_129] :
      ( k1_funct_1(B_129,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_129)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_129))
      | ~ v1_funct_1(B_129)
      | ~ v1_relat_1(B_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_52,c_610])).

tff(c_620,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_617])).

tff(c_629,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_48,c_397,c_620])).

tff(c_630,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_409,c_629])).

tff(c_640,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_630])).

tff(c_644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_406,c_640])).

tff(c_646,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_645,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_652,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_645])).

tff(c_703,plain,
    ( r2_hidden('#skF_6',k1_relset_1('#skF_3','#skF_3','#skF_4'))
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_56])).

tff(c_704,plain,(
    ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_703])).

tff(c_665,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_44])).

tff(c_690,plain,(
    ! [B_136,A_137] :
      ( v1_relat_1(B_136)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(A_137))
      | ~ v1_relat_1(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_696,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_665,c_690])).

tff(c_702,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_696])).

tff(c_666,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_50])).

tff(c_693,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_666,c_690])).

tff(c_699,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_693])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_705,plain,(
    ! [C_138,A_139,B_140] :
      ( v4_relat_1(C_138,A_139)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_712,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_666,c_705])).

tff(c_721,plain,(
    ! [B_144,A_145] :
      ( r1_tarski(k1_relat_1(B_144),A_145)
      | ~ v4_relat_1(B_144,A_145)
      | ~ v1_relat_1(B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_647,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_8])).

tff(c_662,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_647])).

tff(c_667,plain,(
    ! [B_133,A_134] :
      ( B_133 = A_134
      | ~ r1_tarski(B_133,A_134)
      | ~ r1_tarski(A_134,B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_672,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'
      | ~ r1_tarski(A_3,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_662,c_667])).

tff(c_734,plain,(
    ! [B_146] :
      ( k1_relat_1(B_146) = '#skF_3'
      | ~ v4_relat_1(B_146,'#skF_3')
      | ~ v1_relat_1(B_146) ) ),
    inference(resolution,[status(thm)],[c_721,c_672])).

tff(c_740,plain,
    ( k1_relat_1('#skF_4') = '#skF_3'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_712,c_734])).

tff(c_746,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_740])).

tff(c_713,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_665,c_705])).

tff(c_737,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_713,c_734])).

tff(c_743,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_737])).

tff(c_965,plain,(
    ! [A_174,B_175] :
      ( r2_hidden('#skF_1'(A_174,B_175),k1_relat_1(A_174))
      | r1_partfun1(A_174,B_175)
      | ~ r1_tarski(k1_relat_1(A_174),k1_relat_1(B_175))
      | ~ v1_funct_1(B_175)
      | ~ v1_relat_1(B_175)
      | ~ v1_funct_1(A_174)
      | ~ v1_relat_1(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_968,plain,(
    ! [B_175] :
      ( r2_hidden('#skF_1'('#skF_4',B_175),'#skF_3')
      | r1_partfun1('#skF_4',B_175)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_175))
      | ~ v1_funct_1(B_175)
      | ~ v1_relat_1(B_175)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_746,c_965])).

tff(c_976,plain,(
    ! [B_176] :
      ( r2_hidden('#skF_1'('#skF_4',B_176),'#skF_3')
      | r1_partfun1('#skF_4',B_176)
      | ~ v1_funct_1(B_176)
      | ~ v1_relat_1(B_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_52,c_662,c_746,c_968])).

tff(c_817,plain,(
    ! [A_154,B_155,C_156] :
      ( k1_relset_1(A_154,B_155,C_156) = k1_relat_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_820,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_666,c_817])).

tff(c_825,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_746,c_820])).

tff(c_775,plain,(
    ! [E_37] :
      ( r1_partfun1('#skF_4','#skF_5')
      | k1_funct_1('#skF_5',E_37) = k1_funct_1('#skF_4',E_37)
      | ~ r2_hidden(E_37,k1_relset_1('#skF_3','#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_64])).

tff(c_776,plain,(
    ! [E_37] :
      ( k1_funct_1('#skF_5',E_37) = k1_funct_1('#skF_4',E_37)
      | ~ r2_hidden(E_37,k1_relset_1('#skF_3','#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_704,c_775])).

tff(c_842,plain,(
    ! [E_37] :
      ( k1_funct_1('#skF_5',E_37) = k1_funct_1('#skF_4',E_37)
      | ~ r2_hidden(E_37,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_825,c_776])).

tff(c_980,plain,(
    ! [B_176] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_176)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_176))
      | r1_partfun1('#skF_4',B_176)
      | ~ v1_funct_1(B_176)
      | ~ v1_relat_1(B_176) ) ),
    inference(resolution,[status(thm)],[c_976,c_842])).

tff(c_1028,plain,(
    ! [B_185,A_186] :
      ( k1_funct_1(B_185,'#skF_1'(A_186,B_185)) != k1_funct_1(A_186,'#skF_1'(A_186,B_185))
      | r1_partfun1(A_186,B_185)
      | ~ r1_tarski(k1_relat_1(A_186),k1_relat_1(B_185))
      | ~ v1_funct_1(B_185)
      | ~ v1_relat_1(B_185)
      | ~ v1_funct_1(A_186)
      | ~ v1_relat_1(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1033,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | r1_partfun1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_980,c_1028])).

tff(c_1038,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_48,c_699,c_52,c_6,c_746,c_743,c_1033])).

tff(c_1040,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_704,c_1038])).

tff(c_1042,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_703])).

tff(c_1053,plain,(
    k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1042,c_54])).

tff(c_1061,plain,(
    ! [C_193,A_194,B_195] :
      ( v4_relat_1(C_193,A_194)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1068,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_666,c_1061])).

tff(c_1070,plain,(
    ! [B_196,A_197] :
      ( r1_tarski(k1_relat_1(B_196),A_197)
      | ~ v4_relat_1(B_196,A_197)
      | ~ v1_relat_1(B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1083,plain,(
    ! [B_198] :
      ( k1_relat_1(B_198) = '#skF_3'
      | ~ v4_relat_1(B_198,'#skF_3')
      | ~ v1_relat_1(B_198) ) ),
    inference(resolution,[status(thm)],[c_1070,c_672])).

tff(c_1089,plain,
    ( k1_relat_1('#skF_4') = '#skF_3'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1068,c_1083])).

tff(c_1095,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_1089])).

tff(c_1155,plain,(
    ! [A_202,B_203,C_204] :
      ( k1_relset_1(A_202,B_203,C_204) = k1_relat_1(C_204)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1158,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_666,c_1155])).

tff(c_1163,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1095,c_1158])).

tff(c_1041,plain,(
    r2_hidden('#skF_6',k1_relset_1('#skF_3','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_703])).

tff(c_1166,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1163,c_1041])).

tff(c_1322,plain,(
    ! [B_228,C_229,A_230] :
      ( k1_funct_1(B_228,C_229) = k1_funct_1(A_230,C_229)
      | ~ r2_hidden(C_229,k1_relat_1(A_230))
      | ~ r1_partfun1(A_230,B_228)
      | ~ r1_tarski(k1_relat_1(A_230),k1_relat_1(B_228))
      | ~ v1_funct_1(B_228)
      | ~ v1_relat_1(B_228)
      | ~ v1_funct_1(A_230)
      | ~ v1_relat_1(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1326,plain,(
    ! [B_228,C_229] :
      ( k1_funct_1(B_228,C_229) = k1_funct_1('#skF_4',C_229)
      | ~ r2_hidden(C_229,'#skF_3')
      | ~ r1_partfun1('#skF_4',B_228)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_228))
      | ~ v1_funct_1(B_228)
      | ~ v1_relat_1(B_228)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1095,c_1322])).

tff(c_1360,plain,(
    ! [B_234,C_235] :
      ( k1_funct_1(B_234,C_235) = k1_funct_1('#skF_4',C_235)
      | ~ r2_hidden(C_235,'#skF_3')
      | ~ r1_partfun1('#skF_4',B_234)
      | ~ v1_funct_1(B_234)
      | ~ v1_relat_1(B_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_52,c_662,c_1095,c_1326])).

tff(c_1370,plain,(
    ! [B_236] :
      ( k1_funct_1(B_236,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_236)
      | ~ v1_funct_1(B_236)
      | ~ v1_relat_1(B_236) ) ),
    inference(resolution,[status(thm)],[c_1166,c_1360])).

tff(c_1377,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1042,c_1370])).

tff(c_1384,plain,(
    k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_48,c_1377])).

tff(c_1386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1053,c_1384])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:28:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.56  
% 3.55/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.56  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.55/1.56  
% 3.55/1.56  %Foreground sorts:
% 3.55/1.56  
% 3.55/1.56  
% 3.55/1.56  %Background operators:
% 3.55/1.56  
% 3.55/1.56  
% 3.55/1.56  %Foreground operators:
% 3.55/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.55/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.55/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.55/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.55/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.55/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.55/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.55/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.55/1.56  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.55/1.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.55/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.55/1.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.55/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.55/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.55/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.55/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.55/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.55/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.55/1.56  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 3.55/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.55/1.56  
% 3.74/1.58  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.74/1.58  tff(f_117, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (r1_partfun1(C, D) <=> (![E]: (r2_hidden(E, k1_relset_1(A, B, C)) => (k1_funct_1(C, E) = k1_funct_1(D, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_2)).
% 3.74/1.58  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.74/1.58  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.74/1.58  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.74/1.58  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.74/1.58  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.74/1.58  tff(f_94, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) => (r1_partfun1(A, B) <=> (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_partfun1)).
% 3.74/1.58  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.74/1.58  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.74/1.58  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.74/1.58  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.74/1.58  tff(c_70, plain, (![B_42, A_43]: (v1_relat_1(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.74/1.58  tff(c_73, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_70])).
% 3.74/1.58  tff(c_79, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_73])).
% 3.74/1.58  tff(c_399, plain, (![C_93, A_94, B_95]: (v4_relat_1(C_93, A_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.74/1.58  tff(c_406, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_399])).
% 3.74/1.58  tff(c_14, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(B_8), A_7) | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.74/1.58  tff(c_56, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.74/1.58  tff(c_124, plain, (~r1_partfun1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_56])).
% 3.74/1.58  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.74/1.58  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.74/1.58  tff(c_76, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_70])).
% 3.74/1.58  tff(c_82, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_76])).
% 3.74/1.58  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.74/1.58  tff(c_137, plain, (![C_56, A_57, B_58]: (v4_relat_1(C_56, A_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.74/1.58  tff(c_144, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_137])).
% 3.74/1.58  tff(c_42, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.74/1.58  tff(c_68, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_42])).
% 3.74/1.58  tff(c_46, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.74/1.58  tff(c_146, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.74/1.58  tff(c_154, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_146])).
% 3.74/1.58  tff(c_208, plain, (![B_78, A_79, C_80]: (k1_xboole_0=B_78 | k1_relset_1(A_79, B_78, C_80)=A_79 | ~v1_funct_2(C_80, A_79, B_78) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.74/1.58  tff(c_214, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_208])).
% 3.74/1.58  tff(c_220, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_154, c_214])).
% 3.74/1.58  tff(c_221, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_68, c_220])).
% 3.74/1.58  tff(c_323, plain, (![A_85, B_86]: (r2_hidden('#skF_1'(A_85, B_86), k1_relat_1(A_85)) | r1_partfun1(A_85, B_86) | ~r1_tarski(k1_relat_1(A_85), k1_relat_1(B_86)) | ~v1_funct_1(B_86) | ~v1_relat_1(B_86) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.74/1.58  tff(c_153, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_146])).
% 3.74/1.58  tff(c_64, plain, (![E_37]: (r1_partfun1('#skF_4', '#skF_5') | k1_funct_1('#skF_5', E_37)=k1_funct_1('#skF_4', E_37) | ~r2_hidden(E_37, k1_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.74/1.58  tff(c_155, plain, (![E_37]: (k1_funct_1('#skF_5', E_37)=k1_funct_1('#skF_4', E_37) | ~r2_hidden(E_37, k1_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_124, c_64])).
% 3.74/1.58  tff(c_157, plain, (![E_37]: (k1_funct_1('#skF_5', E_37)=k1_funct_1('#skF_4', E_37) | ~r2_hidden(E_37, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_155])).
% 3.74/1.58  tff(c_327, plain, (![B_86]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_86))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_86)) | r1_partfun1('#skF_4', B_86) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_86)) | ~v1_funct_1(B_86) | ~v1_relat_1(B_86) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_323, c_157])).
% 3.74/1.58  tff(c_337, plain, (![B_88]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_88))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_88)) | r1_partfun1('#skF_4', B_88) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_88)) | ~v1_funct_1(B_88) | ~v1_relat_1(B_88))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_52, c_327])).
% 3.74/1.58  tff(c_340, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_221, c_337])).
% 3.74/1.58  tff(c_349, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_48, c_340])).
% 3.74/1.58  tff(c_350, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_124, c_349])).
% 3.74/1.58  tff(c_365, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_350])).
% 3.74/1.58  tff(c_368, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_365])).
% 3.74/1.58  tff(c_372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_144, c_368])).
% 3.74/1.58  tff(c_374, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_350])).
% 3.74/1.58  tff(c_373, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_350])).
% 3.74/1.58  tff(c_38, plain, (![B_26, A_20]: (k1_funct_1(B_26, '#skF_1'(A_20, B_26))!=k1_funct_1(A_20, '#skF_1'(A_20, B_26)) | r1_partfun1(A_20, B_26) | ~r1_tarski(k1_relat_1(A_20), k1_relat_1(B_26)) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.74/1.58  tff(c_388, plain, (r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_373, c_38])).
% 3.74/1.58  tff(c_393, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_52, c_82, c_48, c_374, c_221, c_388])).
% 3.74/1.58  tff(c_395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_393])).
% 3.74/1.58  tff(c_397, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_56])).
% 3.74/1.58  tff(c_54, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.74/1.58  tff(c_409, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_397, c_54])).
% 3.74/1.58  tff(c_422, plain, (![A_100, B_101, C_102]: (k1_relset_1(A_100, B_101, C_102)=k1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.74/1.58  tff(c_430, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_422])).
% 3.74/1.58  tff(c_466, plain, (![B_113, A_114, C_115]: (k1_xboole_0=B_113 | k1_relset_1(A_114, B_113, C_115)=A_114 | ~v1_funct_2(C_115, A_114, B_113) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_114, B_113))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.74/1.58  tff(c_472, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_466])).
% 3.74/1.58  tff(c_478, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_430, c_472])).
% 3.74/1.58  tff(c_479, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_68, c_478])).
% 3.74/1.58  tff(c_429, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_422])).
% 3.74/1.58  tff(c_396, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_56])).
% 3.74/1.58  tff(c_432, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_429, c_396])).
% 3.74/1.58  tff(c_604, plain, (![B_126, C_127, A_128]: (k1_funct_1(B_126, C_127)=k1_funct_1(A_128, C_127) | ~r2_hidden(C_127, k1_relat_1(A_128)) | ~r1_partfun1(A_128, B_126) | ~r1_tarski(k1_relat_1(A_128), k1_relat_1(B_126)) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.74/1.58  tff(c_610, plain, (![B_126]: (k1_funct_1(B_126, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_126) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_126)) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_432, c_604])).
% 3.74/1.58  tff(c_617, plain, (![B_129]: (k1_funct_1(B_129, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_129) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_129)) | ~v1_funct_1(B_129) | ~v1_relat_1(B_129))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_52, c_610])).
% 3.74/1.58  tff(c_620, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_479, c_617])).
% 3.74/1.58  tff(c_629, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_48, c_397, c_620])).
% 3.74/1.58  tff(c_630, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_409, c_629])).
% 3.74/1.58  tff(c_640, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_630])).
% 3.74/1.58  tff(c_644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_406, c_640])).
% 3.74/1.58  tff(c_646, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_42])).
% 3.74/1.58  tff(c_645, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_42])).
% 3.74/1.58  tff(c_652, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_646, c_645])).
% 3.74/1.58  tff(c_703, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_3', '#skF_3', '#skF_4')) | ~r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_652, c_56])).
% 3.74/1.58  tff(c_704, plain, (~r1_partfun1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_703])).
% 3.74/1.58  tff(c_665, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_652, c_44])).
% 3.74/1.58  tff(c_690, plain, (![B_136, A_137]: (v1_relat_1(B_136) | ~m1_subset_1(B_136, k1_zfmisc_1(A_137)) | ~v1_relat_1(A_137))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.74/1.58  tff(c_696, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_665, c_690])).
% 3.74/1.58  tff(c_702, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_696])).
% 3.74/1.58  tff(c_666, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_652, c_50])).
% 3.74/1.58  tff(c_693, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_666, c_690])).
% 3.74/1.58  tff(c_699, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_693])).
% 3.74/1.58  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.74/1.58  tff(c_705, plain, (![C_138, A_139, B_140]: (v4_relat_1(C_138, A_139) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.74/1.58  tff(c_712, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_666, c_705])).
% 3.74/1.58  tff(c_721, plain, (![B_144, A_145]: (r1_tarski(k1_relat_1(B_144), A_145) | ~v4_relat_1(B_144, A_145) | ~v1_relat_1(B_144))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.74/1.58  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.74/1.58  tff(c_647, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_645, c_8])).
% 3.74/1.58  tff(c_662, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_652, c_647])).
% 3.74/1.58  tff(c_667, plain, (![B_133, A_134]: (B_133=A_134 | ~r1_tarski(B_133, A_134) | ~r1_tarski(A_134, B_133))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.74/1.58  tff(c_672, plain, (![A_3]: (A_3='#skF_3' | ~r1_tarski(A_3, '#skF_3'))), inference(resolution, [status(thm)], [c_662, c_667])).
% 3.74/1.58  tff(c_734, plain, (![B_146]: (k1_relat_1(B_146)='#skF_3' | ~v4_relat_1(B_146, '#skF_3') | ~v1_relat_1(B_146))), inference(resolution, [status(thm)], [c_721, c_672])).
% 3.74/1.58  tff(c_740, plain, (k1_relat_1('#skF_4')='#skF_3' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_712, c_734])).
% 3.74/1.58  tff(c_746, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_699, c_740])).
% 3.74/1.58  tff(c_713, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_665, c_705])).
% 3.74/1.58  tff(c_737, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_713, c_734])).
% 3.74/1.58  tff(c_743, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_702, c_737])).
% 3.74/1.58  tff(c_965, plain, (![A_174, B_175]: (r2_hidden('#skF_1'(A_174, B_175), k1_relat_1(A_174)) | r1_partfun1(A_174, B_175) | ~r1_tarski(k1_relat_1(A_174), k1_relat_1(B_175)) | ~v1_funct_1(B_175) | ~v1_relat_1(B_175) | ~v1_funct_1(A_174) | ~v1_relat_1(A_174))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.74/1.58  tff(c_968, plain, (![B_175]: (r2_hidden('#skF_1'('#skF_4', B_175), '#skF_3') | r1_partfun1('#skF_4', B_175) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_175)) | ~v1_funct_1(B_175) | ~v1_relat_1(B_175) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_746, c_965])).
% 3.74/1.58  tff(c_976, plain, (![B_176]: (r2_hidden('#skF_1'('#skF_4', B_176), '#skF_3') | r1_partfun1('#skF_4', B_176) | ~v1_funct_1(B_176) | ~v1_relat_1(B_176))), inference(demodulation, [status(thm), theory('equality')], [c_699, c_52, c_662, c_746, c_968])).
% 3.74/1.58  tff(c_817, plain, (![A_154, B_155, C_156]: (k1_relset_1(A_154, B_155, C_156)=k1_relat_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.74/1.58  tff(c_820, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_666, c_817])).
% 3.74/1.58  tff(c_825, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_746, c_820])).
% 3.74/1.58  tff(c_775, plain, (![E_37]: (r1_partfun1('#skF_4', '#skF_5') | k1_funct_1('#skF_5', E_37)=k1_funct_1('#skF_4', E_37) | ~r2_hidden(E_37, k1_relset_1('#skF_3', '#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_652, c_64])).
% 3.74/1.58  tff(c_776, plain, (![E_37]: (k1_funct_1('#skF_5', E_37)=k1_funct_1('#skF_4', E_37) | ~r2_hidden(E_37, k1_relset_1('#skF_3', '#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_704, c_775])).
% 3.74/1.58  tff(c_842, plain, (![E_37]: (k1_funct_1('#skF_5', E_37)=k1_funct_1('#skF_4', E_37) | ~r2_hidden(E_37, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_825, c_776])).
% 3.74/1.58  tff(c_980, plain, (![B_176]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_176))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_176)) | r1_partfun1('#skF_4', B_176) | ~v1_funct_1(B_176) | ~v1_relat_1(B_176))), inference(resolution, [status(thm)], [c_976, c_842])).
% 3.74/1.58  tff(c_1028, plain, (![B_185, A_186]: (k1_funct_1(B_185, '#skF_1'(A_186, B_185))!=k1_funct_1(A_186, '#skF_1'(A_186, B_185)) | r1_partfun1(A_186, B_185) | ~r1_tarski(k1_relat_1(A_186), k1_relat_1(B_185)) | ~v1_funct_1(B_185) | ~v1_relat_1(B_185) | ~v1_funct_1(A_186) | ~v1_relat_1(A_186))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.74/1.58  tff(c_1033, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | r1_partfun1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_980, c_1028])).
% 3.74/1.58  tff(c_1038, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_702, c_48, c_699, c_52, c_6, c_746, c_743, c_1033])).
% 3.74/1.58  tff(c_1040, plain, $false, inference(negUnitSimplification, [status(thm)], [c_704, c_1038])).
% 3.74/1.58  tff(c_1042, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_703])).
% 3.74/1.58  tff(c_1053, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1042, c_54])).
% 3.74/1.58  tff(c_1061, plain, (![C_193, A_194, B_195]: (v4_relat_1(C_193, A_194) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.74/1.58  tff(c_1068, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_666, c_1061])).
% 3.74/1.58  tff(c_1070, plain, (![B_196, A_197]: (r1_tarski(k1_relat_1(B_196), A_197) | ~v4_relat_1(B_196, A_197) | ~v1_relat_1(B_196))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.74/1.58  tff(c_1083, plain, (![B_198]: (k1_relat_1(B_198)='#skF_3' | ~v4_relat_1(B_198, '#skF_3') | ~v1_relat_1(B_198))), inference(resolution, [status(thm)], [c_1070, c_672])).
% 3.74/1.58  tff(c_1089, plain, (k1_relat_1('#skF_4')='#skF_3' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1068, c_1083])).
% 3.74/1.58  tff(c_1095, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_699, c_1089])).
% 3.74/1.58  tff(c_1155, plain, (![A_202, B_203, C_204]: (k1_relset_1(A_202, B_203, C_204)=k1_relat_1(C_204) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.74/1.58  tff(c_1158, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_666, c_1155])).
% 3.74/1.58  tff(c_1163, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1095, c_1158])).
% 3.74/1.58  tff(c_1041, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_3', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_703])).
% 3.74/1.58  tff(c_1166, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1163, c_1041])).
% 3.74/1.58  tff(c_1322, plain, (![B_228, C_229, A_230]: (k1_funct_1(B_228, C_229)=k1_funct_1(A_230, C_229) | ~r2_hidden(C_229, k1_relat_1(A_230)) | ~r1_partfun1(A_230, B_228) | ~r1_tarski(k1_relat_1(A_230), k1_relat_1(B_228)) | ~v1_funct_1(B_228) | ~v1_relat_1(B_228) | ~v1_funct_1(A_230) | ~v1_relat_1(A_230))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.74/1.58  tff(c_1326, plain, (![B_228, C_229]: (k1_funct_1(B_228, C_229)=k1_funct_1('#skF_4', C_229) | ~r2_hidden(C_229, '#skF_3') | ~r1_partfun1('#skF_4', B_228) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_228)) | ~v1_funct_1(B_228) | ~v1_relat_1(B_228) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1095, c_1322])).
% 3.74/1.58  tff(c_1360, plain, (![B_234, C_235]: (k1_funct_1(B_234, C_235)=k1_funct_1('#skF_4', C_235) | ~r2_hidden(C_235, '#skF_3') | ~r1_partfun1('#skF_4', B_234) | ~v1_funct_1(B_234) | ~v1_relat_1(B_234))), inference(demodulation, [status(thm), theory('equality')], [c_699, c_52, c_662, c_1095, c_1326])).
% 3.74/1.58  tff(c_1370, plain, (![B_236]: (k1_funct_1(B_236, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_236) | ~v1_funct_1(B_236) | ~v1_relat_1(B_236))), inference(resolution, [status(thm)], [c_1166, c_1360])).
% 3.74/1.58  tff(c_1377, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1042, c_1370])).
% 3.74/1.58  tff(c_1384, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_702, c_48, c_1377])).
% 3.74/1.58  tff(c_1386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1053, c_1384])).
% 3.74/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.58  
% 3.74/1.58  Inference rules
% 3.74/1.58  ----------------------
% 3.74/1.58  #Ref     : 3
% 3.74/1.58  #Sup     : 244
% 3.74/1.58  #Fact    : 0
% 3.74/1.58  #Define  : 0
% 3.74/1.58  #Split   : 7
% 3.74/1.58  #Chain   : 0
% 3.74/1.58  #Close   : 0
% 3.74/1.58  
% 3.74/1.58  Ordering : KBO
% 3.74/1.58  
% 3.74/1.58  Simplification rules
% 3.74/1.58  ----------------------
% 3.74/1.58  #Subsume      : 32
% 3.74/1.58  #Demod        : 365
% 3.74/1.58  #Tautology    : 123
% 3.74/1.58  #SimpNegUnit  : 17
% 3.74/1.58  #BackRed      : 9
% 3.74/1.59  
% 3.74/1.59  #Partial instantiations: 0
% 3.74/1.59  #Strategies tried      : 1
% 3.74/1.59  
% 3.74/1.59  Timing (in seconds)
% 3.74/1.59  ----------------------
% 3.74/1.59  Preprocessing        : 0.33
% 3.74/1.59  Parsing              : 0.17
% 3.74/1.59  CNF conversion       : 0.02
% 3.74/1.59  Main loop            : 0.47
% 3.74/1.59  Inferencing          : 0.17
% 3.74/1.59  Reduction            : 0.16
% 3.74/1.59  Demodulation         : 0.11
% 3.74/1.59  BG Simplification    : 0.03
% 3.74/1.59  Subsumption          : 0.08
% 3.74/1.59  Abstraction          : 0.02
% 3.74/1.59  MUC search           : 0.00
% 3.74/1.59  Cooper               : 0.00
% 3.74/1.59  Total                : 0.86
% 3.74/1.59  Index Insertion      : 0.00
% 3.74/1.59  Index Deletion       : 0.00
% 3.74/1.59  Index Matching       : 0.00
% 3.74/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
