%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:37 EST 2020

% Result     : Theorem 8.87s
% Output     : CNFRefutation 9.05s
% Verified   : 
% Statistics : Number of formulae       :  349 (18101 expanded)
%              Number of leaves         :   43 (5636 expanded)
%              Depth                    :   21
%              Number of atoms          :  534 (45099 expanded)
%              Number of equality atoms :  188 (11370 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_168,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_92,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_151,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_122,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_139,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_84,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_88,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_182,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_199,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_182])).

tff(c_92,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_86,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_4976,plain,(
    ! [A_432,B_433,C_434] :
      ( k2_relset_1(A_432,B_433,C_434) = k2_relat_1(C_434)
      | ~ m1_subset_1(C_434,k1_zfmisc_1(k2_zfmisc_1(A_432,B_433))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4988,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_4976])).

tff(c_5003,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4988])).

tff(c_38,plain,(
    ! [A_21] :
      ( k1_relat_1(k2_funct_1(A_21)) = k2_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    ! [A_19] :
      ( v1_funct_1(k2_funct_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_82,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_201,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_212,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_201])).

tff(c_216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_92,c_212])).

tff(c_217,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_240,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_1670,plain,(
    ! [A_216,B_217,C_218] :
      ( k2_relset_1(A_216,B_217,C_218) = k2_relat_1(C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1682,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_1670])).

tff(c_1697,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1682])).

tff(c_30,plain,(
    ! [A_19] :
      ( v1_relat_1(k2_funct_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_218,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_1342,plain,(
    ! [A_185] :
      ( k1_relat_1(k2_funct_1(A_185)) = k2_relat_1(A_185)
      | ~ v2_funct_1(A_185)
      | ~ v1_funct_1(A_185)
      | ~ v1_relat_1(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_78,plain,(
    ! [A_39] :
      ( v1_funct_2(A_39,k1_relat_1(A_39),k2_relat_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_3238,plain,(
    ! [A_309] :
      ( v1_funct_2(k2_funct_1(A_309),k2_relat_1(A_309),k2_relat_1(k2_funct_1(A_309)))
      | ~ v1_funct_1(k2_funct_1(A_309))
      | ~ v1_relat_1(k2_funct_1(A_309))
      | ~ v2_funct_1(A_309)
      | ~ v1_funct_1(A_309)
      | ~ v1_relat_1(A_309) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1342,c_78])).

tff(c_3250,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1697,c_3238])).

tff(c_3269,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_92,c_86,c_218,c_3250])).

tff(c_3276,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3269])).

tff(c_3279,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_3276])).

tff(c_3283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_92,c_3279])).

tff(c_3285,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3269])).

tff(c_24,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) = k1_xboole_0
      | k2_relat_1(A_18) != k1_xboole_0
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_222,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_199,c_24])).

tff(c_239,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_1700,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1697,c_239])).

tff(c_90,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_1591,plain,(
    ! [A_206,B_207,C_208] :
      ( k1_relset_1(A_206,B_207,C_208) = k1_relat_1(C_208)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1617,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_1591])).

tff(c_1954,plain,(
    ! [B_247,A_248,C_249] :
      ( k1_xboole_0 = B_247
      | k1_relset_1(A_248,B_247,C_249) = A_248
      | ~ v1_funct_2(C_249,A_248,B_247)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_248,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1969,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_1954])).

tff(c_1992,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1617,c_1969])).

tff(c_1993,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1700,c_1992])).

tff(c_36,plain,(
    ! [A_21] :
      ( k2_relat_1(k2_funct_1(A_21)) = k1_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1445,plain,(
    ! [A_196] :
      ( m1_subset_1(A_196,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_196),k2_relat_1(A_196))))
      | ~ v1_funct_1(A_196)
      | ~ v1_relat_1(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_3758,plain,(
    ! [A_337] :
      ( m1_subset_1(k2_funct_1(A_337),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_337)),k1_relat_1(A_337))))
      | ~ v1_funct_1(k2_funct_1(A_337))
      | ~ v1_relat_1(k2_funct_1(A_337))
      | ~ v2_funct_1(A_337)
      | ~ v1_funct_1(A_337)
      | ~ v1_relat_1(A_337) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1445])).

tff(c_3789,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1993,c_3758])).

tff(c_3812,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_92,c_86,c_3285,c_218,c_3789])).

tff(c_3839,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),'#skF_3')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3812])).

tff(c_3855,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_92,c_86,c_1697,c_3839])).

tff(c_3857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_3855])).

tff(c_3858,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_3859,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_5142,plain,(
    ! [A_442,B_443,C_444] :
      ( k1_relset_1(A_442,B_443,C_444) = k1_relat_1(C_444)
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(A_442,B_443))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_5174,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3859,c_5142])).

tff(c_5302,plain,(
    ! [B_463,C_464,A_465] :
      ( k1_xboole_0 = B_463
      | v1_funct_2(C_464,A_465,B_463)
      | k1_relset_1(A_465,B_463,C_464) != A_465
      | ~ m1_subset_1(C_464,k1_zfmisc_1(k2_zfmisc_1(A_465,B_463))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_5314,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_3859,c_5302])).

tff(c_5339,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5174,c_5314])).

tff(c_5340,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3858,c_5339])).

tff(c_5349,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5340])).

tff(c_5352,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_5349])).

tff(c_5355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_92,c_86,c_5003,c_5352])).

tff(c_5356,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5340])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5398,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5356,c_6])).

tff(c_12,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_5394,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5356,c_5356,c_12])).

tff(c_3898,plain,(
    ! [B_339,A_340] :
      ( v1_xboole_0(B_339)
      | ~ m1_subset_1(B_339,k1_zfmisc_1(A_340))
      | ~ v1_xboole_0(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3914,plain,
    ( v1_xboole_0(k2_funct_1('#skF_5'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_3859,c_3898])).

tff(c_3960,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3914])).

tff(c_5490,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5394,c_3960])).

tff(c_5494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5398,c_5490])).

tff(c_5496,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3914])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_5527,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5496,c_8])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( k1_xboole_0 = B_7
      | k1_xboole_0 = A_6
      | k2_zfmisc_1(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_5549,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5527,c_10])).

tff(c_5551,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5549])).

tff(c_5574,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5551,c_6])).

tff(c_5570,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5551,c_5551,c_12])).

tff(c_3919,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_88,c_3898])).

tff(c_3946,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3919])).

tff(c_5620,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5570,c_3946])).

tff(c_5624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5574,c_5620])).

tff(c_5625,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5549])).

tff(c_5667,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5625,c_6])).

tff(c_14,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_5664,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_3',B_7) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5625,c_5625,c_14])).

tff(c_5736,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5664,c_3946])).

tff(c_5740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5667,c_5736])).

tff(c_5742,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3919])).

tff(c_5741,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_3919])).

tff(c_5746,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_5741,c_8])).

tff(c_6107,plain,(
    ! [A_507] :
      ( A_507 = '#skF_5'
      | ~ v1_xboole_0(A_507) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5746,c_8])).

tff(c_6122,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_5742,c_6107])).

tff(c_5768,plain,(
    ! [B_7,A_6] :
      ( B_7 = '#skF_5'
      | A_6 = '#skF_5'
      | k2_zfmisc_1(A_6,B_7) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5746,c_5746,c_5746,c_10])).

tff(c_6138,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_6122,c_5768])).

tff(c_6178,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6138])).

tff(c_16,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_46,plain,(
    ! [A_31] :
      ( v1_funct_2(k1_xboole_0,A_31,k1_xboole_0)
      | k1_xboole_0 = A_31
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_31,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_96,plain,(
    ! [A_31] :
      ( v1_funct_2(k1_xboole_0,A_31,k1_xboole_0)
      | k1_xboole_0 = A_31 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_46])).

tff(c_5756,plain,(
    ! [A_31] :
      ( v1_funct_2('#skF_5',A_31,'#skF_5')
      | A_31 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5746,c_5746,c_5746,c_96])).

tff(c_6385,plain,(
    ! [A_519] :
      ( v1_funct_2('#skF_3',A_519,'#skF_3')
      | A_519 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6178,c_6178,c_6178,c_5756])).

tff(c_5865,plain,(
    ! [A_491] :
      ( A_491 = '#skF_5'
      | ~ v1_xboole_0(A_491) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5746,c_8])).

tff(c_5872,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_5742,c_5865])).

tff(c_5888,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_5872,c_5768])).

tff(c_5890,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5888])).

tff(c_5902,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5890,c_5741])).

tff(c_5757,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5746,c_5746,c_12])).

tff(c_5893,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5890,c_5890,c_5757])).

tff(c_5864,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3914])).

tff(c_5991,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5893,c_5864])).

tff(c_5994,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5902,c_5991])).

tff(c_5995,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5888])).

tff(c_6008,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5995,c_5741])).

tff(c_5758,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_5',B_7) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5746,c_5746,c_14])).

tff(c_6000,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_4',B_7) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5995,c_5995,c_5758])).

tff(c_6088,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6000,c_5864])).

tff(c_6091,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6008,c_6088])).

tff(c_6092,plain,(
    v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3914])).

tff(c_6121,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6092,c_6107])).

tff(c_6143,plain,(
    ~ v1_funct_2('#skF_5','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6121,c_3858])).

tff(c_6179,plain,(
    ~ v1_funct_2('#skF_3','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6178,c_6143])).

tff(c_6389,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6385,c_6179])).

tff(c_6196,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6178,c_90])).

tff(c_6405,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6389,c_6389,c_6196])).

tff(c_6393,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6389,c_6389,c_6179])).

tff(c_6509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6405,c_6393])).

tff(c_6510,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6138])).

tff(c_6536,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6510,c_5741])).

tff(c_5812,plain,(
    ! [B_489] : k2_zfmisc_1('#skF_5',B_489) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5746,c_5746,c_14])).

tff(c_72,plain,(
    ! [A_35,B_36] : m1_subset_1('#skF_2'(A_35,B_36),k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_5817,plain,(
    ! [B_489] : m1_subset_1('#skF_2'('#skF_5',B_489),k1_zfmisc_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5812,c_72])).

tff(c_6814,plain,(
    ! [B_546] : m1_subset_1('#skF_2'('#skF_4',B_546),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6510,c_6510,c_5817])).

tff(c_18,plain,(
    ! [B_11,A_9] :
      ( v1_xboole_0(B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_9))
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6824,plain,(
    ! [B_546] :
      ( v1_xboole_0('#skF_2'('#skF_4',B_546))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6814,c_18])).

tff(c_6839,plain,(
    ! [B_547] : v1_xboole_0('#skF_2'('#skF_4',B_547)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6536,c_6824])).

tff(c_5760,plain,(
    ! [A_5] :
      ( A_5 = '#skF_5'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5746,c_8])).

tff(c_6526,plain,(
    ! [A_5] :
      ( A_5 = '#skF_4'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6510,c_5760])).

tff(c_6852,plain,(
    ! [B_548] : '#skF_2'('#skF_4',B_548) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6839,c_6526])).

tff(c_62,plain,(
    ! [A_35,B_36] : v1_funct_2('#skF_2'(A_35,B_36),A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_6863,plain,(
    ! [B_548] : v1_funct_2('#skF_4','#skF_4',B_548) ),
    inference(superposition,[status(thm),theory(equality)],[c_6852,c_62])).

tff(c_6522,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6510,c_6143])).

tff(c_6891,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6863,c_6522])).

tff(c_6893,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_14556,plain,(
    ! [A_1102,B_1103,C_1104] :
      ( k2_relset_1(A_1102,B_1103,C_1104) = k2_relat_1(C_1104)
      | ~ m1_subset_1(C_1104,k1_zfmisc_1(k2_zfmisc_1(A_1102,B_1103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_14565,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_14556])).

tff(c_14579,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_6893,c_14565])).

tff(c_14618,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14579,c_6])).

tff(c_14614,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14579,c_14579,c_12])).

tff(c_13968,plain,(
    ! [B_1047,A_1048] :
      ( v1_xboole_0(B_1047)
      | ~ m1_subset_1(B_1047,k1_zfmisc_1(A_1048))
      | ~ v1_xboole_0(A_1048) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14005,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_88,c_13968])).

tff(c_14032,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_14005])).

tff(c_14773,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14614,c_14032])).

tff(c_14777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14618,c_14773])).

tff(c_14778,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_14005])).

tff(c_14809,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_14778,c_8])).

tff(c_7387,plain,(
    ! [A_601,B_602,C_603] :
      ( k2_relset_1(A_601,B_602,C_603) = k2_relat_1(C_603)
      | ~ m1_subset_1(C_603,k1_zfmisc_1(k2_zfmisc_1(A_601,B_602))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_7396,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_7387])).

tff(c_7410,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6893,c_84,c_7396])).

tff(c_7442,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7410,c_6])).

tff(c_7438,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7410,c_7410,c_12])).

tff(c_6947,plain,(
    ! [B_554,A_555] :
      ( v1_xboole_0(B_554)
      | ~ m1_subset_1(B_554,k1_zfmisc_1(A_555))
      | ~ v1_xboole_0(A_555) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6974,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_88,c_6947])).

tff(c_7001,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6974])).

tff(c_7561,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7438,c_7001])).

tff(c_7565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7442,c_7561])).

tff(c_7566,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_6974])).

tff(c_7571,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_7566,c_8])).

tff(c_7577,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7571,c_6893])).

tff(c_200,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_182])).

tff(c_226,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_200,c_24])).

tff(c_6926,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_7576,plain,(
    k2_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7571,c_7571,c_6926])).

tff(c_7605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7577,c_7576])).

tff(c_7607,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_14817,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14809,c_14809,c_7607])).

tff(c_14828,plain,(
    ! [A_8] : m1_subset_1('#skF_5',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14809,c_16])).

tff(c_15851,plain,(
    ! [A_1171,B_1172,C_1173] :
      ( k2_relset_1(A_1171,B_1172,C_1173) = k2_relat_1(C_1173)
      | ~ m1_subset_1(C_1173,k1_zfmisc_1(k2_zfmisc_1(A_1171,B_1172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_15861,plain,(
    ! [A_1171,B_1172] : k2_relset_1(A_1171,B_1172,'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14828,c_15851])).

tff(c_15882,plain,(
    ! [A_1174,B_1175] : k2_relset_1(A_1174,B_1175,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14817,c_15861])).

tff(c_15886,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_15882,c_84])).

tff(c_7616,plain,(
    ! [A_612,B_613] : m1_subset_1('#skF_2'(A_612,B_613),k1_zfmisc_1(k2_zfmisc_1(A_612,B_613))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_7625,plain,(
    ! [B_7] : m1_subset_1('#skF_2'(k1_xboole_0,B_7),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_7616])).

tff(c_13974,plain,(
    ! [B_7] :
      ( v1_xboole_0('#skF_2'(k1_xboole_0,B_7))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_7625,c_13968])).

tff(c_13996,plain,(
    ! [B_7] : v1_xboole_0('#skF_2'(k1_xboole_0,B_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13974])).

tff(c_15570,plain,(
    ! [B_1157] : v1_xboole_0('#skF_2'('#skF_5',B_1157)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14809,c_13996])).

tff(c_14829,plain,(
    ! [A_5] :
      ( A_5 = '#skF_5'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14809,c_8])).

tff(c_15622,plain,(
    ! [B_1160] : '#skF_2'('#skF_5',B_1160) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_15570,c_14829])).

tff(c_15633,plain,(
    ! [B_1160] : v1_funct_2('#skF_5','#skF_5',B_1160) ),
    inference(superposition,[status(thm),theory(equality)],[c_15622,c_62])).

tff(c_15898,plain,(
    ! [B_1160] : v1_funct_2('#skF_4','#skF_4',B_1160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15886,c_15886,c_15633])).

tff(c_15196,plain,(
    ! [A_1136,B_1137,C_1138] :
      ( k2_relset_1(A_1136,B_1137,C_1138) = k2_relat_1(C_1138)
      | ~ m1_subset_1(C_1138,k1_zfmisc_1(k2_zfmisc_1(A_1136,B_1137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_15203,plain,(
    ! [A_1136,B_1137] : k2_relset_1(A_1136,B_1137,'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14828,c_15196])).

tff(c_15225,plain,(
    ! [A_1139,B_1140] : k2_relset_1(A_1139,B_1140,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14817,c_15203])).

tff(c_15229,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_15225,c_84])).

tff(c_15259,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15229,c_14778])).

tff(c_14827,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_5',B_7) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14809,c_14809,c_14])).

tff(c_15246,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_4',B_7) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15229,c_15229,c_14827])).

tff(c_8045,plain,(
    ! [A_659,B_660,C_661] :
      ( k2_relset_1(A_659,B_660,C_661) = k2_relat_1(C_661)
      | ~ m1_subset_1(C_661,k1_zfmisc_1(k2_zfmisc_1(A_659,B_660))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_8054,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_8045])).

tff(c_8068,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_6893,c_8054])).

tff(c_8099,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8068,c_6])).

tff(c_8095,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8068,c_8068,c_12])).

tff(c_7643,plain,(
    ! [B_616,A_617] :
      ( v1_xboole_0(B_616)
      | ~ m1_subset_1(B_616,k1_zfmisc_1(A_617))
      | ~ v1_xboole_0(A_617) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_7676,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_88,c_7643])).

tff(c_7724,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7676])).

tff(c_8248,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8095,c_7724])).

tff(c_8252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8099,c_8248])).

tff(c_8254,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7676])).

tff(c_8253,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_7676])).

tff(c_8258,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8253,c_8])).

tff(c_8385,plain,(
    ! [A_681] :
      ( A_681 = '#skF_5'
      | ~ v1_xboole_0(A_681) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8258,c_8])).

tff(c_8400,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8254,c_8385])).

tff(c_8744,plain,(
    ! [B_706,A_707] :
      ( B_706 = '#skF_5'
      | A_707 = '#skF_5'
      | k2_zfmisc_1(A_707,B_706) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8258,c_8258,c_8258,c_10])).

tff(c_8754,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_8400,c_8744])).

tff(c_8795,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8754])).

tff(c_8267,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8258,c_8258,c_7607])).

tff(c_8819,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8795,c_8795,c_8267])).

tff(c_8278,plain,(
    ! [A_8] : m1_subset_1('#skF_5',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8258,c_16])).

tff(c_8904,plain,(
    ! [A_715] : m1_subset_1('#skF_3',k1_zfmisc_1(A_715)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8795,c_8278])).

tff(c_44,plain,(
    ! [A_28,B_29,C_30] :
      ( k2_relset_1(A_28,B_29,C_30) = k2_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_8908,plain,(
    ! [A_28,B_29] : k2_relset_1(A_28,B_29,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8904,c_44])).

tff(c_9147,plain,(
    ! [A_728,B_729] : k2_relset_1(A_728,B_729,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8819,c_8908])).

tff(c_8825,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8795,c_84])).

tff(c_9151,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_9147,c_8825])).

tff(c_8276,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8258,c_8258,c_12])).

tff(c_8813,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8795,c_8795,c_8276])).

tff(c_7642,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_8822,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8795,c_7642])).

tff(c_9144,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8813,c_8822])).

tff(c_9159,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9151,c_9151,c_9144])).

tff(c_8824,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8795,c_199])).

tff(c_9179,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9151,c_8824])).

tff(c_8828,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8795,c_92])).

tff(c_9180,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9151,c_8828])).

tff(c_8827,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8795,c_86])).

tff(c_9181,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9151,c_8827])).

tff(c_8823,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8795,c_218])).

tff(c_9177,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9151,c_8823])).

tff(c_7606,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_8268,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8258,c_8258,c_7606])).

tff(c_8818,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8795,c_8795,c_8268])).

tff(c_9175,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9151,c_9151,c_8818])).

tff(c_8522,plain,(
    ! [A_690] :
      ( k2_relat_1(k2_funct_1(A_690)) = k1_relat_1(A_690)
      | ~ v2_funct_1(A_690)
      | ~ v1_funct_1(A_690)
      | ~ v1_relat_1(A_690) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_11183,plain,(
    ! [A_866] :
      ( v1_funct_2(k2_funct_1(A_866),k1_relat_1(k2_funct_1(A_866)),k1_relat_1(A_866))
      | ~ v1_funct_1(k2_funct_1(A_866))
      | ~ v1_relat_1(k2_funct_1(A_866))
      | ~ v2_funct_1(A_866)
      | ~ v1_funct_1(A_866)
      | ~ v1_relat_1(A_866) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8522,c_78])).

tff(c_11192,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9175,c_11183])).

tff(c_11204,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9179,c_9180,c_9181,c_9177,c_11192])).

tff(c_11205,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_11204])).

tff(c_11208,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_11205])).

tff(c_11212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9179,c_9180,c_11208])).

tff(c_11214,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_11204])).

tff(c_8277,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_5',B_7) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8258,c_8258,c_14])).

tff(c_8811,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_3',B_7) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8795,c_8795,c_8277])).

tff(c_9162,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_4',B_7) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9151,c_9151,c_8811])).

tff(c_8274,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) = '#skF_5'
      | k2_relat_1(A_18) != '#skF_5'
      | ~ v1_relat_1(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8258,c_8258,c_24])).

tff(c_8798,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) = '#skF_3'
      | k2_relat_1(A_18) != '#skF_3'
      | ~ v1_relat_1(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8795,c_8795,c_8274])).

tff(c_9654,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) = '#skF_4'
      | k2_relat_1(A_18) != '#skF_4'
      | ~ v1_relat_1(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9151,c_9151,c_8798])).

tff(c_11221,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = '#skF_4'
    | k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_11214,c_9654])).

tff(c_11263,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_11221])).

tff(c_11269,plain,
    ( k1_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_11263])).

tff(c_11275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9179,c_9180,c_9181,c_9175,c_11269])).

tff(c_11276,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11221])).

tff(c_76,plain,(
    ! [A_39] :
      ( m1_subset_1(A_39,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_39),k2_relat_1(A_39))))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_11303,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11276,c_76])).

tff(c_11330,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11214,c_9177,c_9162,c_11303])).

tff(c_11332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9159,c_11330])).

tff(c_11333,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8754])).

tff(c_11378,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_4',B_7) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11333,c_11333,c_8277])).

tff(c_11389,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11333,c_7642])).

tff(c_11692,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11378,c_11389])).

tff(c_11391,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11333,c_199])).

tff(c_11395,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11333,c_92])).

tff(c_11394,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11333,c_86])).

tff(c_11390,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11333,c_218])).

tff(c_11385,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11333,c_11333,c_8268])).

tff(c_13440,plain,(
    ! [A_1015] :
      ( v1_funct_2(k2_funct_1(A_1015),k1_relat_1(k2_funct_1(A_1015)),k1_relat_1(A_1015))
      | ~ v1_funct_1(k2_funct_1(A_1015))
      | ~ v1_relat_1(k2_funct_1(A_1015))
      | ~ v2_funct_1(A_1015)
      | ~ v1_funct_1(A_1015)
      | ~ v1_relat_1(A_1015) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8522,c_78])).

tff(c_13449,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11385,c_13440])).

tff(c_13461,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11391,c_11395,c_11394,c_11390,c_13449])).

tff(c_13462,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_13461])).

tff(c_13465,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_13462])).

tff(c_13469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11391,c_11395,c_13465])).

tff(c_13471,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_13461])).

tff(c_11380,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11333,c_11333,c_8276])).

tff(c_11386,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11333,c_11333,c_8267])).

tff(c_26,plain,(
    ! [A_18] :
      ( k2_relat_1(A_18) = k1_xboole_0
      | k1_relat_1(A_18) != k1_xboole_0
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8270,plain,(
    ! [A_18] :
      ( k2_relat_1(A_18) = '#skF_5'
      | k1_relat_1(A_18) != '#skF_5'
      | ~ v1_relat_1(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8258,c_8258,c_26])).

tff(c_11364,plain,(
    ! [A_18] :
      ( k2_relat_1(A_18) = '#skF_4'
      | k1_relat_1(A_18) != '#skF_4'
      | ~ v1_relat_1(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11333,c_11333,c_8270])).

tff(c_13479,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = '#skF_4'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_13471,c_11364])).

tff(c_13535,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_13479])).

tff(c_13538,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_13535])).

tff(c_13541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11391,c_11395,c_11394,c_11386,c_13538])).

tff(c_13542,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_13479])).

tff(c_13567,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13542,c_76])).

tff(c_13599,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13471,c_11390,c_11380,c_13567])).

tff(c_13601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11692,c_13599])).

tff(c_13603,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_13993,plain,
    ( v1_xboole_0(k2_funct_1('#skF_5'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_13603,c_13968])).

tff(c_14929,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_13993])).

tff(c_15457,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15246,c_14929])).

tff(c_15460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15259,c_15457])).

tff(c_15461,plain,(
    v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_13993])).

tff(c_15474,plain,(
    ! [A_1153] :
      ( A_1153 = '#skF_5'
      | ~ v1_xboole_0(A_1153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14809,c_8])).

tff(c_15488,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_15461,c_15474])).

tff(c_13602,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_15495,plain,(
    ~ v1_funct_2('#skF_5','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15488,c_13602])).

tff(c_15902,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15886,c_15495])).

tff(c_16155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15898,c_15902])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n024.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 17:48:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.87/3.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.05/3.42  
% 9.05/3.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.05/3.42  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 9.05/3.42  
% 9.05/3.42  %Foreground sorts:
% 9.05/3.42  
% 9.05/3.42  
% 9.05/3.42  %Background operators:
% 9.05/3.42  
% 9.05/3.42  
% 9.05/3.42  %Foreground operators:
% 9.05/3.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.05/3.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.05/3.42  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.05/3.42  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.05/3.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.05/3.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.05/3.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.05/3.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.05/3.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.05/3.42  tff('#skF_5', type, '#skF_5': $i).
% 9.05/3.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.05/3.42  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.05/3.42  tff('#skF_3', type, '#skF_3': $i).
% 9.05/3.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.05/3.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.05/3.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.05/3.42  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.05/3.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.05/3.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.05/3.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.05/3.42  tff('#skF_4', type, '#skF_4': $i).
% 9.05/3.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.05/3.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.05/3.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.05/3.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.05/3.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.05/3.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.05/3.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.05/3.42  
% 9.05/3.45  tff(f_168, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 9.05/3.45  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.05/3.45  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.05/3.45  tff(f_92, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 9.05/3.45  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.05/3.45  tff(f_151, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 9.05/3.45  tff(f_70, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 9.05/3.45  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.05/3.45  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.05/3.45  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.05/3.45  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.05/3.45  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 9.05/3.45  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.05/3.45  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 9.05/3.45  tff(f_139, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 9.05/3.45  tff(c_84, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_168])).
% 9.05/3.45  tff(c_88, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 9.05/3.45  tff(c_182, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.05/3.45  tff(c_199, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_182])).
% 9.05/3.45  tff(c_92, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 9.05/3.45  tff(c_86, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 9.05/3.45  tff(c_4976, plain, (![A_432, B_433, C_434]: (k2_relset_1(A_432, B_433, C_434)=k2_relat_1(C_434) | ~m1_subset_1(C_434, k1_zfmisc_1(k2_zfmisc_1(A_432, B_433))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.05/3.45  tff(c_4988, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_4976])).
% 9.05/3.45  tff(c_5003, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4988])).
% 9.05/3.45  tff(c_38, plain, (![A_21]: (k1_relat_1(k2_funct_1(A_21))=k2_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.05/3.45  tff(c_28, plain, (![A_19]: (v1_funct_1(k2_funct_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.05/3.45  tff(c_82, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 9.05/3.45  tff(c_201, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_82])).
% 9.05/3.45  tff(c_212, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_201])).
% 9.05/3.45  tff(c_216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_199, c_92, c_212])).
% 9.05/3.45  tff(c_217, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_82])).
% 9.05/3.45  tff(c_240, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_217])).
% 9.05/3.45  tff(c_1670, plain, (![A_216, B_217, C_218]: (k2_relset_1(A_216, B_217, C_218)=k2_relat_1(C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.05/3.45  tff(c_1682, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_1670])).
% 9.05/3.45  tff(c_1697, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1682])).
% 9.05/3.45  tff(c_30, plain, (![A_19]: (v1_relat_1(k2_funct_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.05/3.45  tff(c_218, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_82])).
% 9.05/3.45  tff(c_1342, plain, (![A_185]: (k1_relat_1(k2_funct_1(A_185))=k2_relat_1(A_185) | ~v2_funct_1(A_185) | ~v1_funct_1(A_185) | ~v1_relat_1(A_185))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.05/3.45  tff(c_78, plain, (![A_39]: (v1_funct_2(A_39, k1_relat_1(A_39), k2_relat_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_151])).
% 9.05/3.45  tff(c_3238, plain, (![A_309]: (v1_funct_2(k2_funct_1(A_309), k2_relat_1(A_309), k2_relat_1(k2_funct_1(A_309))) | ~v1_funct_1(k2_funct_1(A_309)) | ~v1_relat_1(k2_funct_1(A_309)) | ~v2_funct_1(A_309) | ~v1_funct_1(A_309) | ~v1_relat_1(A_309))), inference(superposition, [status(thm), theory('equality')], [c_1342, c_78])).
% 9.05/3.45  tff(c_3250, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1697, c_3238])).
% 9.05/3.45  tff(c_3269, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_92, c_86, c_218, c_3250])).
% 9.05/3.45  tff(c_3276, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_3269])).
% 9.05/3.45  tff(c_3279, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_3276])).
% 9.05/3.45  tff(c_3283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_199, c_92, c_3279])).
% 9.05/3.45  tff(c_3285, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_3269])).
% 9.05/3.45  tff(c_24, plain, (![A_18]: (k1_relat_1(A_18)=k1_xboole_0 | k2_relat_1(A_18)!=k1_xboole_0 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.05/3.45  tff(c_222, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_199, c_24])).
% 9.05/3.45  tff(c_239, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_222])).
% 9.05/3.45  tff(c_1700, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1697, c_239])).
% 9.05/3.45  tff(c_90, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_168])).
% 9.05/3.45  tff(c_1591, plain, (![A_206, B_207, C_208]: (k1_relset_1(A_206, B_207, C_208)=k1_relat_1(C_208) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.05/3.45  tff(c_1617, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_1591])).
% 9.05/3.45  tff(c_1954, plain, (![B_247, A_248, C_249]: (k1_xboole_0=B_247 | k1_relset_1(A_248, B_247, C_249)=A_248 | ~v1_funct_2(C_249, A_248, B_247) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_248, B_247))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.05/3.45  tff(c_1969, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_88, c_1954])).
% 9.05/3.45  tff(c_1992, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1617, c_1969])).
% 9.05/3.45  tff(c_1993, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1700, c_1992])).
% 9.05/3.45  tff(c_36, plain, (![A_21]: (k2_relat_1(k2_funct_1(A_21))=k1_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.05/3.45  tff(c_1445, plain, (![A_196]: (m1_subset_1(A_196, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_196), k2_relat_1(A_196)))) | ~v1_funct_1(A_196) | ~v1_relat_1(A_196))), inference(cnfTransformation, [status(thm)], [f_151])).
% 9.05/3.45  tff(c_3758, plain, (![A_337]: (m1_subset_1(k2_funct_1(A_337), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_337)), k1_relat_1(A_337)))) | ~v1_funct_1(k2_funct_1(A_337)) | ~v1_relat_1(k2_funct_1(A_337)) | ~v2_funct_1(A_337) | ~v1_funct_1(A_337) | ~v1_relat_1(A_337))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1445])).
% 9.05/3.45  tff(c_3789, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1993, c_3758])).
% 9.05/3.45  tff(c_3812, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_92, c_86, c_3285, c_218, c_3789])).
% 9.05/3.45  tff(c_3839, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), '#skF_3'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_38, c_3812])).
% 9.05/3.45  tff(c_3855, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_92, c_86, c_1697, c_3839])).
% 9.05/3.45  tff(c_3857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_3855])).
% 9.05/3.45  tff(c_3858, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_217])).
% 9.05/3.45  tff(c_3859, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_217])).
% 9.05/3.45  tff(c_5142, plain, (![A_442, B_443, C_444]: (k1_relset_1(A_442, B_443, C_444)=k1_relat_1(C_444) | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(A_442, B_443))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.05/3.45  tff(c_5174, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_3859, c_5142])).
% 9.05/3.45  tff(c_5302, plain, (![B_463, C_464, A_465]: (k1_xboole_0=B_463 | v1_funct_2(C_464, A_465, B_463) | k1_relset_1(A_465, B_463, C_464)!=A_465 | ~m1_subset_1(C_464, k1_zfmisc_1(k2_zfmisc_1(A_465, B_463))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.05/3.45  tff(c_5314, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_3859, c_5302])).
% 9.05/3.45  tff(c_5339, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5174, c_5314])).
% 9.05/3.45  tff(c_5340, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3858, c_5339])).
% 9.05/3.45  tff(c_5349, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_5340])).
% 9.05/3.45  tff(c_5352, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_38, c_5349])).
% 9.05/3.45  tff(c_5355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_199, c_92, c_86, c_5003, c_5352])).
% 9.05/3.45  tff(c_5356, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_5340])).
% 9.05/3.45  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.05/3.45  tff(c_5398, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5356, c_6])).
% 9.05/3.45  tff(c_12, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.05/3.45  tff(c_5394, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5356, c_5356, c_12])).
% 9.05/3.45  tff(c_3898, plain, (![B_339, A_340]: (v1_xboole_0(B_339) | ~m1_subset_1(B_339, k1_zfmisc_1(A_340)) | ~v1_xboole_0(A_340))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.05/3.45  tff(c_3914, plain, (v1_xboole_0(k2_funct_1('#skF_5')) | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_3859, c_3898])).
% 9.05/3.45  tff(c_3960, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_3914])).
% 9.05/3.45  tff(c_5490, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5394, c_3960])).
% 9.05/3.45  tff(c_5494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5398, c_5490])).
% 9.05/3.45  tff(c_5496, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_3914])).
% 9.05/3.45  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.05/3.45  tff(c_5527, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_5496, c_8])).
% 9.05/3.45  tff(c_10, plain, (![B_7, A_6]: (k1_xboole_0=B_7 | k1_xboole_0=A_6 | k2_zfmisc_1(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.05/3.45  tff(c_5549, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5527, c_10])).
% 9.05/3.45  tff(c_5551, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_5549])).
% 9.05/3.45  tff(c_5574, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5551, c_6])).
% 9.05/3.45  tff(c_5570, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5551, c_5551, c_12])).
% 9.05/3.45  tff(c_3919, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_88, c_3898])).
% 9.05/3.45  tff(c_3946, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_3919])).
% 9.05/3.45  tff(c_5620, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5570, c_3946])).
% 9.05/3.45  tff(c_5624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5574, c_5620])).
% 9.05/3.45  tff(c_5625, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_5549])).
% 9.05/3.45  tff(c_5667, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5625, c_6])).
% 9.05/3.45  tff(c_14, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.05/3.45  tff(c_5664, plain, (![B_7]: (k2_zfmisc_1('#skF_3', B_7)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5625, c_5625, c_14])).
% 9.05/3.45  tff(c_5736, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5664, c_3946])).
% 9.05/3.45  tff(c_5740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5667, c_5736])).
% 9.05/3.45  tff(c_5742, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_3919])).
% 9.05/3.45  tff(c_5741, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_3919])).
% 9.05/3.45  tff(c_5746, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_5741, c_8])).
% 9.05/3.45  tff(c_6107, plain, (![A_507]: (A_507='#skF_5' | ~v1_xboole_0(A_507))), inference(demodulation, [status(thm), theory('equality')], [c_5746, c_8])).
% 9.05/3.45  tff(c_6122, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_5742, c_6107])).
% 9.05/3.45  tff(c_5768, plain, (![B_7, A_6]: (B_7='#skF_5' | A_6='#skF_5' | k2_zfmisc_1(A_6, B_7)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5746, c_5746, c_5746, c_10])).
% 9.05/3.45  tff(c_6138, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_6122, c_5768])).
% 9.05/3.45  tff(c_6178, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_6138])).
% 9.05/3.45  tff(c_16, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.05/3.45  tff(c_46, plain, (![A_31]: (v1_funct_2(k1_xboole_0, A_31, k1_xboole_0) | k1_xboole_0=A_31 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_31, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.05/3.45  tff(c_96, plain, (![A_31]: (v1_funct_2(k1_xboole_0, A_31, k1_xboole_0) | k1_xboole_0=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_46])).
% 9.05/3.45  tff(c_5756, plain, (![A_31]: (v1_funct_2('#skF_5', A_31, '#skF_5') | A_31='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5746, c_5746, c_5746, c_96])).
% 9.05/3.45  tff(c_6385, plain, (![A_519]: (v1_funct_2('#skF_3', A_519, '#skF_3') | A_519='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6178, c_6178, c_6178, c_5756])).
% 9.05/3.45  tff(c_5865, plain, (![A_491]: (A_491='#skF_5' | ~v1_xboole_0(A_491))), inference(demodulation, [status(thm), theory('equality')], [c_5746, c_8])).
% 9.05/3.45  tff(c_5872, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_5742, c_5865])).
% 9.05/3.45  tff(c_5888, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_5872, c_5768])).
% 9.05/3.45  tff(c_5890, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_5888])).
% 9.05/3.45  tff(c_5902, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5890, c_5741])).
% 9.05/3.45  tff(c_5757, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5746, c_5746, c_12])).
% 9.05/3.45  tff(c_5893, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5890, c_5890, c_5757])).
% 9.05/3.45  tff(c_5864, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_3914])).
% 9.05/3.45  tff(c_5991, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5893, c_5864])).
% 9.05/3.45  tff(c_5994, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5902, c_5991])).
% 9.05/3.45  tff(c_5995, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_5888])).
% 9.05/3.45  tff(c_6008, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5995, c_5741])).
% 9.05/3.45  tff(c_5758, plain, (![B_7]: (k2_zfmisc_1('#skF_5', B_7)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5746, c_5746, c_14])).
% 9.05/3.45  tff(c_6000, plain, (![B_7]: (k2_zfmisc_1('#skF_4', B_7)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5995, c_5995, c_5758])).
% 9.05/3.45  tff(c_6088, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6000, c_5864])).
% 9.05/3.45  tff(c_6091, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6008, c_6088])).
% 9.05/3.45  tff(c_6092, plain, (v1_xboole_0(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_3914])).
% 9.05/3.45  tff(c_6121, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_6092, c_6107])).
% 9.05/3.45  tff(c_6143, plain, (~v1_funct_2('#skF_5', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6121, c_3858])).
% 9.05/3.45  tff(c_6179, plain, (~v1_funct_2('#skF_3', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6178, c_6143])).
% 9.05/3.45  tff(c_6389, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_6385, c_6179])).
% 9.05/3.45  tff(c_6196, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6178, c_90])).
% 9.05/3.45  tff(c_6405, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6389, c_6389, c_6196])).
% 9.05/3.45  tff(c_6393, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6389, c_6389, c_6179])).
% 9.05/3.45  tff(c_6509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6405, c_6393])).
% 9.05/3.45  tff(c_6510, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_6138])).
% 9.05/3.45  tff(c_6536, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6510, c_5741])).
% 9.05/3.45  tff(c_5812, plain, (![B_489]: (k2_zfmisc_1('#skF_5', B_489)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5746, c_5746, c_14])).
% 9.05/3.45  tff(c_72, plain, (![A_35, B_36]: (m1_subset_1('#skF_2'(A_35, B_36), k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.05/3.45  tff(c_5817, plain, (![B_489]: (m1_subset_1('#skF_2'('#skF_5', B_489), k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_5812, c_72])).
% 9.05/3.45  tff(c_6814, plain, (![B_546]: (m1_subset_1('#skF_2'('#skF_4', B_546), k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6510, c_6510, c_5817])).
% 9.05/3.45  tff(c_18, plain, (![B_11, A_9]: (v1_xboole_0(B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_9)) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.05/3.45  tff(c_6824, plain, (![B_546]: (v1_xboole_0('#skF_2'('#skF_4', B_546)) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_6814, c_18])).
% 9.05/3.45  tff(c_6839, plain, (![B_547]: (v1_xboole_0('#skF_2'('#skF_4', B_547)))), inference(demodulation, [status(thm), theory('equality')], [c_6536, c_6824])).
% 9.05/3.45  tff(c_5760, plain, (![A_5]: (A_5='#skF_5' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_5746, c_8])).
% 9.05/3.45  tff(c_6526, plain, (![A_5]: (A_5='#skF_4' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_6510, c_5760])).
% 9.05/3.45  tff(c_6852, plain, (![B_548]: ('#skF_2'('#skF_4', B_548)='#skF_4')), inference(resolution, [status(thm)], [c_6839, c_6526])).
% 9.05/3.45  tff(c_62, plain, (![A_35, B_36]: (v1_funct_2('#skF_2'(A_35, B_36), A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.05/3.45  tff(c_6863, plain, (![B_548]: (v1_funct_2('#skF_4', '#skF_4', B_548))), inference(superposition, [status(thm), theory('equality')], [c_6852, c_62])).
% 9.05/3.45  tff(c_6522, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6510, c_6143])).
% 9.05/3.45  tff(c_6891, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6863, c_6522])).
% 9.05/3.45  tff(c_6893, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_222])).
% 9.05/3.45  tff(c_14556, plain, (![A_1102, B_1103, C_1104]: (k2_relset_1(A_1102, B_1103, C_1104)=k2_relat_1(C_1104) | ~m1_subset_1(C_1104, k1_zfmisc_1(k2_zfmisc_1(A_1102, B_1103))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.05/3.45  tff(c_14565, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_14556])).
% 9.05/3.45  tff(c_14579, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_6893, c_14565])).
% 9.05/3.45  tff(c_14618, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14579, c_6])).
% 9.05/3.45  tff(c_14614, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14579, c_14579, c_12])).
% 9.05/3.45  tff(c_13968, plain, (![B_1047, A_1048]: (v1_xboole_0(B_1047) | ~m1_subset_1(B_1047, k1_zfmisc_1(A_1048)) | ~v1_xboole_0(A_1048))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.05/3.45  tff(c_14005, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_88, c_13968])).
% 9.05/3.45  tff(c_14032, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_14005])).
% 9.05/3.45  tff(c_14773, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14614, c_14032])).
% 9.05/3.45  tff(c_14777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14618, c_14773])).
% 9.05/3.45  tff(c_14778, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_14005])).
% 9.05/3.45  tff(c_14809, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_14778, c_8])).
% 9.05/3.45  tff(c_7387, plain, (![A_601, B_602, C_603]: (k2_relset_1(A_601, B_602, C_603)=k2_relat_1(C_603) | ~m1_subset_1(C_603, k1_zfmisc_1(k2_zfmisc_1(A_601, B_602))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.05/3.45  tff(c_7396, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_7387])).
% 9.05/3.45  tff(c_7410, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6893, c_84, c_7396])).
% 9.05/3.45  tff(c_7442, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7410, c_6])).
% 9.05/3.45  tff(c_7438, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7410, c_7410, c_12])).
% 9.05/3.45  tff(c_6947, plain, (![B_554, A_555]: (v1_xboole_0(B_554) | ~m1_subset_1(B_554, k1_zfmisc_1(A_555)) | ~v1_xboole_0(A_555))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.05/3.45  tff(c_6974, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_88, c_6947])).
% 9.05/3.45  tff(c_7001, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_6974])).
% 9.05/3.45  tff(c_7561, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7438, c_7001])).
% 9.05/3.45  tff(c_7565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7442, c_7561])).
% 9.05/3.45  tff(c_7566, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_6974])).
% 9.05/3.45  tff(c_7571, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_7566, c_8])).
% 9.05/3.45  tff(c_7577, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7571, c_6893])).
% 9.05/3.45  tff(c_200, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_182])).
% 9.05/3.45  tff(c_226, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_200, c_24])).
% 9.05/3.45  tff(c_6926, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_226])).
% 9.05/3.45  tff(c_7576, plain, (k2_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7571, c_7571, c_6926])).
% 9.05/3.45  tff(c_7605, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7577, c_7576])).
% 9.05/3.45  tff(c_7607, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_226])).
% 9.05/3.45  tff(c_14817, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_14809, c_14809, c_7607])).
% 9.05/3.45  tff(c_14828, plain, (![A_8]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_14809, c_16])).
% 9.05/3.45  tff(c_15851, plain, (![A_1171, B_1172, C_1173]: (k2_relset_1(A_1171, B_1172, C_1173)=k2_relat_1(C_1173) | ~m1_subset_1(C_1173, k1_zfmisc_1(k2_zfmisc_1(A_1171, B_1172))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.05/3.45  tff(c_15861, plain, (![A_1171, B_1172]: (k2_relset_1(A_1171, B_1172, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_14828, c_15851])).
% 9.05/3.45  tff(c_15882, plain, (![A_1174, B_1175]: (k2_relset_1(A_1174, B_1175, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14817, c_15861])).
% 9.05/3.45  tff(c_15886, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_15882, c_84])).
% 9.05/3.45  tff(c_7616, plain, (![A_612, B_613]: (m1_subset_1('#skF_2'(A_612, B_613), k1_zfmisc_1(k2_zfmisc_1(A_612, B_613))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.05/3.45  tff(c_7625, plain, (![B_7]: (m1_subset_1('#skF_2'(k1_xboole_0, B_7), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_7616])).
% 9.05/3.45  tff(c_13974, plain, (![B_7]: (v1_xboole_0('#skF_2'(k1_xboole_0, B_7)) | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_7625, c_13968])).
% 9.05/3.45  tff(c_13996, plain, (![B_7]: (v1_xboole_0('#skF_2'(k1_xboole_0, B_7)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_13974])).
% 9.05/3.45  tff(c_15570, plain, (![B_1157]: (v1_xboole_0('#skF_2'('#skF_5', B_1157)))), inference(demodulation, [status(thm), theory('equality')], [c_14809, c_13996])).
% 9.05/3.45  tff(c_14829, plain, (![A_5]: (A_5='#skF_5' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_14809, c_8])).
% 9.05/3.45  tff(c_15622, plain, (![B_1160]: ('#skF_2'('#skF_5', B_1160)='#skF_5')), inference(resolution, [status(thm)], [c_15570, c_14829])).
% 9.05/3.45  tff(c_15633, plain, (![B_1160]: (v1_funct_2('#skF_5', '#skF_5', B_1160))), inference(superposition, [status(thm), theory('equality')], [c_15622, c_62])).
% 9.05/3.45  tff(c_15898, plain, (![B_1160]: (v1_funct_2('#skF_4', '#skF_4', B_1160))), inference(demodulation, [status(thm), theory('equality')], [c_15886, c_15886, c_15633])).
% 9.05/3.45  tff(c_15196, plain, (![A_1136, B_1137, C_1138]: (k2_relset_1(A_1136, B_1137, C_1138)=k2_relat_1(C_1138) | ~m1_subset_1(C_1138, k1_zfmisc_1(k2_zfmisc_1(A_1136, B_1137))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.05/3.45  tff(c_15203, plain, (![A_1136, B_1137]: (k2_relset_1(A_1136, B_1137, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_14828, c_15196])).
% 9.05/3.45  tff(c_15225, plain, (![A_1139, B_1140]: (k2_relset_1(A_1139, B_1140, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14817, c_15203])).
% 9.05/3.45  tff(c_15229, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_15225, c_84])).
% 9.05/3.45  tff(c_15259, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15229, c_14778])).
% 9.05/3.45  tff(c_14827, plain, (![B_7]: (k2_zfmisc_1('#skF_5', B_7)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14809, c_14809, c_14])).
% 9.05/3.45  tff(c_15246, plain, (![B_7]: (k2_zfmisc_1('#skF_4', B_7)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15229, c_15229, c_14827])).
% 9.05/3.45  tff(c_8045, plain, (![A_659, B_660, C_661]: (k2_relset_1(A_659, B_660, C_661)=k2_relat_1(C_661) | ~m1_subset_1(C_661, k1_zfmisc_1(k2_zfmisc_1(A_659, B_660))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.05/3.45  tff(c_8054, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_8045])).
% 9.05/3.45  tff(c_8068, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_6893, c_8054])).
% 9.05/3.45  tff(c_8099, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8068, c_6])).
% 9.05/3.45  tff(c_8095, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8068, c_8068, c_12])).
% 9.05/3.45  tff(c_7643, plain, (![B_616, A_617]: (v1_xboole_0(B_616) | ~m1_subset_1(B_616, k1_zfmisc_1(A_617)) | ~v1_xboole_0(A_617))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.05/3.45  tff(c_7676, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_88, c_7643])).
% 9.05/3.45  tff(c_7724, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_7676])).
% 9.05/3.45  tff(c_8248, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8095, c_7724])).
% 9.05/3.45  tff(c_8252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8099, c_8248])).
% 9.05/3.45  tff(c_8254, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_7676])).
% 9.05/3.45  tff(c_8253, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_7676])).
% 9.05/3.45  tff(c_8258, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_8253, c_8])).
% 9.05/3.45  tff(c_8385, plain, (![A_681]: (A_681='#skF_5' | ~v1_xboole_0(A_681))), inference(demodulation, [status(thm), theory('equality')], [c_8258, c_8])).
% 9.05/3.45  tff(c_8400, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_8254, c_8385])).
% 9.05/3.45  tff(c_8744, plain, (![B_706, A_707]: (B_706='#skF_5' | A_707='#skF_5' | k2_zfmisc_1(A_707, B_706)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8258, c_8258, c_8258, c_10])).
% 9.05/3.45  tff(c_8754, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_8400, c_8744])).
% 9.05/3.45  tff(c_8795, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_8754])).
% 9.05/3.45  tff(c_8267, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8258, c_8258, c_7607])).
% 9.05/3.45  tff(c_8819, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8795, c_8795, c_8267])).
% 9.05/3.45  tff(c_8278, plain, (![A_8]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_8258, c_16])).
% 9.05/3.45  tff(c_8904, plain, (![A_715]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_715)))), inference(demodulation, [status(thm), theory('equality')], [c_8795, c_8278])).
% 9.05/3.45  tff(c_44, plain, (![A_28, B_29, C_30]: (k2_relset_1(A_28, B_29, C_30)=k2_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.05/3.45  tff(c_8908, plain, (![A_28, B_29]: (k2_relset_1(A_28, B_29, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_8904, c_44])).
% 9.05/3.45  tff(c_9147, plain, (![A_728, B_729]: (k2_relset_1(A_728, B_729, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8819, c_8908])).
% 9.05/3.45  tff(c_8825, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8795, c_84])).
% 9.05/3.45  tff(c_9151, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_9147, c_8825])).
% 9.05/3.45  tff(c_8276, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8258, c_8258, c_12])).
% 9.05/3.45  tff(c_8813, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8795, c_8795, c_8276])).
% 9.05/3.45  tff(c_7642, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_217])).
% 9.05/3.45  tff(c_8822, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_8795, c_7642])).
% 9.05/3.45  tff(c_9144, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8813, c_8822])).
% 9.05/3.45  tff(c_9159, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9151, c_9151, c_9144])).
% 9.05/3.45  tff(c_8824, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8795, c_199])).
% 9.05/3.45  tff(c_9179, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9151, c_8824])).
% 9.05/3.45  tff(c_8828, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8795, c_92])).
% 9.05/3.45  tff(c_9180, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9151, c_8828])).
% 9.05/3.45  tff(c_8827, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8795, c_86])).
% 9.05/3.45  tff(c_9181, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9151, c_8827])).
% 9.05/3.45  tff(c_8823, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8795, c_218])).
% 9.05/3.45  tff(c_9177, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9151, c_8823])).
% 9.05/3.45  tff(c_7606, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_226])).
% 9.05/3.45  tff(c_8268, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8258, c_8258, c_7606])).
% 9.05/3.45  tff(c_8818, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8795, c_8795, c_8268])).
% 9.05/3.45  tff(c_9175, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9151, c_9151, c_8818])).
% 9.05/3.45  tff(c_8522, plain, (![A_690]: (k2_relat_1(k2_funct_1(A_690))=k1_relat_1(A_690) | ~v2_funct_1(A_690) | ~v1_funct_1(A_690) | ~v1_relat_1(A_690))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.05/3.45  tff(c_11183, plain, (![A_866]: (v1_funct_2(k2_funct_1(A_866), k1_relat_1(k2_funct_1(A_866)), k1_relat_1(A_866)) | ~v1_funct_1(k2_funct_1(A_866)) | ~v1_relat_1(k2_funct_1(A_866)) | ~v2_funct_1(A_866) | ~v1_funct_1(A_866) | ~v1_relat_1(A_866))), inference(superposition, [status(thm), theory('equality')], [c_8522, c_78])).
% 9.05/3.45  tff(c_11192, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9175, c_11183])).
% 9.05/3.45  tff(c_11204, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9179, c_9180, c_9181, c_9177, c_11192])).
% 9.05/3.45  tff(c_11205, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_11204])).
% 9.05/3.45  tff(c_11208, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_11205])).
% 9.05/3.45  tff(c_11212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9179, c_9180, c_11208])).
% 9.05/3.45  tff(c_11214, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_11204])).
% 9.05/3.45  tff(c_8277, plain, (![B_7]: (k2_zfmisc_1('#skF_5', B_7)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8258, c_8258, c_14])).
% 9.05/3.45  tff(c_8811, plain, (![B_7]: (k2_zfmisc_1('#skF_3', B_7)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8795, c_8795, c_8277])).
% 9.05/3.45  tff(c_9162, plain, (![B_7]: (k2_zfmisc_1('#skF_4', B_7)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9151, c_9151, c_8811])).
% 9.05/3.45  tff(c_8274, plain, (![A_18]: (k1_relat_1(A_18)='#skF_5' | k2_relat_1(A_18)!='#skF_5' | ~v1_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_8258, c_8258, c_24])).
% 9.05/3.45  tff(c_8798, plain, (![A_18]: (k1_relat_1(A_18)='#skF_3' | k2_relat_1(A_18)!='#skF_3' | ~v1_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_8795, c_8795, c_8274])).
% 9.05/3.45  tff(c_9654, plain, (![A_18]: (k1_relat_1(A_18)='#skF_4' | k2_relat_1(A_18)!='#skF_4' | ~v1_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_9151, c_9151, c_8798])).
% 9.05/3.45  tff(c_11221, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_4' | k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(resolution, [status(thm)], [c_11214, c_9654])).
% 9.05/3.45  tff(c_11263, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_11221])).
% 9.05/3.45  tff(c_11269, plain, (k1_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_36, c_11263])).
% 9.05/3.45  tff(c_11275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9179, c_9180, c_9181, c_9175, c_11269])).
% 9.05/3.45  tff(c_11276, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_11221])).
% 9.05/3.45  tff(c_76, plain, (![A_39]: (m1_subset_1(A_39, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_39), k2_relat_1(A_39)))) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_151])).
% 9.05/3.45  tff(c_11303, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11276, c_76])).
% 9.05/3.45  tff(c_11330, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11214, c_9177, c_9162, c_11303])).
% 9.05/3.45  tff(c_11332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9159, c_11330])).
% 9.05/3.45  tff(c_11333, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_8754])).
% 9.05/3.45  tff(c_11378, plain, (![B_7]: (k2_zfmisc_1('#skF_4', B_7)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11333, c_11333, c_8277])).
% 9.05/3.45  tff(c_11389, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_11333, c_7642])).
% 9.05/3.45  tff(c_11692, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11378, c_11389])).
% 9.05/3.45  tff(c_11391, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11333, c_199])).
% 9.05/3.45  tff(c_11395, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11333, c_92])).
% 9.05/3.45  tff(c_11394, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11333, c_86])).
% 9.05/3.45  tff(c_11390, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11333, c_218])).
% 9.05/3.45  tff(c_11385, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11333, c_11333, c_8268])).
% 9.05/3.45  tff(c_13440, plain, (![A_1015]: (v1_funct_2(k2_funct_1(A_1015), k1_relat_1(k2_funct_1(A_1015)), k1_relat_1(A_1015)) | ~v1_funct_1(k2_funct_1(A_1015)) | ~v1_relat_1(k2_funct_1(A_1015)) | ~v2_funct_1(A_1015) | ~v1_funct_1(A_1015) | ~v1_relat_1(A_1015))), inference(superposition, [status(thm), theory('equality')], [c_8522, c_78])).
% 9.05/3.45  tff(c_13449, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11385, c_13440])).
% 9.05/3.45  tff(c_13461, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11391, c_11395, c_11394, c_11390, c_13449])).
% 9.05/3.45  tff(c_13462, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_13461])).
% 9.05/3.45  tff(c_13465, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_13462])).
% 9.05/3.45  tff(c_13469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11391, c_11395, c_13465])).
% 9.05/3.45  tff(c_13471, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_13461])).
% 9.05/3.45  tff(c_11380, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11333, c_11333, c_8276])).
% 9.05/3.45  tff(c_11386, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11333, c_11333, c_8267])).
% 9.05/3.45  tff(c_26, plain, (![A_18]: (k2_relat_1(A_18)=k1_xboole_0 | k1_relat_1(A_18)!=k1_xboole_0 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.05/3.45  tff(c_8270, plain, (![A_18]: (k2_relat_1(A_18)='#skF_5' | k1_relat_1(A_18)!='#skF_5' | ~v1_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_8258, c_8258, c_26])).
% 9.05/3.45  tff(c_11364, plain, (![A_18]: (k2_relat_1(A_18)='#skF_4' | k1_relat_1(A_18)!='#skF_4' | ~v1_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_11333, c_11333, c_8270])).
% 9.05/3.45  tff(c_13479, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_4' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(resolution, [status(thm)], [c_13471, c_11364])).
% 9.05/3.45  tff(c_13535, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_13479])).
% 9.05/3.45  tff(c_13538, plain, (k2_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38, c_13535])).
% 9.05/3.45  tff(c_13541, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11391, c_11395, c_11394, c_11386, c_13538])).
% 9.05/3.45  tff(c_13542, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_13479])).
% 9.05/3.45  tff(c_13567, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_13542, c_76])).
% 9.05/3.45  tff(c_13599, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13471, c_11390, c_11380, c_13567])).
% 9.05/3.45  tff(c_13601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11692, c_13599])).
% 9.05/3.45  tff(c_13603, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_217])).
% 9.05/3.45  tff(c_13993, plain, (v1_xboole_0(k2_funct_1('#skF_5')) | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_13603, c_13968])).
% 9.05/3.45  tff(c_14929, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_13993])).
% 9.05/3.45  tff(c_15457, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15246, c_14929])).
% 9.05/3.45  tff(c_15460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15259, c_15457])).
% 9.05/3.45  tff(c_15461, plain, (v1_xboole_0(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_13993])).
% 9.05/3.45  tff(c_15474, plain, (![A_1153]: (A_1153='#skF_5' | ~v1_xboole_0(A_1153))), inference(demodulation, [status(thm), theory('equality')], [c_14809, c_8])).
% 9.05/3.45  tff(c_15488, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_15461, c_15474])).
% 9.05/3.45  tff(c_13602, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_217])).
% 9.05/3.45  tff(c_15495, plain, (~v1_funct_2('#skF_5', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15488, c_13602])).
% 9.05/3.45  tff(c_15902, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15886, c_15495])).
% 9.05/3.45  tff(c_16155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15898, c_15902])).
% 9.05/3.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.05/3.45  
% 9.05/3.45  Inference rules
% 9.05/3.45  ----------------------
% 9.05/3.45  #Ref     : 0
% 9.05/3.45  #Sup     : 3550
% 9.05/3.45  #Fact    : 0
% 9.05/3.45  #Define  : 0
% 9.05/3.45  #Split   : 52
% 9.05/3.45  #Chain   : 0
% 9.05/3.45  #Close   : 0
% 9.05/3.45  
% 9.05/3.45  Ordering : KBO
% 9.05/3.46  
% 9.05/3.46  Simplification rules
% 9.05/3.46  ----------------------
% 9.05/3.46  #Subsume      : 477
% 9.05/3.46  #Demod        : 5071
% 9.05/3.46  #Tautology    : 2166
% 9.05/3.46  #SimpNegUnit  : 47
% 9.05/3.46  #BackRed      : 701
% 9.05/3.46  
% 9.05/3.46  #Partial instantiations: 0
% 9.05/3.46  #Strategies tried      : 1
% 9.05/3.46  
% 9.05/3.46  Timing (in seconds)
% 9.05/3.46  ----------------------
% 9.05/3.46  Preprocessing        : 0.37
% 9.05/3.46  Parsing              : 0.20
% 9.05/3.46  CNF conversion       : 0.02
% 9.05/3.46  Main loop            : 2.18
% 9.05/3.46  Inferencing          : 0.74
% 9.05/3.46  Reduction            : 0.80
% 9.05/3.46  Demodulation         : 0.59
% 9.05/3.46  BG Simplification    : 0.07
% 9.05/3.46  Subsumption          : 0.35
% 9.05/3.46  Abstraction          : 0.09
% 9.05/3.46  MUC search           : 0.00
% 9.05/3.46  Cooper               : 0.00
% 9.05/3.46  Total                : 2.65
% 9.05/3.46  Index Insertion      : 0.00
% 9.05/3.46  Index Deletion       : 0.00
% 9.05/3.46  Index Matching       : 0.00
% 9.05/3.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
