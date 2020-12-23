%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:50 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 362 expanded)
%              Number of leaves         :   35 ( 129 expanded)
%              Depth                    :   10
%              Number of atoms          :  148 (1205 expanded)
%              Number of equality atoms :   24 ( 346 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_142,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_422,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( r2_relset_1(A_93,B_94,C_95,C_95)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_445,plain,(
    ! [C_97] :
      ( r2_relset_1('#skF_2','#skF_3',C_97,C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_56,c_422])).

tff(c_456,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_445])).

tff(c_46,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_61,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_377,plain,(
    ! [C_90,A_91,B_92] :
      ( v1_partfun1(C_90,A_91)
      | ~ v1_funct_2(C_90,A_91,B_92)
      | ~ v1_funct_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | v1_xboole_0(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_383,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_377])).

tff(c_404,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_383])).

tff(c_411,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_404])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_414,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_411,c_4])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_414])).

tff(c_419,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_404])).

tff(c_420,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_404])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_386,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_377])).

tff(c_407,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_386])).

tff(c_421,plain,(
    v1_partfun1('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_420,c_407])).

tff(c_48,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_496,plain,(
    ! [D_105,C_106,A_107,B_108] :
      ( D_105 = C_106
      | ~ r1_partfun1(C_106,D_105)
      | ~ v1_partfun1(D_105,A_107)
      | ~ v1_partfun1(C_106,A_107)
      | ~ m1_subset_1(D_105,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ v1_funct_1(D_105)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ v1_funct_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_498,plain,(
    ! [A_107,B_108] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_107)
      | ~ v1_partfun1('#skF_4',A_107)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_496])).

tff(c_501,plain,(
    ! [A_107,B_108] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_107)
      | ~ v1_partfun1('#skF_4',A_107)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_498])).

tff(c_752,plain,(
    ! [A_144,B_145] :
      ( ~ v1_partfun1('#skF_5',A_144)
      | ~ v1_partfun1('#skF_4',A_144)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(splitLeft,[status(thm)],[c_501])).

tff(c_759,plain,
    ( ~ v1_partfun1('#skF_5','#skF_2')
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_50,c_752])).

tff(c_772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_419,c_421,c_759])).

tff(c_773,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_501])).

tff(c_44,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_782,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_44])).

tff(c_795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_782])).

tff(c_797,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_796,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_803,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_797,c_796])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_798,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_2])).

tff(c_808,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_798])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_815,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_797,c_797,c_8])).

tff(c_850,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_803,c_56])).

tff(c_879,plain,(
    ! [B_156,A_157] :
      ( v1_xboole_0(B_156)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_157))
      | ~ v1_xboole_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_885,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_850,c_879])).

tff(c_898,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_885])).

tff(c_843,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_797,c_4])).

tff(c_909,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_898,c_843])).

tff(c_14,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_824,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_797,c_14])).

tff(c_928,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_824])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1('#skF_1'(A_4),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1226,plain,(
    ! [A_203,B_204,C_205,D_206] :
      ( r2_relset_1(A_203,B_204,C_205,C_205)
      | ~ m1_subset_1(D_206,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204)))
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1242,plain,(
    ! [A_207,B_208,C_209] :
      ( r2_relset_1(A_207,B_208,C_209,C_209)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(resolution,[status(thm)],[c_12,c_1226])).

tff(c_1256,plain,(
    ! [A_207,B_208] : r2_relset_1(A_207,B_208,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_928,c_1242])).

tff(c_851,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_803,c_50])).

tff(c_882,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_851,c_879])).

tff(c_895,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_882])).

tff(c_905,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_895,c_843])).

tff(c_823,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_44])).

tff(c_912,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_823])).

tff(c_1025,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_909,c_909,c_912])).

tff(c_1260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1256,c_1025])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:33:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.54  
% 3.51/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.54  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.51/1.54  
% 3.51/1.54  %Foreground sorts:
% 3.51/1.54  
% 3.51/1.54  
% 3.51/1.54  %Background operators:
% 3.51/1.54  
% 3.51/1.54  
% 3.51/1.54  %Foreground operators:
% 3.51/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.51/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.51/1.54  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.51/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.51/1.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.51/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.51/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.51/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.51/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.51/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.51/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.51/1.54  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.51/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.51/1.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.51/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.51/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.51/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.51/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.51/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.51/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.51/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.51/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.51/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.51/1.54  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 3.51/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.51/1.54  
% 3.63/1.56  tff(f_142, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 3.63/1.56  tff(f_76, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.63/1.56  tff(f_90, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.63/1.56  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.63/1.56  tff(f_107, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 3.63/1.56  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.63/1.56  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.63/1.56  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.63/1.56  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.63/1.56  tff(f_39, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.63/1.56  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.63/1.56  tff(c_422, plain, (![A_93, B_94, C_95, D_96]: (r2_relset_1(A_93, B_94, C_95, C_95) | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.63/1.56  tff(c_445, plain, (![C_97]: (r2_relset_1('#skF_2', '#skF_3', C_97, C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_56, c_422])).
% 3.63/1.56  tff(c_456, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_445])).
% 3.63/1.56  tff(c_46, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.63/1.56  tff(c_61, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_46])).
% 3.63/1.56  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.63/1.56  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.63/1.56  tff(c_377, plain, (![C_90, A_91, B_92]: (v1_partfun1(C_90, A_91) | ~v1_funct_2(C_90, A_91, B_92) | ~v1_funct_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | v1_xboole_0(B_92))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.63/1.56  tff(c_383, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_377])).
% 3.63/1.56  tff(c_404, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_383])).
% 3.63/1.56  tff(c_411, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_404])).
% 3.63/1.56  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.63/1.56  tff(c_414, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_411, c_4])).
% 3.63/1.56  tff(c_418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_414])).
% 3.63/1.56  tff(c_419, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_404])).
% 3.63/1.56  tff(c_420, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_404])).
% 3.63/1.56  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.63/1.56  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.63/1.56  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.63/1.56  tff(c_386, plain, (v1_partfun1('#skF_5', '#skF_2') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_377])).
% 3.63/1.56  tff(c_407, plain, (v1_partfun1('#skF_5', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_386])).
% 3.63/1.56  tff(c_421, plain, (v1_partfun1('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_420, c_407])).
% 3.63/1.56  tff(c_48, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.63/1.56  tff(c_496, plain, (![D_105, C_106, A_107, B_108]: (D_105=C_106 | ~r1_partfun1(C_106, D_105) | ~v1_partfun1(D_105, A_107) | ~v1_partfun1(C_106, A_107) | ~m1_subset_1(D_105, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~v1_funct_1(D_105) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~v1_funct_1(C_106))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.63/1.56  tff(c_498, plain, (![A_107, B_108]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_107) | ~v1_partfun1('#skF_4', A_107) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_496])).
% 3.63/1.56  tff(c_501, plain, (![A_107, B_108]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_107) | ~v1_partfun1('#skF_4', A_107) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_498])).
% 3.63/1.56  tff(c_752, plain, (![A_144, B_145]: (~v1_partfun1('#skF_5', A_144) | ~v1_partfun1('#skF_4', A_144) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(splitLeft, [status(thm)], [c_501])).
% 3.63/1.56  tff(c_759, plain, (~v1_partfun1('#skF_5', '#skF_2') | ~v1_partfun1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_50, c_752])).
% 3.63/1.56  tff(c_772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_419, c_421, c_759])).
% 3.63/1.56  tff(c_773, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_501])).
% 3.63/1.56  tff(c_44, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.63/1.56  tff(c_782, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_773, c_44])).
% 3.63/1.56  tff(c_795, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_456, c_782])).
% 3.63/1.56  tff(c_797, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_46])).
% 3.63/1.56  tff(c_796, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_46])).
% 3.63/1.56  tff(c_803, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_797, c_796])).
% 3.63/1.56  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.63/1.56  tff(c_798, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_796, c_2])).
% 3.63/1.56  tff(c_808, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_803, c_798])).
% 3.63/1.56  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.63/1.56  tff(c_815, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_797, c_797, c_8])).
% 3.63/1.56  tff(c_850, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_815, c_803, c_56])).
% 3.63/1.56  tff(c_879, plain, (![B_156, A_157]: (v1_xboole_0(B_156) | ~m1_subset_1(B_156, k1_zfmisc_1(A_157)) | ~v1_xboole_0(A_157))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.63/1.56  tff(c_885, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_850, c_879])).
% 3.63/1.56  tff(c_898, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_808, c_885])).
% 3.63/1.56  tff(c_843, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_797, c_4])).
% 3.63/1.56  tff(c_909, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_898, c_843])).
% 3.63/1.56  tff(c_14, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.63/1.56  tff(c_824, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_797, c_14])).
% 3.63/1.56  tff(c_928, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_909, c_824])).
% 3.63/1.56  tff(c_12, plain, (![A_4]: (m1_subset_1('#skF_1'(A_4), A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.63/1.56  tff(c_1226, plain, (![A_203, B_204, C_205, D_206]: (r2_relset_1(A_203, B_204, C_205, C_205) | ~m1_subset_1(D_206, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.63/1.56  tff(c_1242, plain, (![A_207, B_208, C_209]: (r2_relset_1(A_207, B_208, C_209, C_209) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))))), inference(resolution, [status(thm)], [c_12, c_1226])).
% 3.63/1.56  tff(c_1256, plain, (![A_207, B_208]: (r2_relset_1(A_207, B_208, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_928, c_1242])).
% 3.63/1.56  tff(c_851, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_815, c_803, c_50])).
% 3.63/1.56  tff(c_882, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_851, c_879])).
% 3.63/1.56  tff(c_895, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_808, c_882])).
% 3.63/1.56  tff(c_905, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_895, c_843])).
% 3.63/1.56  tff(c_823, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_803, c_44])).
% 3.63/1.56  tff(c_912, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_905, c_823])).
% 3.63/1.56  tff(c_1025, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_909, c_909, c_909, c_912])).
% 3.63/1.56  tff(c_1260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1256, c_1025])).
% 3.63/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.56  
% 3.63/1.56  Inference rules
% 3.63/1.56  ----------------------
% 3.63/1.56  #Ref     : 0
% 3.63/1.56  #Sup     : 253
% 3.63/1.56  #Fact    : 0
% 3.63/1.56  #Define  : 0
% 3.63/1.56  #Split   : 7
% 3.63/1.56  #Chain   : 0
% 3.63/1.56  #Close   : 0
% 3.63/1.56  
% 3.63/1.56  Ordering : KBO
% 3.63/1.56  
% 3.63/1.56  Simplification rules
% 3.63/1.56  ----------------------
% 3.63/1.56  #Subsume      : 33
% 3.63/1.56  #Demod        : 226
% 3.63/1.56  #Tautology    : 134
% 3.63/1.56  #SimpNegUnit  : 2
% 3.63/1.56  #BackRed      : 35
% 3.63/1.56  
% 3.63/1.56  #Partial instantiations: 0
% 3.63/1.56  #Strategies tried      : 1
% 3.63/1.56  
% 3.63/1.56  Timing (in seconds)
% 3.63/1.56  ----------------------
% 3.63/1.57  Preprocessing        : 0.34
% 3.63/1.57  Parsing              : 0.19
% 3.63/1.57  CNF conversion       : 0.02
% 3.63/1.57  Main loop            : 0.45
% 3.63/1.57  Inferencing          : 0.16
% 3.63/1.57  Reduction            : 0.15
% 3.63/1.57  Demodulation         : 0.11
% 3.63/1.57  BG Simplification    : 0.02
% 3.63/1.57  Subsumption          : 0.07
% 3.63/1.57  Abstraction          : 0.02
% 3.63/1.57  MUC search           : 0.00
% 3.63/1.57  Cooper               : 0.00
% 3.63/1.57  Total                : 0.83
% 3.63/1.57  Index Insertion      : 0.00
% 3.63/1.57  Index Deletion       : 0.00
% 3.63/1.57  Index Matching       : 0.00
% 3.63/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
