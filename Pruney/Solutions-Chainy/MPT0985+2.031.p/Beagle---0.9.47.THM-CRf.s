%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:30 EST 2020

% Result     : Theorem 11.26s
% Output     : CNFRefutation 11.67s
% Verified   : 
% Statistics : Number of formulae       :  395 (30341 expanded)
%              Number of leaves         :   43 (9487 expanded)
%              Depth                    :   22
%              Number of atoms          :  698 (78856 expanded)
%              Number of equality atoms :  228 (31900 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_166,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_139,axiom,(
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

tff(f_149,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_121,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_82,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_208,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_221,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_208])).

tff(c_86,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_80,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_78,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_8478,plain,(
    ! [A_419,B_420,C_421] :
      ( k2_relset_1(A_419,B_420,C_421) = k2_relat_1(C_421)
      | ~ m1_subset_1(C_421,k1_zfmisc_1(k2_zfmisc_1(A_419,B_420))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_8491,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_8478])).

tff(c_8502,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_8491])).

tff(c_44,plain,(
    ! [A_22] :
      ( k1_relat_1(k2_funct_1(A_22)) = k2_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_38,plain,(
    ! [A_21] :
      ( v1_funct_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_76,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_148,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_151,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_148])).

tff(c_154,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_151])).

tff(c_189,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_196,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_189])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_196])).

tff(c_206,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_239,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_915,plain,(
    ! [A_160,B_161,C_162] :
      ( k2_relset_1(A_160,B_161,C_162) = k2_relat_1(C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_925,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_915])).

tff(c_935,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_925])).

tff(c_40,plain,(
    ! [A_21] :
      ( v1_relat_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_207,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_34,plain,(
    ! [A_20] :
      ( k2_relat_1(A_20) != k1_xboole_0
      | k1_xboole_0 = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_228,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_221,c_34])).

tff(c_230,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_936,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_230])).

tff(c_84,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_747,plain,(
    ! [A_135,B_136,C_137] :
      ( k1_relset_1(A_135,B_136,C_137) = k1_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_762,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_747])).

tff(c_1220,plain,(
    ! [B_190,A_191,C_192] :
      ( k1_xboole_0 = B_190
      | k1_relset_1(A_191,B_190,C_192) = A_191
      | ~ v1_funct_2(C_192,A_191,B_190)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_191,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1233,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_1220])).

tff(c_1248,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_762,c_1233])).

tff(c_1249,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_936,c_1248])).

tff(c_709,plain,(
    ! [A_128] :
      ( k2_relat_1(k2_funct_1(A_128)) = k1_relat_1(A_128)
      | ~ v2_funct_1(A_128)
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_72,plain,(
    ! [A_42] :
      ( v1_funct_2(A_42,k1_relat_1(A_42),k2_relat_1(A_42))
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_6153,plain,(
    ! [A_332] :
      ( v1_funct_2(k2_funct_1(A_332),k1_relat_1(k2_funct_1(A_332)),k1_relat_1(A_332))
      | ~ v1_funct_1(k2_funct_1(A_332))
      | ~ v1_relat_1(k2_funct_1(A_332))
      | ~ v2_funct_1(A_332)
      | ~ v1_funct_1(A_332)
      | ~ v1_relat_1(A_332) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_709,c_72])).

tff(c_6168,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1249,c_6153])).

tff(c_6177,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_86,c_80,c_207,c_6168])).

tff(c_6178,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6177])).

tff(c_6181,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_6178])).

tff(c_6185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_86,c_6181])).

tff(c_6187,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6177])).

tff(c_42,plain,(
    ! [A_22] :
      ( k2_relat_1(k2_funct_1(A_22)) = k1_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_791,plain,(
    ! [A_143] :
      ( m1_subset_1(A_143,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_143),k2_relat_1(A_143))))
      | ~ v1_funct_1(A_143)
      | ~ v1_relat_1(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_7675,plain,(
    ! [A_344] :
      ( m1_subset_1(k2_funct_1(A_344),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_344)),k1_relat_1(A_344))))
      | ~ v1_funct_1(k2_funct_1(A_344))
      | ~ v1_relat_1(k2_funct_1(A_344))
      | ~ v2_funct_1(A_344)
      | ~ v1_funct_1(A_344)
      | ~ v1_relat_1(A_344) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_791])).

tff(c_7717,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1249,c_7675])).

tff(c_7734,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_86,c_80,c_6187,c_207,c_7717])).

tff(c_7764,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),'#skF_3')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_7734])).

tff(c_7785,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_86,c_80,c_935,c_7764])).

tff(c_7787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_239,c_7785])).

tff(c_7788,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_8503,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8502,c_230])).

tff(c_8422,plain,(
    ! [A_411,B_412,C_413] :
      ( k1_relset_1(A_411,B_412,C_413) = k1_relat_1(C_413)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(A_411,B_412))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_8445,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_8422])).

tff(c_8743,plain,(
    ! [B_443,A_444,C_445] :
      ( k1_xboole_0 = B_443
      | k1_relset_1(A_444,B_443,C_445) = A_444
      | ~ v1_funct_2(C_445,A_444,B_443)
      | ~ m1_subset_1(C_445,k1_zfmisc_1(k2_zfmisc_1(A_444,B_443))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_8759,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_8743])).

tff(c_8776,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_8445,c_8759])).

tff(c_8777,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_8503,c_8776])).

tff(c_36,plain,(
    ! [A_20] :
      ( k1_relat_1(A_20) != k1_xboole_0
      | k1_xboole_0 = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_229,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_221,c_36])).

tff(c_232,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_8788,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8777,c_232])).

tff(c_7789,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_8443,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_7789,c_8422])).

tff(c_8819,plain,(
    ! [B_447,C_448,A_449] :
      ( k1_xboole_0 = B_447
      | v1_funct_2(C_448,A_449,B_447)
      | k1_relset_1(A_449,B_447,C_448) != A_449
      | ~ m1_subset_1(C_448,k1_zfmisc_1(k2_zfmisc_1(A_449,B_447))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_8825,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_7789,c_8819])).

tff(c_8841,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8443,c_8825])).

tff(c_8842,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_7788,c_8788,c_8841])).

tff(c_8851,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_8842])).

tff(c_8854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_86,c_80,c_8502,c_8851])).

tff(c_8855,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_8857,plain,(
    k2_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8855,c_230])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8862,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8855,c_12])).

tff(c_32,plain,(
    ! [A_19] :
      ( v1_xboole_0(k2_relat_1(A_19))
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8968,plain,(
    ! [A_462,B_463] :
      ( r2_hidden('#skF_2'(A_462,B_463),A_462)
      | r1_tarski(A_462,B_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8978,plain,(
    ! [A_462,B_463] :
      ( ~ v1_xboole_0(A_462)
      | r1_tarski(A_462,B_463) ) ),
    inference(resolution,[status(thm)],[c_8968,c_2])).

tff(c_9050,plain,(
    ! [B_473,A_474] :
      ( B_473 = A_474
      | ~ r1_tarski(B_473,A_474)
      | ~ r1_tarski(A_474,B_473) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_9070,plain,(
    ! [B_478,A_479] :
      ( B_478 = A_479
      | ~ r1_tarski(B_478,A_479)
      | ~ v1_xboole_0(A_479) ) ),
    inference(resolution,[status(thm)],[c_8978,c_9050])).

tff(c_9084,plain,(
    ! [B_480,A_481] :
      ( B_480 = A_481
      | ~ v1_xboole_0(B_480)
      | ~ v1_xboole_0(A_481) ) ),
    inference(resolution,[status(thm)],[c_8978,c_9070])).

tff(c_9091,plain,(
    ! [A_482] :
      ( A_482 = '#skF_5'
      | ~ v1_xboole_0(A_482) ) ),
    inference(resolution,[status(thm)],[c_8862,c_9084])).

tff(c_9101,plain,(
    ! [A_483] :
      ( k2_relat_1(A_483) = '#skF_5'
      | ~ v1_xboole_0(A_483) ) ),
    inference(resolution,[status(thm)],[c_32,c_9091])).

tff(c_9104,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8862,c_9101])).

tff(c_9111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8857,c_9104])).

tff(c_9112,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_9113,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_9123,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9112,c_9113])).

tff(c_18009,plain,(
    ! [A_1110] :
      ( k1_relat_1(k2_funct_1(A_1110)) = k2_relat_1(A_1110)
      | ~ v2_funct_1(A_1110)
      | ~ v1_funct_1(A_1110)
      | ~ v1_relat_1(A_1110) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_9732,plain,(
    ! [A_558,B_559,C_560] :
      ( k2_relset_1(A_558,B_559,C_560) = k2_relat_1(C_560)
      | ~ m1_subset_1(C_560,k1_zfmisc_1(k2_zfmisc_1(A_558,B_559))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_9745,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_9732])).

tff(c_9748,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_9123,c_9745])).

tff(c_9118,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9112,c_12])).

tff(c_9776,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9748,c_9118])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_9116,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9112,c_9112,c_22])).

tff(c_9773,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9748,c_9748,c_9116])).

tff(c_9265,plain,(
    ! [A_503,B_504] :
      ( r2_hidden('#skF_2'(A_503,B_504),A_503)
      | r1_tarski(A_503,B_504) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9275,plain,(
    ! [A_503,B_504] :
      ( ~ v1_xboole_0(A_503)
      | r1_tarski(A_503,B_504) ) ),
    inference(resolution,[status(thm)],[c_9265,c_2])).

tff(c_129,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_133,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_82,c_129])).

tff(c_9295,plain,(
    ! [B_507,A_508] :
      ( B_507 = A_508
      | ~ r1_tarski(B_507,A_508)
      | ~ r1_tarski(A_508,B_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_9303,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_133,c_9295])).

tff(c_9318,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_9303])).

tff(c_9322,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_9275,c_9318])).

tff(c_9889,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9773,c_9322])).

tff(c_9892,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9776,c_9889])).

tff(c_9893,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_9303])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( k1_xboole_0 = B_13
      | k1_xboole_0 = A_12
      | k2_zfmisc_1(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_9181,plain,(
    ! [B_13,A_12] :
      ( B_13 = '#skF_5'
      | A_12 = '#skF_5'
      | k2_zfmisc_1(A_12,B_13) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9112,c_9112,c_9112,c_20])).

tff(c_9918,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_9893,c_9181])).

tff(c_9936,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_9918])).

tff(c_9950,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9936,c_9936,c_9123])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_9952,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9936,c_9112])).

tff(c_58,plain,(
    ! [A_39] :
      ( v1_funct_2(k1_xboole_0,A_39,k1_xboole_0)
      | k1_xboole_0 = A_39
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_39,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_90,plain,(
    ! [A_39] :
      ( v1_funct_2(k1_xboole_0,A_39,k1_xboole_0)
      | k1_xboole_0 = A_39
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_58])).

tff(c_9971,plain,(
    ! [A_39] :
      ( v1_funct_2('#skF_3',A_39,'#skF_3')
      | A_39 = '#skF_3'
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9952,c_9952,c_9952,c_9952,c_9952,c_90])).

tff(c_9972,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_9971])).

tff(c_9985,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_9972])).

tff(c_9989,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_9985])).

tff(c_9991,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_9971])).

tff(c_24,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_9117,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_5',B_13) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9112,c_9112,c_24])).

tff(c_9949,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_3',B_13) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9936,c_9936,c_9117])).

tff(c_10182,plain,(
    ! [A_583,B_584,C_585] :
      ( k2_relset_1(A_583,B_584,C_585) = k2_relat_1(C_585)
      | ~ m1_subset_1(C_585,k1_zfmisc_1(k2_zfmisc_1(A_583,B_584))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_10764,plain,(
    ! [B_662,C_663] :
      ( k2_relset_1('#skF_3',B_662,C_663) = k2_relat_1(C_663)
      | ~ m1_subset_1(C_663,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9949,c_10182])).

tff(c_10766,plain,(
    ! [B_662] : k2_relset_1('#skF_3',B_662,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_9991,c_10764])).

tff(c_10783,plain,(
    ! [B_666] : k2_relset_1('#skF_3',B_666,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9950,c_10766])).

tff(c_9955,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9936,c_78])).

tff(c_10790,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_10783,c_9955])).

tff(c_9953,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9936,c_221])).

tff(c_10852,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10790,c_9953])).

tff(c_9958,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9936,c_86])).

tff(c_10850,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10790,c_9958])).

tff(c_9957,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9936,c_80])).

tff(c_10851,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10790,c_9957])).

tff(c_10268,plain,(
    ! [A_589,B_590,C_591] :
      ( k1_relset_1(A_589,B_590,C_591) = k1_relat_1(C_591)
      | ~ m1_subset_1(C_591,k1_zfmisc_1(k2_zfmisc_1(A_589,B_590))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_10589,plain,(
    ! [B_648,C_649] :
      ( k1_relset_1('#skF_3',B_648,C_649) = k1_relat_1(C_649)
      | ~ m1_subset_1(C_649,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9949,c_10268])).

tff(c_10616,plain,(
    ! [B_653] : k1_relset_1('#skF_3',B_653,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_9991,c_10589])).

tff(c_9956,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9936,c_84])).

tff(c_66,plain,(
    ! [B_40,C_41] :
      ( k1_relset_1(k1_xboole_0,B_40,C_41) = k1_xboole_0
      | ~ v1_funct_2(C_41,k1_xboole_0,B_40)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_87,plain,(
    ! [B_40,C_41] :
      ( k1_relset_1(k1_xboole_0,B_40,C_41) = k1_xboole_0
      | ~ v1_funct_2(C_41,k1_xboole_0,B_40)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_66])).

tff(c_10412,plain,(
    ! [B_614,C_615] :
      ( k1_relset_1('#skF_3',B_614,C_615) = '#skF_3'
      | ~ v1_funct_2(C_615,'#skF_3',B_614)
      | ~ m1_subset_1(C_615,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9952,c_9952,c_9952,c_9952,c_87])).

tff(c_10417,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_9956,c_10412])).

tff(c_10424,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9991,c_10417])).

tff(c_10623,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_10616,c_10424])).

tff(c_10810,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10790,c_10790,c_10623])).

tff(c_9954,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9936,c_207])).

tff(c_10849,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10790,c_9954])).

tff(c_10127,plain,(
    ! [A_576] :
      ( k2_relat_1(k2_funct_1(A_576)) = k1_relat_1(A_576)
      | ~ v2_funct_1(A_576)
      | ~ v1_funct_1(A_576)
      | ~ v1_relat_1(A_576) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_11907,plain,(
    ! [A_759] :
      ( v1_funct_2(k2_funct_1(A_759),k1_relat_1(k2_funct_1(A_759)),k1_relat_1(A_759))
      | ~ v1_funct_1(k2_funct_1(A_759))
      | ~ v1_relat_1(k2_funct_1(A_759))
      | ~ v2_funct_1(A_759)
      | ~ v1_funct_1(A_759)
      | ~ v1_relat_1(A_759) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10127,c_72])).

tff(c_11913,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10810,c_11907])).

tff(c_11921,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10852,c_10850,c_10851,c_10849,c_11913])).

tff(c_11922,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_11921])).

tff(c_11925,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_11922])).

tff(c_11929,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10852,c_10850,c_11925])).

tff(c_11931,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_11921])).

tff(c_9114,plain,(
    ! [A_20] :
      ( k2_relat_1(A_20) != '#skF_5'
      | A_20 = '#skF_5'
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9112,c_9112,c_34])).

tff(c_9942,plain,(
    ! [A_20] :
      ( k2_relat_1(A_20) != '#skF_3'
      | A_20 = '#skF_3'
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9936,c_9936,c_9114])).

tff(c_10834,plain,(
    ! [A_20] :
      ( k2_relat_1(A_20) != '#skF_4'
      | A_20 = '#skF_4'
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10790,c_10790,c_9942])).

tff(c_11939,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_11931,c_10834])).

tff(c_11945,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_11939])).

tff(c_11948,plain,
    ( k1_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_11945])).

tff(c_11951,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10852,c_10850,c_10851,c_10810,c_11948])).

tff(c_11952,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11939])).

tff(c_9948,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9936,c_9936,c_9116])).

tff(c_9168,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_9945,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9936,c_9168])).

tff(c_10091,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9948,c_9945])).

tff(c_10095,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_10091])).

tff(c_10840,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10790,c_10790,c_10095])).

tff(c_11957,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11952,c_10840])).

tff(c_11966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_11957])).

tff(c_11967,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9918])).

tff(c_11984,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11967,c_221])).

tff(c_11989,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11967,c_86])).

tff(c_11988,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11967,c_80])).

tff(c_11981,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11967,c_11967,c_9123])).

tff(c_11985,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11967,c_207])).

tff(c_11983,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11967,c_9112])).

tff(c_11994,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_12014,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11983,c_11983,c_11994])).

tff(c_12017,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_12014])).

tff(c_12021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_12017])).

tff(c_12023,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_12034,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11983,c_11983,c_12023])).

tff(c_11980,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_4',B_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11967,c_11967,c_9117])).

tff(c_12390,plain,(
    ! [A_798,B_799,C_800] :
      ( k1_relset_1(A_798,B_799,C_800) = k1_relat_1(C_800)
      | ~ m1_subset_1(C_800,k1_zfmisc_1(k2_zfmisc_1(A_798,B_799))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_12545,plain,(
    ! [B_825,C_826] :
      ( k1_relset_1('#skF_4',B_825,C_826) = k1_relat_1(C_826)
      | ~ m1_subset_1(C_826,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11980,c_12390])).

tff(c_12551,plain,(
    ! [B_825] : k1_relset_1('#skF_4',B_825,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12034,c_12545])).

tff(c_62,plain,(
    ! [C_41,B_40] :
      ( v1_funct_2(C_41,k1_xboole_0,B_40)
      | k1_relset_1(k1_xboole_0,B_40,C_41) != k1_xboole_0
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_88,plain,(
    ! [C_41,B_40] :
      ( v1_funct_2(C_41,k1_xboole_0,B_40)
      | k1_relset_1(k1_xboole_0,B_40,C_41) != k1_xboole_0
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_62])).

tff(c_12654,plain,(
    ! [C_846,B_847] :
      ( v1_funct_2(C_846,'#skF_4',B_847)
      | k1_relset_1('#skF_4',B_847,C_846) != '#skF_4'
      | ~ m1_subset_1(C_846,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11983,c_11983,c_11983,c_11983,c_88])).

tff(c_12656,plain,(
    ! [B_847] :
      ( v1_funct_2('#skF_4','#skF_4',B_847)
      | k1_relset_1('#skF_4',B_847,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_12034,c_12654])).

tff(c_12661,plain,(
    ! [B_847] :
      ( v1_funct_2('#skF_4','#skF_4',B_847)
      | k1_relat_1('#skF_4') != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12551,c_12656])).

tff(c_12678,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_12661])).

tff(c_11982,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11967,c_9118])).

tff(c_12315,plain,(
    ! [C_782,A_783,B_784] :
      ( v1_partfun1(C_782,A_783)
      | ~ m1_subset_1(C_782,k1_zfmisc_1(k2_zfmisc_1(A_783,B_784)))
      | ~ v1_xboole_0(A_783) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_12321,plain,(
    ! [C_782] :
      ( v1_partfun1(C_782,'#skF_4')
      | ~ m1_subset_1(C_782,k1_zfmisc_1('#skF_4'))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11980,c_12315])).

tff(c_12329,plain,(
    ! [C_785] :
      ( v1_partfun1(C_785,'#skF_4')
      | ~ m1_subset_1(C_785,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11982,c_12321])).

tff(c_12337,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_12034,c_12329])).

tff(c_13123,plain,(
    ! [A_891,B_892,A_893] :
      ( k1_relset_1(A_891,B_892,A_893) = k1_relat_1(A_893)
      | ~ r1_tarski(A_893,k2_zfmisc_1(A_891,B_892)) ) ),
    inference(resolution,[status(thm)],[c_30,c_12390])).

tff(c_13161,plain,(
    ! [A_896,B_897,A_898] :
      ( k1_relset_1(A_896,B_897,A_898) = k1_relat_1(A_898)
      | ~ v1_xboole_0(A_898) ) ),
    inference(resolution,[status(thm)],[c_9275,c_13123])).

tff(c_13166,plain,(
    ! [A_896,B_897] : k1_relset_1(A_896,B_897,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11982,c_13161])).

tff(c_11979,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11967,c_11967,c_9116])).

tff(c_12156,plain,(
    ! [B_767,A_768] :
      ( B_767 = A_768
      | ~ r1_tarski(B_767,A_768)
      | ~ v1_xboole_0(A_768) ) ),
    inference(resolution,[status(thm)],[c_9275,c_9295])).

tff(c_12184,plain,(
    ! [B_770,A_771] :
      ( B_770 = A_771
      | ~ v1_xboole_0(B_770)
      | ~ v1_xboole_0(A_771) ) ),
    inference(resolution,[status(thm)],[c_9275,c_12156])).

tff(c_12191,plain,(
    ! [A_772] :
      ( A_772 = '#skF_4'
      | ~ v1_xboole_0(A_772) ) ),
    inference(resolution,[status(thm)],[c_11982,c_12184])).

tff(c_12201,plain,(
    ! [A_773] :
      ( k2_relat_1(A_773) = '#skF_4'
      | ~ v1_xboole_0(A_773) ) ),
    inference(resolution,[status(thm)],[c_32,c_12191])).

tff(c_12210,plain,(
    ! [A_19] :
      ( k2_relat_1(k2_relat_1(A_19)) = '#skF_4'
      | ~ v1_xboole_0(A_19) ) ),
    inference(resolution,[status(thm)],[c_32,c_12201])).

tff(c_12470,plain,(
    ! [A_817] :
      ( m1_subset_1(A_817,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_817),k2_relat_1(A_817))))
      | ~ v1_funct_1(A_817)
      | ~ v1_relat_1(A_817) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12970,plain,(
    ! [A_869] :
      ( r1_tarski(A_869,k2_zfmisc_1(k1_relat_1(A_869),k2_relat_1(A_869)))
      | ~ v1_funct_1(A_869)
      | ~ v1_relat_1(A_869) ) ),
    inference(resolution,[status(thm)],[c_12470,c_28])).

tff(c_12996,plain,(
    ! [A_19] :
      ( r1_tarski(k2_relat_1(A_19),k2_zfmisc_1(k1_relat_1(k2_relat_1(A_19)),'#skF_4'))
      | ~ v1_funct_1(k2_relat_1(A_19))
      | ~ v1_relat_1(k2_relat_1(A_19))
      | ~ v1_xboole_0(A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12210,c_12970])).

tff(c_14568,plain,(
    ! [A_936] :
      ( r1_tarski(k2_relat_1(A_936),'#skF_4')
      | ~ v1_funct_1(k2_relat_1(A_936))
      | ~ v1_relat_1(k2_relat_1(A_936))
      | ~ v1_xboole_0(A_936) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11979,c_12996])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9895,plain,(
    ! [C_562,B_563,A_564] :
      ( r2_hidden(C_562,B_563)
      | ~ r2_hidden(C_562,A_564)
      | ~ r1_tarski(A_564,B_563) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13100,plain,(
    ! [A_885,B_886,B_887] :
      ( r2_hidden('#skF_2'(A_885,B_886),B_887)
      | ~ r1_tarski(A_885,B_887)
      | r1_tarski(A_885,B_886) ) ),
    inference(resolution,[status(thm)],[c_10,c_9895])).

tff(c_13112,plain,(
    ! [B_887,A_885,B_886] :
      ( ~ v1_xboole_0(B_887)
      | ~ r1_tarski(A_885,B_887)
      | r1_tarski(A_885,B_886) ) ),
    inference(resolution,[status(thm)],[c_13100,c_2])).

tff(c_14572,plain,(
    ! [A_936,B_886] :
      ( ~ v1_xboole_0('#skF_4')
      | r1_tarski(k2_relat_1(A_936),B_886)
      | ~ v1_funct_1(k2_relat_1(A_936))
      | ~ v1_relat_1(k2_relat_1(A_936))
      | ~ v1_xboole_0(A_936) ) ),
    inference(resolution,[status(thm)],[c_14568,c_13112])).

tff(c_14687,plain,(
    ! [A_947,B_948] :
      ( r1_tarski(k2_relat_1(A_947),B_948)
      | ~ v1_funct_1(k2_relat_1(A_947))
      | ~ v1_relat_1(k2_relat_1(A_947))
      | ~ v1_xboole_0(A_947) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11982,c_14572])).

tff(c_14762,plain,(
    ! [B_948] :
      ( r1_tarski('#skF_4',B_948)
      | ~ v1_funct_1(k2_relat_1('#skF_4'))
      | ~ v1_relat_1(k2_relat_1('#skF_4'))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11981,c_14687])).

tff(c_14780,plain,(
    ! [B_949] : r1_tarski('#skF_4',B_949) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11982,c_11984,c_11981,c_11989,c_11981,c_14762])).

tff(c_12587,plain,(
    ! [C_834,A_835,B_836] :
      ( v1_funct_2(C_834,A_835,B_836)
      | ~ v1_partfun1(C_834,A_835)
      | ~ v1_funct_1(C_834)
      | ~ m1_subset_1(C_834,k1_zfmisc_1(k2_zfmisc_1(A_835,B_836))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_12602,plain,(
    ! [A_17,A_835,B_836] :
      ( v1_funct_2(A_17,A_835,B_836)
      | ~ v1_partfun1(A_17,A_835)
      | ~ v1_funct_1(A_17)
      | ~ r1_tarski(A_17,k2_zfmisc_1(A_835,B_836)) ) ),
    inference(resolution,[status(thm)],[c_30,c_12587])).

tff(c_14784,plain,(
    ! [A_835,B_836] :
      ( v1_funct_2('#skF_4',A_835,B_836)
      | ~ v1_partfun1('#skF_4',A_835)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14780,c_12602])).

tff(c_14889,plain,(
    ! [A_952,B_953] :
      ( v1_funct_2('#skF_4',A_952,B_953)
      | ~ v1_partfun1('#skF_4',A_952) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11989,c_14784])).

tff(c_12553,plain,(
    ! [B_40,C_41] :
      ( k1_relset_1('#skF_4',B_40,C_41) = '#skF_4'
      | ~ v1_funct_2(C_41,'#skF_4',B_40)
      | ~ m1_subset_1(C_41,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11983,c_11983,c_11983,c_11983,c_87])).

tff(c_14892,plain,(
    ! [B_953] :
      ( k1_relset_1('#skF_4',B_953,'#skF_4') = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
      | ~ v1_partfun1('#skF_4','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14889,c_12553])).

tff(c_14898,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12337,c_12034,c_13166,c_14892])).

tff(c_14900,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12678,c_14898])).

tff(c_14902,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_12661])).

tff(c_12166,plain,(
    ! [A_769] :
      ( k2_relat_1(k2_funct_1(A_769)) = k1_relat_1(A_769)
      | ~ v2_funct_1(A_769)
      | ~ v1_funct_1(A_769)
      | ~ v1_relat_1(A_769) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_16943,plain,(
    ! [A_1055] :
      ( v1_funct_2(k2_funct_1(A_1055),k1_relat_1(k2_funct_1(A_1055)),k1_relat_1(A_1055))
      | ~ v1_funct_1(k2_funct_1(A_1055))
      | ~ v1_relat_1(k2_funct_1(A_1055))
      | ~ v2_funct_1(A_1055)
      | ~ v1_funct_1(A_1055)
      | ~ v1_relat_1(A_1055) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12166,c_72])).

tff(c_16949,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14902,c_16943])).

tff(c_16957,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11984,c_11989,c_11988,c_11985,c_16949])).

tff(c_16958,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_16957])).

tff(c_16961,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_16958])).

tff(c_16965,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11984,c_11989,c_16961])).

tff(c_16967,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_16957])).

tff(c_9115,plain,(
    ! [A_20] :
      ( k1_relat_1(A_20) != '#skF_5'
      | A_20 = '#skF_5'
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9112,c_9112,c_36])).

tff(c_11972,plain,(
    ! [A_20] :
      ( k1_relat_1(A_20) != '#skF_4'
      | A_20 = '#skF_4'
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11967,c_11967,c_9115])).

tff(c_16975,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16967,c_11972])).

tff(c_17458,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_16975])).

tff(c_17461,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_17458])).

tff(c_17464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11984,c_11989,c_11988,c_11981,c_17461])).

tff(c_17465,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16975])).

tff(c_11976,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11967,c_9168])).

tff(c_12129,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11980,c_11976])).

tff(c_12133,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_12129])).

tff(c_17470,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17465,c_12133])).

tff(c_17479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_17470])).

tff(c_17481,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_46,plain,(
    ! [C_25,A_23,B_24] :
      ( v1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_17496,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_17481,c_46])).

tff(c_17599,plain,(
    ! [A_1073] :
      ( k1_relat_1(A_1073) != '#skF_5'
      | A_1073 = '#skF_5'
      | ~ v1_relat_1(A_1073) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9112,c_9112,c_36])).

tff(c_17617,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_17496,c_17599])).

tff(c_17655,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_17617])).

tff(c_18018,plain,
    ( k2_relat_1('#skF_5') != '#skF_5'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_18009,c_17655])).

tff(c_18025,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_86,c_80,c_9123,c_18018])).

tff(c_18026,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_17617])).

tff(c_17575,plain,(
    ! [A_1072] :
      ( k2_relat_1(A_1072) != '#skF_5'
      | A_1072 = '#skF_5'
      | ~ v1_relat_1(A_1072) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9112,c_9112,c_34])).

tff(c_17593,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_17496,c_17575])).

tff(c_17621,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_17593])).

tff(c_18028,plain,(
    k2_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18026,c_17621])).

tff(c_18036,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9123,c_18028])).

tff(c_18037,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_17593])).

tff(c_18041,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18037,c_17481])).

tff(c_18470,plain,(
    ! [C_1145,A_1146,B_1147] :
      ( v1_partfun1(C_1145,A_1146)
      | ~ m1_subset_1(C_1145,k1_zfmisc_1(k2_zfmisc_1(A_1146,B_1147)))
      | ~ v1_xboole_0(A_1146) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_18487,plain,
    ( v1_partfun1('#skF_5','#skF_4')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_18041,c_18470])).

tff(c_18493,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_18487])).

tff(c_18669,plain,(
    ! [A_1173,B_1174,C_1175] :
      ( k2_relset_1(A_1173,B_1174,C_1175) = k2_relat_1(C_1175)
      | ~ m1_subset_1(C_1175,k1_zfmisc_1(k2_zfmisc_1(A_1173,B_1174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_18688,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_18669])).

tff(c_18694,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_9123,c_18688])).

tff(c_18730,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18694,c_9118])).

tff(c_18740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18493,c_18730])).

tff(c_18742,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_18487])).

tff(c_17525,plain,(
    ! [A_1064,B_1065] :
      ( r2_hidden('#skF_2'(A_1064,B_1065),A_1064)
      | r1_tarski(A_1064,B_1065) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_17535,plain,(
    ! [A_1064,B_1065] :
      ( ~ v1_xboole_0(A_1064)
      | r1_tarski(A_1064,B_1065) ) ),
    inference(resolution,[status(thm)],[c_17525,c_2])).

tff(c_18111,plain,(
    ! [B_1115,A_1116] :
      ( B_1115 = A_1116
      | ~ r1_tarski(B_1115,A_1116)
      | ~ r1_tarski(A_1116,B_1115) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18127,plain,(
    ! [B_1117,A_1118] :
      ( B_1117 = A_1118
      | ~ r1_tarski(B_1117,A_1118)
      | ~ v1_xboole_0(A_1118) ) ),
    inference(resolution,[status(thm)],[c_17535,c_18111])).

tff(c_18145,plain,(
    ! [B_1119,A_1120] :
      ( B_1119 = A_1120
      | ~ v1_xboole_0(B_1119)
      | ~ v1_xboole_0(A_1120) ) ),
    inference(resolution,[status(thm)],[c_17535,c_18127])).

tff(c_18150,plain,(
    ! [A_1120] :
      ( A_1120 = '#skF_5'
      | ~ v1_xboole_0(A_1120) ) ),
    inference(resolution,[status(thm)],[c_9118,c_18145])).

tff(c_18764,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18742,c_18150])).

tff(c_18788,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_4',B_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18764,c_18764,c_9117])).

tff(c_17497,plain,(
    r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_17481,c_28])).

tff(c_18039,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18037,c_17497])).

tff(c_18120,plain,
    ( k2_zfmisc_1('#skF_4','#skF_3') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_18039,c_18111])).

tff(c_18285,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_18120])).

tff(c_18298,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_17535,c_18285])).

tff(c_18922,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18788,c_18298])).

tff(c_18925,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18742,c_18922])).

tff(c_18926,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_18120])).

tff(c_17557,plain,(
    ! [B_13,A_12] :
      ( B_13 = '#skF_5'
      | A_12 = '#skF_5'
      | k2_zfmisc_1(A_12,B_13) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9112,c_9112,c_9112,c_20])).

tff(c_18953,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_18926,c_17557])).

tff(c_18956,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_18953])).

tff(c_18977,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18956,c_9118])).

tff(c_18974,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18956,c_18956,c_9116])).

tff(c_18122,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_133,c_18111])).

tff(c_18232,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_18122])).

tff(c_18263,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_17535,c_18232])).

tff(c_19052,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18974,c_18263])).

tff(c_19055,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18977,c_19052])).

tff(c_19056,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18953])).

tff(c_19077,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19056,c_9118])).

tff(c_19075,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_3',B_13) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19056,c_19056,c_9117])).

tff(c_19175,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19075,c_18263])).

tff(c_19178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19077,c_19175])).

tff(c_19179,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_18122])).

tff(c_19196,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_19179,c_17557])).

tff(c_19215,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_19196])).

tff(c_19182,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19179,c_82])).

tff(c_19216,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19215,c_19215,c_19182])).

tff(c_19234,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19215,c_9112])).

tff(c_19344,plain,(
    ! [A_39] :
      ( v1_funct_2('#skF_3',A_39,'#skF_3')
      | A_39 = '#skF_3'
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19234,c_19234,c_19234,c_19234,c_19234,c_90])).

tff(c_19345,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_19344])).

tff(c_19358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19216,c_19345])).

tff(c_19464,plain,(
    ! [A_1195] :
      ( v1_funct_2('#skF_3',A_1195,'#skF_3')
      | A_1195 = '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_19344])).

tff(c_17480,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_18042,plain,(
    ~ v1_funct_2('#skF_5','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18037,c_17480])).

tff(c_19223,plain,(
    ~ v1_funct_2('#skF_3','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19215,c_18042])).

tff(c_19468,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_19464,c_19223])).

tff(c_19237,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19215,c_84])).

tff(c_19483,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19468,c_19468,c_19237])).

tff(c_19476,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19468,c_19468,c_19223])).

tff(c_19664,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19483,c_19476])).

tff(c_19665,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_19196])).

tff(c_19686,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19665,c_221])).

tff(c_19690,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19665,c_86])).

tff(c_19689,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19665,c_80])).

tff(c_19683,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19665,c_19665,c_9123])).

tff(c_19675,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19665,c_19665,c_18037])).

tff(c_19839,plain,(
    ! [A_1207] :
      ( k2_relat_1(k2_funct_1(A_1207)) = k1_relat_1(A_1207)
      | ~ v2_funct_1(A_1207)
      | ~ v1_funct_1(A_1207)
      | ~ v1_relat_1(A_1207) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_19857,plain,
    ( k2_relat_1('#skF_4') = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_19675,c_19839])).

tff(c_19861,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19686,c_19690,c_19689,c_19683,c_19857])).

tff(c_19667,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19665,c_19665,c_19182])).

tff(c_19682,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_4',B_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19665,c_19665,c_9117])).

tff(c_20035,plain,(
    ! [A_1220,B_1221,C_1222] :
      ( k1_relset_1(A_1220,B_1221,C_1222) = k1_relat_1(C_1222)
      | ~ m1_subset_1(C_1222,k1_zfmisc_1(k2_zfmisc_1(A_1220,B_1221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_20236,plain,(
    ! [B_1254,C_1255] :
      ( k1_relset_1('#skF_4',B_1254,C_1255) = k1_relat_1(C_1255)
      | ~ m1_subset_1(C_1255,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19682,c_20035])).

tff(c_20238,plain,(
    ! [B_1254] : k1_relset_1('#skF_4',B_1254,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_19667,c_20236])).

tff(c_20243,plain,(
    ! [B_1254] : k1_relset_1('#skF_4',B_1254,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19861,c_20238])).

tff(c_19685,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19665,c_9112])).

tff(c_20315,plain,(
    ! [C_1269,B_1270] :
      ( v1_funct_2(C_1269,'#skF_4',B_1270)
      | k1_relset_1('#skF_4',B_1270,C_1269) != '#skF_4'
      | ~ m1_subset_1(C_1269,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19685,c_19685,c_19685,c_19685,c_88])).

tff(c_20317,plain,(
    ! [B_1270] :
      ( v1_funct_2('#skF_4','#skF_4',B_1270)
      | k1_relset_1('#skF_4',B_1270,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_19667,c_20315])).

tff(c_20323,plain,(
    ! [B_1270] : v1_funct_2('#skF_4','#skF_4',B_1270) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20243,c_20317])).

tff(c_19674,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19665,c_18042])).

tff(c_20328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20323,c_19674])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:27:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.26/3.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.47/3.94  
% 11.47/3.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.47/3.94  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 11.47/3.94  
% 11.47/3.94  %Foreground sorts:
% 11.47/3.94  
% 11.47/3.94  
% 11.47/3.94  %Background operators:
% 11.47/3.94  
% 11.47/3.94  
% 11.47/3.94  %Foreground operators:
% 11.47/3.94  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.47/3.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.47/3.94  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.47/3.94  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.47/3.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.47/3.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.47/3.94  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.47/3.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.47/3.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.47/3.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.47/3.94  tff('#skF_5', type, '#skF_5': $i).
% 11.47/3.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.47/3.94  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 11.47/3.94  tff('#skF_3', type, '#skF_3': $i).
% 11.47/3.94  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.47/3.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.47/3.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.47/3.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.47/3.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.47/3.94  tff('#skF_4', type, '#skF_4': $i).
% 11.47/3.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.47/3.94  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.47/3.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.47/3.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.47/3.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.47/3.94  
% 11.67/3.98  tff(f_166, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 11.67/3.98  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.67/3.98  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.67/3.98  tff(f_92, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 11.67/3.98  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 11.67/3.98  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 11.67/3.98  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.67/3.98  tff(f_139, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 11.67/3.98  tff(f_149, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 11.67/3.98  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.67/3.98  tff(f_66, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 11.67/3.98  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.67/3.98  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.67/3.98  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.67/3.98  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.67/3.98  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.67/3.98  tff(f_121, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 11.67/3.98  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 11.67/3.98  tff(c_82, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 11.67/3.98  tff(c_208, plain, (![C_71, A_72, B_73]: (v1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.67/3.98  tff(c_221, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_208])).
% 11.67/3.98  tff(c_86, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_166])).
% 11.67/3.98  tff(c_80, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_166])).
% 11.67/3.98  tff(c_78, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_166])).
% 11.67/3.98  tff(c_8478, plain, (![A_419, B_420, C_421]: (k2_relset_1(A_419, B_420, C_421)=k2_relat_1(C_421) | ~m1_subset_1(C_421, k1_zfmisc_1(k2_zfmisc_1(A_419, B_420))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.67/3.98  tff(c_8491, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_8478])).
% 11.67/3.98  tff(c_8502, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_8491])).
% 11.67/3.98  tff(c_44, plain, (![A_22]: (k1_relat_1(k2_funct_1(A_22))=k2_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.67/3.98  tff(c_38, plain, (![A_21]: (v1_funct_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.67/3.98  tff(c_76, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 11.67/3.98  tff(c_148, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_76])).
% 11.67/3.98  tff(c_151, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_148])).
% 11.67/3.98  tff(c_154, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_151])).
% 11.67/3.98  tff(c_189, plain, (![C_68, A_69, B_70]: (v1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.67/3.98  tff(c_196, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_189])).
% 11.67/3.98  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_196])).
% 11.67/3.98  tff(c_206, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_76])).
% 11.67/3.98  tff(c_239, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_206])).
% 11.67/3.98  tff(c_915, plain, (![A_160, B_161, C_162]: (k2_relset_1(A_160, B_161, C_162)=k2_relat_1(C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.67/3.98  tff(c_925, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_915])).
% 11.67/3.98  tff(c_935, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_925])).
% 11.67/3.98  tff(c_40, plain, (![A_21]: (v1_relat_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.67/3.98  tff(c_207, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_76])).
% 11.67/3.98  tff(c_34, plain, (![A_20]: (k2_relat_1(A_20)!=k1_xboole_0 | k1_xboole_0=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.67/3.98  tff(c_228, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_221, c_34])).
% 11.67/3.98  tff(c_230, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_228])).
% 11.67/3.98  tff(c_936, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_935, c_230])).
% 11.67/3.98  tff(c_84, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_166])).
% 11.67/3.98  tff(c_747, plain, (![A_135, B_136, C_137]: (k1_relset_1(A_135, B_136, C_137)=k1_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.67/3.98  tff(c_762, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_747])).
% 11.67/3.98  tff(c_1220, plain, (![B_190, A_191, C_192]: (k1_xboole_0=B_190 | k1_relset_1(A_191, B_190, C_192)=A_191 | ~v1_funct_2(C_192, A_191, B_190) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_191, B_190))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.67/3.98  tff(c_1233, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_82, c_1220])).
% 11.67/3.98  tff(c_1248, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_762, c_1233])).
% 11.67/3.98  tff(c_1249, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_936, c_1248])).
% 11.67/3.98  tff(c_709, plain, (![A_128]: (k2_relat_1(k2_funct_1(A_128))=k1_relat_1(A_128) | ~v2_funct_1(A_128) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.67/3.98  tff(c_72, plain, (![A_42]: (v1_funct_2(A_42, k1_relat_1(A_42), k2_relat_1(A_42)) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.67/3.98  tff(c_6153, plain, (![A_332]: (v1_funct_2(k2_funct_1(A_332), k1_relat_1(k2_funct_1(A_332)), k1_relat_1(A_332)) | ~v1_funct_1(k2_funct_1(A_332)) | ~v1_relat_1(k2_funct_1(A_332)) | ~v2_funct_1(A_332) | ~v1_funct_1(A_332) | ~v1_relat_1(A_332))), inference(superposition, [status(thm), theory('equality')], [c_709, c_72])).
% 11.67/3.98  tff(c_6168, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1249, c_6153])).
% 11.67/3.98  tff(c_6177, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_86, c_80, c_207, c_6168])).
% 11.67/3.98  tff(c_6178, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_6177])).
% 11.67/3.98  tff(c_6181, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_6178])).
% 11.67/3.98  tff(c_6185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_86, c_6181])).
% 11.67/3.98  tff(c_6187, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_6177])).
% 11.67/3.98  tff(c_42, plain, (![A_22]: (k2_relat_1(k2_funct_1(A_22))=k1_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.67/3.98  tff(c_791, plain, (![A_143]: (m1_subset_1(A_143, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_143), k2_relat_1(A_143)))) | ~v1_funct_1(A_143) | ~v1_relat_1(A_143))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.67/3.98  tff(c_7675, plain, (![A_344]: (m1_subset_1(k2_funct_1(A_344), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_344)), k1_relat_1(A_344)))) | ~v1_funct_1(k2_funct_1(A_344)) | ~v1_relat_1(k2_funct_1(A_344)) | ~v2_funct_1(A_344) | ~v1_funct_1(A_344) | ~v1_relat_1(A_344))), inference(superposition, [status(thm), theory('equality')], [c_42, c_791])).
% 11.67/3.98  tff(c_7717, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1249, c_7675])).
% 11.67/3.98  tff(c_7734, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_86, c_80, c_6187, c_207, c_7717])).
% 11.67/3.98  tff(c_7764, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), '#skF_3'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_44, c_7734])).
% 11.67/3.98  tff(c_7785, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_86, c_80, c_935, c_7764])).
% 11.67/3.98  tff(c_7787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_239, c_7785])).
% 11.67/3.98  tff(c_7788, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_206])).
% 11.67/3.98  tff(c_8503, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8502, c_230])).
% 11.67/3.98  tff(c_8422, plain, (![A_411, B_412, C_413]: (k1_relset_1(A_411, B_412, C_413)=k1_relat_1(C_413) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(A_411, B_412))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.67/3.98  tff(c_8445, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_8422])).
% 11.67/3.98  tff(c_8743, plain, (![B_443, A_444, C_445]: (k1_xboole_0=B_443 | k1_relset_1(A_444, B_443, C_445)=A_444 | ~v1_funct_2(C_445, A_444, B_443) | ~m1_subset_1(C_445, k1_zfmisc_1(k2_zfmisc_1(A_444, B_443))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.67/3.98  tff(c_8759, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_82, c_8743])).
% 11.67/3.98  tff(c_8776, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_8445, c_8759])).
% 11.67/3.98  tff(c_8777, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_8503, c_8776])).
% 11.67/3.98  tff(c_36, plain, (![A_20]: (k1_relat_1(A_20)!=k1_xboole_0 | k1_xboole_0=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.67/3.98  tff(c_229, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_221, c_36])).
% 11.67/3.98  tff(c_232, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_229])).
% 11.67/3.98  tff(c_8788, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8777, c_232])).
% 11.67/3.98  tff(c_7789, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_206])).
% 11.67/3.98  tff(c_8443, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_7789, c_8422])).
% 11.67/3.98  tff(c_8819, plain, (![B_447, C_448, A_449]: (k1_xboole_0=B_447 | v1_funct_2(C_448, A_449, B_447) | k1_relset_1(A_449, B_447, C_448)!=A_449 | ~m1_subset_1(C_448, k1_zfmisc_1(k2_zfmisc_1(A_449, B_447))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.67/3.98  tff(c_8825, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_7789, c_8819])).
% 11.67/3.98  tff(c_8841, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8443, c_8825])).
% 11.67/3.98  tff(c_8842, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_7788, c_8788, c_8841])).
% 11.67/3.98  tff(c_8851, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_44, c_8842])).
% 11.67/3.98  tff(c_8854, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_86, c_80, c_8502, c_8851])).
% 11.67/3.98  tff(c_8855, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_229])).
% 11.67/3.98  tff(c_8857, plain, (k2_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8855, c_230])).
% 11.67/3.98  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.67/3.98  tff(c_8862, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8855, c_12])).
% 11.67/3.98  tff(c_32, plain, (![A_19]: (v1_xboole_0(k2_relat_1(A_19)) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.67/3.98  tff(c_8968, plain, (![A_462, B_463]: (r2_hidden('#skF_2'(A_462, B_463), A_462) | r1_tarski(A_462, B_463))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.67/3.98  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.67/3.98  tff(c_8978, plain, (![A_462, B_463]: (~v1_xboole_0(A_462) | r1_tarski(A_462, B_463))), inference(resolution, [status(thm)], [c_8968, c_2])).
% 11.67/3.98  tff(c_9050, plain, (![B_473, A_474]: (B_473=A_474 | ~r1_tarski(B_473, A_474) | ~r1_tarski(A_474, B_473))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.67/3.98  tff(c_9070, plain, (![B_478, A_479]: (B_478=A_479 | ~r1_tarski(B_478, A_479) | ~v1_xboole_0(A_479))), inference(resolution, [status(thm)], [c_8978, c_9050])).
% 11.67/3.98  tff(c_9084, plain, (![B_480, A_481]: (B_480=A_481 | ~v1_xboole_0(B_480) | ~v1_xboole_0(A_481))), inference(resolution, [status(thm)], [c_8978, c_9070])).
% 11.67/3.98  tff(c_9091, plain, (![A_482]: (A_482='#skF_5' | ~v1_xboole_0(A_482))), inference(resolution, [status(thm)], [c_8862, c_9084])).
% 11.67/3.98  tff(c_9101, plain, (![A_483]: (k2_relat_1(A_483)='#skF_5' | ~v1_xboole_0(A_483))), inference(resolution, [status(thm)], [c_32, c_9091])).
% 11.67/3.98  tff(c_9104, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_8862, c_9101])).
% 11.67/3.98  tff(c_9111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8857, c_9104])).
% 11.67/3.98  tff(c_9112, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_228])).
% 11.67/3.98  tff(c_9113, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_228])).
% 11.67/3.98  tff(c_9123, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_9112, c_9113])).
% 11.67/3.98  tff(c_18009, plain, (![A_1110]: (k1_relat_1(k2_funct_1(A_1110))=k2_relat_1(A_1110) | ~v2_funct_1(A_1110) | ~v1_funct_1(A_1110) | ~v1_relat_1(A_1110))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.67/3.98  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.67/3.98  tff(c_9732, plain, (![A_558, B_559, C_560]: (k2_relset_1(A_558, B_559, C_560)=k2_relat_1(C_560) | ~m1_subset_1(C_560, k1_zfmisc_1(k2_zfmisc_1(A_558, B_559))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.67/3.98  tff(c_9745, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_9732])).
% 11.67/3.98  tff(c_9748, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_9123, c_9745])).
% 11.67/3.98  tff(c_9118, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9112, c_12])).
% 11.67/3.98  tff(c_9776, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9748, c_9118])).
% 11.67/3.98  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.67/3.98  tff(c_9116, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9112, c_9112, c_22])).
% 11.67/3.98  tff(c_9773, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9748, c_9748, c_9116])).
% 11.67/3.98  tff(c_9265, plain, (![A_503, B_504]: (r2_hidden('#skF_2'(A_503, B_504), A_503) | r1_tarski(A_503, B_504))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.67/3.98  tff(c_9275, plain, (![A_503, B_504]: (~v1_xboole_0(A_503) | r1_tarski(A_503, B_504))), inference(resolution, [status(thm)], [c_9265, c_2])).
% 11.67/3.98  tff(c_129, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.67/3.98  tff(c_133, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_129])).
% 11.67/3.98  tff(c_9295, plain, (![B_507, A_508]: (B_507=A_508 | ~r1_tarski(B_507, A_508) | ~r1_tarski(A_508, B_507))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.67/3.98  tff(c_9303, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_133, c_9295])).
% 11.67/3.98  tff(c_9318, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_9303])).
% 11.67/3.98  tff(c_9322, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_9275, c_9318])).
% 11.67/3.98  tff(c_9889, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9773, c_9322])).
% 11.67/3.98  tff(c_9892, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9776, c_9889])).
% 11.67/3.98  tff(c_9893, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_9303])).
% 11.67/3.98  tff(c_20, plain, (![B_13, A_12]: (k1_xboole_0=B_13 | k1_xboole_0=A_12 | k2_zfmisc_1(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.67/3.98  tff(c_9181, plain, (![B_13, A_12]: (B_13='#skF_5' | A_12='#skF_5' | k2_zfmisc_1(A_12, B_13)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9112, c_9112, c_9112, c_20])).
% 11.67/3.98  tff(c_9918, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_9893, c_9181])).
% 11.67/3.98  tff(c_9936, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_9918])).
% 11.67/3.98  tff(c_9950, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9936, c_9936, c_9123])).
% 11.67/3.98  tff(c_30, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.67/3.98  tff(c_9952, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9936, c_9112])).
% 11.67/3.98  tff(c_58, plain, (![A_39]: (v1_funct_2(k1_xboole_0, A_39, k1_xboole_0) | k1_xboole_0=A_39 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_39, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.67/3.98  tff(c_90, plain, (![A_39]: (v1_funct_2(k1_xboole_0, A_39, k1_xboole_0) | k1_xboole_0=A_39 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_58])).
% 11.67/3.98  tff(c_9971, plain, (![A_39]: (v1_funct_2('#skF_3', A_39, '#skF_3') | A_39='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_9952, c_9952, c_9952, c_9952, c_9952, c_90])).
% 11.67/3.98  tff(c_9972, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_9971])).
% 11.67/3.98  tff(c_9985, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_9972])).
% 11.67/3.98  tff(c_9989, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_9985])).
% 11.67/3.98  tff(c_9991, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_9971])).
% 11.67/3.98  tff(c_24, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.67/3.98  tff(c_9117, plain, (![B_13]: (k2_zfmisc_1('#skF_5', B_13)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9112, c_9112, c_24])).
% 11.67/3.98  tff(c_9949, plain, (![B_13]: (k2_zfmisc_1('#skF_3', B_13)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9936, c_9936, c_9117])).
% 11.67/3.98  tff(c_10182, plain, (![A_583, B_584, C_585]: (k2_relset_1(A_583, B_584, C_585)=k2_relat_1(C_585) | ~m1_subset_1(C_585, k1_zfmisc_1(k2_zfmisc_1(A_583, B_584))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.67/3.98  tff(c_10764, plain, (![B_662, C_663]: (k2_relset_1('#skF_3', B_662, C_663)=k2_relat_1(C_663) | ~m1_subset_1(C_663, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_9949, c_10182])).
% 11.67/3.98  tff(c_10766, plain, (![B_662]: (k2_relset_1('#skF_3', B_662, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_9991, c_10764])).
% 11.67/3.98  tff(c_10783, plain, (![B_666]: (k2_relset_1('#skF_3', B_666, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9950, c_10766])).
% 11.67/3.98  tff(c_9955, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9936, c_78])).
% 11.67/3.98  tff(c_10790, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_10783, c_9955])).
% 11.67/3.98  tff(c_9953, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9936, c_221])).
% 11.67/3.98  tff(c_10852, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10790, c_9953])).
% 11.67/3.98  tff(c_9958, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9936, c_86])).
% 11.67/3.98  tff(c_10850, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10790, c_9958])).
% 11.67/3.98  tff(c_9957, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9936, c_80])).
% 11.67/3.98  tff(c_10851, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10790, c_9957])).
% 11.67/3.98  tff(c_10268, plain, (![A_589, B_590, C_591]: (k1_relset_1(A_589, B_590, C_591)=k1_relat_1(C_591) | ~m1_subset_1(C_591, k1_zfmisc_1(k2_zfmisc_1(A_589, B_590))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.67/3.98  tff(c_10589, plain, (![B_648, C_649]: (k1_relset_1('#skF_3', B_648, C_649)=k1_relat_1(C_649) | ~m1_subset_1(C_649, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_9949, c_10268])).
% 11.67/3.98  tff(c_10616, plain, (![B_653]: (k1_relset_1('#skF_3', B_653, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_9991, c_10589])).
% 11.67/3.98  tff(c_9956, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9936, c_84])).
% 11.67/3.98  tff(c_66, plain, (![B_40, C_41]: (k1_relset_1(k1_xboole_0, B_40, C_41)=k1_xboole_0 | ~v1_funct_2(C_41, k1_xboole_0, B_40) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_40))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.67/3.98  tff(c_87, plain, (![B_40, C_41]: (k1_relset_1(k1_xboole_0, B_40, C_41)=k1_xboole_0 | ~v1_funct_2(C_41, k1_xboole_0, B_40) | ~m1_subset_1(C_41, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_66])).
% 11.67/3.98  tff(c_10412, plain, (![B_614, C_615]: (k1_relset_1('#skF_3', B_614, C_615)='#skF_3' | ~v1_funct_2(C_615, '#skF_3', B_614) | ~m1_subset_1(C_615, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_9952, c_9952, c_9952, c_9952, c_87])).
% 11.67/3.98  tff(c_10417, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_9956, c_10412])).
% 11.67/3.98  tff(c_10424, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9991, c_10417])).
% 11.67/3.98  tff(c_10623, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_10616, c_10424])).
% 11.67/3.98  tff(c_10810, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10790, c_10790, c_10623])).
% 11.67/3.98  tff(c_9954, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9936, c_207])).
% 11.67/3.98  tff(c_10849, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10790, c_9954])).
% 11.67/3.98  tff(c_10127, plain, (![A_576]: (k2_relat_1(k2_funct_1(A_576))=k1_relat_1(A_576) | ~v2_funct_1(A_576) | ~v1_funct_1(A_576) | ~v1_relat_1(A_576))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.67/3.98  tff(c_11907, plain, (![A_759]: (v1_funct_2(k2_funct_1(A_759), k1_relat_1(k2_funct_1(A_759)), k1_relat_1(A_759)) | ~v1_funct_1(k2_funct_1(A_759)) | ~v1_relat_1(k2_funct_1(A_759)) | ~v2_funct_1(A_759) | ~v1_funct_1(A_759) | ~v1_relat_1(A_759))), inference(superposition, [status(thm), theory('equality')], [c_10127, c_72])).
% 11.67/3.98  tff(c_11913, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10810, c_11907])).
% 11.67/3.98  tff(c_11921, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10852, c_10850, c_10851, c_10849, c_11913])).
% 11.67/3.98  tff(c_11922, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_11921])).
% 11.67/3.98  tff(c_11925, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_11922])).
% 11.67/3.98  tff(c_11929, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10852, c_10850, c_11925])).
% 11.67/3.98  tff(c_11931, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_11921])).
% 11.67/3.98  tff(c_9114, plain, (![A_20]: (k2_relat_1(A_20)!='#skF_5' | A_20='#skF_5' | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_9112, c_9112, c_34])).
% 11.67/3.98  tff(c_9942, plain, (![A_20]: (k2_relat_1(A_20)!='#skF_3' | A_20='#skF_3' | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_9936, c_9936, c_9114])).
% 11.67/3.98  tff(c_10834, plain, (![A_20]: (k2_relat_1(A_20)!='#skF_4' | A_20='#skF_4' | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_10790, c_10790, c_9942])).
% 11.67/3.98  tff(c_11939, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_11931, c_10834])).
% 11.67/3.98  tff(c_11945, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_11939])).
% 11.67/3.98  tff(c_11948, plain, (k1_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_42, c_11945])).
% 11.67/3.98  tff(c_11951, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10852, c_10850, c_10851, c_10810, c_11948])).
% 11.67/3.98  tff(c_11952, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_11939])).
% 11.67/3.98  tff(c_9948, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9936, c_9936, c_9116])).
% 11.67/3.98  tff(c_9168, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_206])).
% 11.67/3.98  tff(c_9945, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_9936, c_9168])).
% 11.67/3.98  tff(c_10091, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9948, c_9945])).
% 11.67/3.98  tff(c_10095, plain, (~r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_30, c_10091])).
% 11.67/3.98  tff(c_10840, plain, (~r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10790, c_10790, c_10095])).
% 11.67/3.98  tff(c_11957, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11952, c_10840])).
% 11.67/3.98  tff(c_11966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_11957])).
% 11.67/3.98  tff(c_11967, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_9918])).
% 11.67/3.98  tff(c_11984, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11967, c_221])).
% 11.67/3.98  tff(c_11989, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11967, c_86])).
% 11.67/3.98  tff(c_11988, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11967, c_80])).
% 11.67/3.98  tff(c_11981, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11967, c_11967, c_9123])).
% 11.67/3.98  tff(c_11985, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11967, c_207])).
% 11.67/3.98  tff(c_11983, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11967, c_9112])).
% 11.67/3.98  tff(c_11994, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_90])).
% 11.67/3.98  tff(c_12014, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11983, c_11983, c_11994])).
% 11.67/3.98  tff(c_12017, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_12014])).
% 11.67/3.98  tff(c_12021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_12017])).
% 11.67/3.98  tff(c_12023, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_90])).
% 11.67/3.98  tff(c_12034, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11983, c_11983, c_12023])).
% 11.67/3.98  tff(c_11980, plain, (![B_13]: (k2_zfmisc_1('#skF_4', B_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11967, c_11967, c_9117])).
% 11.67/3.98  tff(c_12390, plain, (![A_798, B_799, C_800]: (k1_relset_1(A_798, B_799, C_800)=k1_relat_1(C_800) | ~m1_subset_1(C_800, k1_zfmisc_1(k2_zfmisc_1(A_798, B_799))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.67/3.98  tff(c_12545, plain, (![B_825, C_826]: (k1_relset_1('#skF_4', B_825, C_826)=k1_relat_1(C_826) | ~m1_subset_1(C_826, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_11980, c_12390])).
% 11.67/3.98  tff(c_12551, plain, (![B_825]: (k1_relset_1('#skF_4', B_825, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_12034, c_12545])).
% 11.67/3.98  tff(c_62, plain, (![C_41, B_40]: (v1_funct_2(C_41, k1_xboole_0, B_40) | k1_relset_1(k1_xboole_0, B_40, C_41)!=k1_xboole_0 | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_40))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.67/3.98  tff(c_88, plain, (![C_41, B_40]: (v1_funct_2(C_41, k1_xboole_0, B_40) | k1_relset_1(k1_xboole_0, B_40, C_41)!=k1_xboole_0 | ~m1_subset_1(C_41, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_62])).
% 11.67/3.98  tff(c_12654, plain, (![C_846, B_847]: (v1_funct_2(C_846, '#skF_4', B_847) | k1_relset_1('#skF_4', B_847, C_846)!='#skF_4' | ~m1_subset_1(C_846, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11983, c_11983, c_11983, c_11983, c_88])).
% 11.67/3.98  tff(c_12656, plain, (![B_847]: (v1_funct_2('#skF_4', '#skF_4', B_847) | k1_relset_1('#skF_4', B_847, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_12034, c_12654])).
% 11.67/3.98  tff(c_12661, plain, (![B_847]: (v1_funct_2('#skF_4', '#skF_4', B_847) | k1_relat_1('#skF_4')!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12551, c_12656])).
% 11.67/3.98  tff(c_12678, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_12661])).
% 11.67/3.98  tff(c_11982, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11967, c_9118])).
% 11.67/3.98  tff(c_12315, plain, (![C_782, A_783, B_784]: (v1_partfun1(C_782, A_783) | ~m1_subset_1(C_782, k1_zfmisc_1(k2_zfmisc_1(A_783, B_784))) | ~v1_xboole_0(A_783))), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.67/3.98  tff(c_12321, plain, (![C_782]: (v1_partfun1(C_782, '#skF_4') | ~m1_subset_1(C_782, k1_zfmisc_1('#skF_4')) | ~v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11980, c_12315])).
% 11.67/3.98  tff(c_12329, plain, (![C_785]: (v1_partfun1(C_785, '#skF_4') | ~m1_subset_1(C_785, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11982, c_12321])).
% 11.67/3.98  tff(c_12337, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_12034, c_12329])).
% 11.67/3.98  tff(c_13123, plain, (![A_891, B_892, A_893]: (k1_relset_1(A_891, B_892, A_893)=k1_relat_1(A_893) | ~r1_tarski(A_893, k2_zfmisc_1(A_891, B_892)))), inference(resolution, [status(thm)], [c_30, c_12390])).
% 11.67/3.98  tff(c_13161, plain, (![A_896, B_897, A_898]: (k1_relset_1(A_896, B_897, A_898)=k1_relat_1(A_898) | ~v1_xboole_0(A_898))), inference(resolution, [status(thm)], [c_9275, c_13123])).
% 11.67/3.98  tff(c_13166, plain, (![A_896, B_897]: (k1_relset_1(A_896, B_897, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_11982, c_13161])).
% 11.67/3.98  tff(c_11979, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11967, c_11967, c_9116])).
% 11.67/3.98  tff(c_12156, plain, (![B_767, A_768]: (B_767=A_768 | ~r1_tarski(B_767, A_768) | ~v1_xboole_0(A_768))), inference(resolution, [status(thm)], [c_9275, c_9295])).
% 11.67/3.98  tff(c_12184, plain, (![B_770, A_771]: (B_770=A_771 | ~v1_xboole_0(B_770) | ~v1_xboole_0(A_771))), inference(resolution, [status(thm)], [c_9275, c_12156])).
% 11.67/3.98  tff(c_12191, plain, (![A_772]: (A_772='#skF_4' | ~v1_xboole_0(A_772))), inference(resolution, [status(thm)], [c_11982, c_12184])).
% 11.67/3.98  tff(c_12201, plain, (![A_773]: (k2_relat_1(A_773)='#skF_4' | ~v1_xboole_0(A_773))), inference(resolution, [status(thm)], [c_32, c_12191])).
% 11.67/3.98  tff(c_12210, plain, (![A_19]: (k2_relat_1(k2_relat_1(A_19))='#skF_4' | ~v1_xboole_0(A_19))), inference(resolution, [status(thm)], [c_32, c_12201])).
% 11.67/3.98  tff(c_12470, plain, (![A_817]: (m1_subset_1(A_817, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_817), k2_relat_1(A_817)))) | ~v1_funct_1(A_817) | ~v1_relat_1(A_817))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.67/3.98  tff(c_28, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.67/3.98  tff(c_12970, plain, (![A_869]: (r1_tarski(A_869, k2_zfmisc_1(k1_relat_1(A_869), k2_relat_1(A_869))) | ~v1_funct_1(A_869) | ~v1_relat_1(A_869))), inference(resolution, [status(thm)], [c_12470, c_28])).
% 11.67/3.98  tff(c_12996, plain, (![A_19]: (r1_tarski(k2_relat_1(A_19), k2_zfmisc_1(k1_relat_1(k2_relat_1(A_19)), '#skF_4')) | ~v1_funct_1(k2_relat_1(A_19)) | ~v1_relat_1(k2_relat_1(A_19)) | ~v1_xboole_0(A_19))), inference(superposition, [status(thm), theory('equality')], [c_12210, c_12970])).
% 11.67/3.98  tff(c_14568, plain, (![A_936]: (r1_tarski(k2_relat_1(A_936), '#skF_4') | ~v1_funct_1(k2_relat_1(A_936)) | ~v1_relat_1(k2_relat_1(A_936)) | ~v1_xboole_0(A_936))), inference(demodulation, [status(thm), theory('equality')], [c_11979, c_12996])).
% 11.67/3.98  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.67/3.98  tff(c_9895, plain, (![C_562, B_563, A_564]: (r2_hidden(C_562, B_563) | ~r2_hidden(C_562, A_564) | ~r1_tarski(A_564, B_563))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.67/3.98  tff(c_13100, plain, (![A_885, B_886, B_887]: (r2_hidden('#skF_2'(A_885, B_886), B_887) | ~r1_tarski(A_885, B_887) | r1_tarski(A_885, B_886))), inference(resolution, [status(thm)], [c_10, c_9895])).
% 11.67/3.98  tff(c_13112, plain, (![B_887, A_885, B_886]: (~v1_xboole_0(B_887) | ~r1_tarski(A_885, B_887) | r1_tarski(A_885, B_886))), inference(resolution, [status(thm)], [c_13100, c_2])).
% 11.67/3.98  tff(c_14572, plain, (![A_936, B_886]: (~v1_xboole_0('#skF_4') | r1_tarski(k2_relat_1(A_936), B_886) | ~v1_funct_1(k2_relat_1(A_936)) | ~v1_relat_1(k2_relat_1(A_936)) | ~v1_xboole_0(A_936))), inference(resolution, [status(thm)], [c_14568, c_13112])).
% 11.67/3.98  tff(c_14687, plain, (![A_947, B_948]: (r1_tarski(k2_relat_1(A_947), B_948) | ~v1_funct_1(k2_relat_1(A_947)) | ~v1_relat_1(k2_relat_1(A_947)) | ~v1_xboole_0(A_947))), inference(demodulation, [status(thm), theory('equality')], [c_11982, c_14572])).
% 11.67/3.98  tff(c_14762, plain, (![B_948]: (r1_tarski('#skF_4', B_948) | ~v1_funct_1(k2_relat_1('#skF_4')) | ~v1_relat_1(k2_relat_1('#skF_4')) | ~v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11981, c_14687])).
% 11.67/3.98  tff(c_14780, plain, (![B_949]: (r1_tarski('#skF_4', B_949))), inference(demodulation, [status(thm), theory('equality')], [c_11982, c_11984, c_11981, c_11989, c_11981, c_14762])).
% 11.67/3.98  tff(c_12587, plain, (![C_834, A_835, B_836]: (v1_funct_2(C_834, A_835, B_836) | ~v1_partfun1(C_834, A_835) | ~v1_funct_1(C_834) | ~m1_subset_1(C_834, k1_zfmisc_1(k2_zfmisc_1(A_835, B_836))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.67/3.98  tff(c_12602, plain, (![A_17, A_835, B_836]: (v1_funct_2(A_17, A_835, B_836) | ~v1_partfun1(A_17, A_835) | ~v1_funct_1(A_17) | ~r1_tarski(A_17, k2_zfmisc_1(A_835, B_836)))), inference(resolution, [status(thm)], [c_30, c_12587])).
% 11.67/3.98  tff(c_14784, plain, (![A_835, B_836]: (v1_funct_2('#skF_4', A_835, B_836) | ~v1_partfun1('#skF_4', A_835) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_14780, c_12602])).
% 11.67/3.98  tff(c_14889, plain, (![A_952, B_953]: (v1_funct_2('#skF_4', A_952, B_953) | ~v1_partfun1('#skF_4', A_952))), inference(demodulation, [status(thm), theory('equality')], [c_11989, c_14784])).
% 11.67/3.98  tff(c_12553, plain, (![B_40, C_41]: (k1_relset_1('#skF_4', B_40, C_41)='#skF_4' | ~v1_funct_2(C_41, '#skF_4', B_40) | ~m1_subset_1(C_41, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11983, c_11983, c_11983, c_11983, c_87])).
% 11.67/3.98  tff(c_14892, plain, (![B_953]: (k1_relset_1('#skF_4', B_953, '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_partfun1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_14889, c_12553])).
% 11.67/3.98  tff(c_14898, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12337, c_12034, c_13166, c_14892])).
% 11.67/3.98  tff(c_14900, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12678, c_14898])).
% 11.67/3.98  tff(c_14902, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_12661])).
% 11.67/3.98  tff(c_12166, plain, (![A_769]: (k2_relat_1(k2_funct_1(A_769))=k1_relat_1(A_769) | ~v2_funct_1(A_769) | ~v1_funct_1(A_769) | ~v1_relat_1(A_769))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.67/3.98  tff(c_16943, plain, (![A_1055]: (v1_funct_2(k2_funct_1(A_1055), k1_relat_1(k2_funct_1(A_1055)), k1_relat_1(A_1055)) | ~v1_funct_1(k2_funct_1(A_1055)) | ~v1_relat_1(k2_funct_1(A_1055)) | ~v2_funct_1(A_1055) | ~v1_funct_1(A_1055) | ~v1_relat_1(A_1055))), inference(superposition, [status(thm), theory('equality')], [c_12166, c_72])).
% 11.67/3.98  tff(c_16949, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14902, c_16943])).
% 11.67/3.98  tff(c_16957, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11984, c_11989, c_11988, c_11985, c_16949])).
% 11.67/3.98  tff(c_16958, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_16957])).
% 11.67/3.98  tff(c_16961, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_16958])).
% 11.67/3.98  tff(c_16965, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11984, c_11989, c_16961])).
% 11.67/3.98  tff(c_16967, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_16957])).
% 11.67/3.98  tff(c_9115, plain, (![A_20]: (k1_relat_1(A_20)!='#skF_5' | A_20='#skF_5' | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_9112, c_9112, c_36])).
% 11.67/3.98  tff(c_11972, plain, (![A_20]: (k1_relat_1(A_20)!='#skF_4' | A_20='#skF_4' | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_11967, c_11967, c_9115])).
% 11.67/3.98  tff(c_16975, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_16967, c_11972])).
% 11.67/3.98  tff(c_17458, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_16975])).
% 11.67/3.98  tff(c_17461, plain, (k2_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_44, c_17458])).
% 11.67/3.98  tff(c_17464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11984, c_11989, c_11988, c_11981, c_17461])).
% 11.67/3.98  tff(c_17465, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_16975])).
% 11.67/3.98  tff(c_11976, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_11967, c_9168])).
% 11.67/3.98  tff(c_12129, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11980, c_11976])).
% 11.67/3.98  tff(c_12133, plain, (~r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_30, c_12129])).
% 11.67/3.98  tff(c_17470, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17465, c_12133])).
% 11.67/3.98  tff(c_17479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_17470])).
% 11.67/3.98  tff(c_17481, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_206])).
% 11.67/3.98  tff(c_46, plain, (![C_25, A_23, B_24]: (v1_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.67/3.98  tff(c_17496, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_17481, c_46])).
% 11.67/3.98  tff(c_17599, plain, (![A_1073]: (k1_relat_1(A_1073)!='#skF_5' | A_1073='#skF_5' | ~v1_relat_1(A_1073))), inference(demodulation, [status(thm), theory('equality')], [c_9112, c_9112, c_36])).
% 11.67/3.98  tff(c_17617, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_17496, c_17599])).
% 11.67/3.98  tff(c_17655, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_17617])).
% 11.67/3.98  tff(c_18018, plain, (k2_relat_1('#skF_5')!='#skF_5' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_18009, c_17655])).
% 11.67/3.98  tff(c_18025, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_86, c_80, c_9123, c_18018])).
% 11.67/3.98  tff(c_18026, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_17617])).
% 11.67/3.98  tff(c_17575, plain, (![A_1072]: (k2_relat_1(A_1072)!='#skF_5' | A_1072='#skF_5' | ~v1_relat_1(A_1072))), inference(demodulation, [status(thm), theory('equality')], [c_9112, c_9112, c_34])).
% 11.67/3.98  tff(c_17593, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_17496, c_17575])).
% 11.67/3.98  tff(c_17621, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_17593])).
% 11.67/3.98  tff(c_18028, plain, (k2_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_18026, c_17621])).
% 11.67/3.98  tff(c_18036, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9123, c_18028])).
% 11.67/3.98  tff(c_18037, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_17593])).
% 11.67/3.98  tff(c_18041, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_18037, c_17481])).
% 11.67/3.98  tff(c_18470, plain, (![C_1145, A_1146, B_1147]: (v1_partfun1(C_1145, A_1146) | ~m1_subset_1(C_1145, k1_zfmisc_1(k2_zfmisc_1(A_1146, B_1147))) | ~v1_xboole_0(A_1146))), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.67/3.98  tff(c_18487, plain, (v1_partfun1('#skF_5', '#skF_4') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_18041, c_18470])).
% 11.67/3.98  tff(c_18493, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_18487])).
% 11.67/3.98  tff(c_18669, plain, (![A_1173, B_1174, C_1175]: (k2_relset_1(A_1173, B_1174, C_1175)=k2_relat_1(C_1175) | ~m1_subset_1(C_1175, k1_zfmisc_1(k2_zfmisc_1(A_1173, B_1174))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.67/3.98  tff(c_18688, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_18669])).
% 11.67/3.98  tff(c_18694, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_9123, c_18688])).
% 11.67/3.98  tff(c_18730, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18694, c_9118])).
% 11.67/3.98  tff(c_18740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18493, c_18730])).
% 11.67/3.98  tff(c_18742, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_18487])).
% 11.67/3.98  tff(c_17525, plain, (![A_1064, B_1065]: (r2_hidden('#skF_2'(A_1064, B_1065), A_1064) | r1_tarski(A_1064, B_1065))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.67/3.98  tff(c_17535, plain, (![A_1064, B_1065]: (~v1_xboole_0(A_1064) | r1_tarski(A_1064, B_1065))), inference(resolution, [status(thm)], [c_17525, c_2])).
% 11.67/3.98  tff(c_18111, plain, (![B_1115, A_1116]: (B_1115=A_1116 | ~r1_tarski(B_1115, A_1116) | ~r1_tarski(A_1116, B_1115))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.67/3.98  tff(c_18127, plain, (![B_1117, A_1118]: (B_1117=A_1118 | ~r1_tarski(B_1117, A_1118) | ~v1_xboole_0(A_1118))), inference(resolution, [status(thm)], [c_17535, c_18111])).
% 11.67/3.98  tff(c_18145, plain, (![B_1119, A_1120]: (B_1119=A_1120 | ~v1_xboole_0(B_1119) | ~v1_xboole_0(A_1120))), inference(resolution, [status(thm)], [c_17535, c_18127])).
% 11.67/3.98  tff(c_18150, plain, (![A_1120]: (A_1120='#skF_5' | ~v1_xboole_0(A_1120))), inference(resolution, [status(thm)], [c_9118, c_18145])).
% 11.67/3.98  tff(c_18764, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_18742, c_18150])).
% 11.67/3.98  tff(c_18788, plain, (![B_13]: (k2_zfmisc_1('#skF_4', B_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18764, c_18764, c_9117])).
% 11.67/3.98  tff(c_17497, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_17481, c_28])).
% 11.67/3.98  tff(c_18039, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18037, c_17497])).
% 11.67/3.98  tff(c_18120, plain, (k2_zfmisc_1('#skF_4', '#skF_3')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_18039, c_18111])).
% 11.67/3.98  tff(c_18285, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_18120])).
% 11.67/3.98  tff(c_18298, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_17535, c_18285])).
% 11.67/3.98  tff(c_18922, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18788, c_18298])).
% 11.67/3.98  tff(c_18925, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18742, c_18922])).
% 11.67/3.98  tff(c_18926, plain, (k2_zfmisc_1('#skF_4', '#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_18120])).
% 11.67/3.98  tff(c_17557, plain, (![B_13, A_12]: (B_13='#skF_5' | A_12='#skF_5' | k2_zfmisc_1(A_12, B_13)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9112, c_9112, c_9112, c_20])).
% 11.67/3.98  tff(c_18953, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_18926, c_17557])).
% 11.67/3.98  tff(c_18956, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_18953])).
% 11.67/3.98  tff(c_18977, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18956, c_9118])).
% 11.67/3.98  tff(c_18974, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18956, c_18956, c_9116])).
% 11.67/3.98  tff(c_18122, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_133, c_18111])).
% 11.67/3.98  tff(c_18232, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_18122])).
% 11.67/3.98  tff(c_18263, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_17535, c_18232])).
% 11.67/3.98  tff(c_19052, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18974, c_18263])).
% 11.67/3.98  tff(c_19055, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18977, c_19052])).
% 11.67/3.98  tff(c_19056, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_18953])).
% 11.67/3.98  tff(c_19077, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19056, c_9118])).
% 11.67/3.98  tff(c_19075, plain, (![B_13]: (k2_zfmisc_1('#skF_3', B_13)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19056, c_19056, c_9117])).
% 11.67/3.98  tff(c_19175, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19075, c_18263])).
% 11.67/3.98  tff(c_19178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19077, c_19175])).
% 11.67/3.98  tff(c_19179, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_18122])).
% 11.67/3.98  tff(c_19196, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_19179, c_17557])).
% 11.67/3.98  tff(c_19215, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_19196])).
% 11.67/3.98  tff(c_19182, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_19179, c_82])).
% 11.67/3.98  tff(c_19216, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_19215, c_19215, c_19182])).
% 11.67/3.98  tff(c_19234, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_19215, c_9112])).
% 11.67/3.98  tff(c_19344, plain, (![A_39]: (v1_funct_2('#skF_3', A_39, '#skF_3') | A_39='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_19234, c_19234, c_19234, c_19234, c_19234, c_90])).
% 11.67/3.98  tff(c_19345, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_19344])).
% 11.67/3.98  tff(c_19358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19216, c_19345])).
% 11.67/3.98  tff(c_19464, plain, (![A_1195]: (v1_funct_2('#skF_3', A_1195, '#skF_3') | A_1195='#skF_3')), inference(splitRight, [status(thm)], [c_19344])).
% 11.67/3.98  tff(c_17480, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_206])).
% 11.67/3.98  tff(c_18042, plain, (~v1_funct_2('#skF_5', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18037, c_17480])).
% 11.67/3.98  tff(c_19223, plain, (~v1_funct_2('#skF_3', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19215, c_18042])).
% 11.67/3.98  tff(c_19468, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_19464, c_19223])).
% 11.67/3.98  tff(c_19237, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19215, c_84])).
% 11.67/3.98  tff(c_19483, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19468, c_19468, c_19237])).
% 11.67/3.98  tff(c_19476, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19468, c_19468, c_19223])).
% 11.67/3.98  tff(c_19664, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19483, c_19476])).
% 11.67/3.98  tff(c_19665, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_19196])).
% 11.67/3.98  tff(c_19686, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19665, c_221])).
% 11.67/3.98  tff(c_19690, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19665, c_86])).
% 11.67/3.98  tff(c_19689, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19665, c_80])).
% 11.67/3.98  tff(c_19683, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19665, c_19665, c_9123])).
% 11.67/3.98  tff(c_19675, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19665, c_19665, c_18037])).
% 11.67/3.98  tff(c_19839, plain, (![A_1207]: (k2_relat_1(k2_funct_1(A_1207))=k1_relat_1(A_1207) | ~v2_funct_1(A_1207) | ~v1_funct_1(A_1207) | ~v1_relat_1(A_1207))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.67/3.98  tff(c_19857, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_19675, c_19839])).
% 11.67/3.98  tff(c_19861, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19686, c_19690, c_19689, c_19683, c_19857])).
% 11.67/3.98  tff(c_19667, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_19665, c_19665, c_19182])).
% 11.67/3.98  tff(c_19682, plain, (![B_13]: (k2_zfmisc_1('#skF_4', B_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19665, c_19665, c_9117])).
% 11.67/3.98  tff(c_20035, plain, (![A_1220, B_1221, C_1222]: (k1_relset_1(A_1220, B_1221, C_1222)=k1_relat_1(C_1222) | ~m1_subset_1(C_1222, k1_zfmisc_1(k2_zfmisc_1(A_1220, B_1221))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.67/3.98  tff(c_20236, plain, (![B_1254, C_1255]: (k1_relset_1('#skF_4', B_1254, C_1255)=k1_relat_1(C_1255) | ~m1_subset_1(C_1255, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_19682, c_20035])).
% 11.67/3.98  tff(c_20238, plain, (![B_1254]: (k1_relset_1('#skF_4', B_1254, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_19667, c_20236])).
% 11.67/3.98  tff(c_20243, plain, (![B_1254]: (k1_relset_1('#skF_4', B_1254, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19861, c_20238])).
% 11.67/3.98  tff(c_19685, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19665, c_9112])).
% 11.67/3.98  tff(c_20315, plain, (![C_1269, B_1270]: (v1_funct_2(C_1269, '#skF_4', B_1270) | k1_relset_1('#skF_4', B_1270, C_1269)!='#skF_4' | ~m1_subset_1(C_1269, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_19685, c_19685, c_19685, c_19685, c_88])).
% 11.67/3.98  tff(c_20317, plain, (![B_1270]: (v1_funct_2('#skF_4', '#skF_4', B_1270) | k1_relset_1('#skF_4', B_1270, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_19667, c_20315])).
% 11.67/3.98  tff(c_20323, plain, (![B_1270]: (v1_funct_2('#skF_4', '#skF_4', B_1270))), inference(demodulation, [status(thm), theory('equality')], [c_20243, c_20317])).
% 11.67/3.98  tff(c_19674, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19665, c_18042])).
% 11.67/3.98  tff(c_20328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20323, c_19674])).
% 11.67/3.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.67/3.98  
% 11.67/3.98  Inference rules
% 11.67/3.98  ----------------------
% 11.67/3.98  #Ref     : 0
% 11.67/3.98  #Sup     : 5239
% 11.67/3.98  #Fact    : 0
% 11.67/3.98  #Define  : 0
% 11.67/3.98  #Split   : 70
% 11.67/3.98  #Chain   : 0
% 11.67/3.98  #Close   : 0
% 11.67/3.98  
% 11.67/3.98  Ordering : KBO
% 11.67/3.98  
% 11.67/3.98  Simplification rules
% 11.67/3.98  ----------------------
% 11.67/3.98  #Subsume      : 1647
% 11.67/3.98  #Demod        : 3286
% 11.67/3.98  #Tautology    : 1546
% 11.67/3.98  #SimpNegUnit  : 35
% 11.67/3.98  #BackRed      : 413
% 11.67/3.98  
% 11.67/3.98  #Partial instantiations: 0
% 11.67/3.98  #Strategies tried      : 1
% 11.67/3.98  
% 11.67/3.98  Timing (in seconds)
% 11.67/3.98  ----------------------
% 11.67/3.98  Preprocessing        : 0.36
% 11.67/3.98  Parsing              : 0.18
% 11.67/3.98  CNF conversion       : 0.03
% 11.67/3.98  Main loop            : 2.79
% 11.67/3.98  Inferencing          : 0.83
% 11.67/3.99  Reduction            : 0.89
% 11.67/3.99  Demodulation         : 0.61
% 11.67/3.99  BG Simplification    : 0.09
% 11.67/3.99  Subsumption          : 0.76
% 11.67/3.99  Abstraction          : 0.11
% 11.67/3.99  MUC search           : 0.00
% 11.67/3.99  Cooper               : 0.00
% 11.67/3.99  Total                : 3.27
% 11.67/3.99  Index Insertion      : 0.00
% 11.67/3.99  Index Deletion       : 0.00
% 11.67/3.99  Index Matching       : 0.00
% 11.67/3.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
