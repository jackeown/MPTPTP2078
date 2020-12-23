%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:13 EST 2020

% Result     : Theorem 5.17s
% Output     : CNFRefutation 5.17s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 781 expanded)
%              Number of leaves         :   37 ( 246 expanded)
%              Depth                    :   11
%              Number of atoms          :  260 (2457 expanded)
%              Number of equality atoms :   89 ( 974 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_155,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_123,axiom,(
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

tff(f_135,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ~ ( ~ ( A = k1_xboole_0
            & B != k1_xboole_0 )
        & ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ~ ( B = k1_relat_1(C)
                & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_70,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_26,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_82,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1544,plain,(
    ! [B_176,A_177] :
      ( v1_relat_1(B_176)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(A_177))
      | ~ v1_relat_1(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1547,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_82,c_1544])).

tff(c_1553,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1547])).

tff(c_1587,plain,(
    ! [C_183,B_184,A_185] :
      ( v5_relat_1(C_183,B_184)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_185,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1601,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_1587])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v5_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_80,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1617,plain,(
    ! [A_189,C_190,B_191] :
      ( r1_tarski(A_189,C_190)
      | ~ r1_tarski(B_191,C_190)
      | ~ r1_tarski(A_189,B_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1645,plain,(
    ! [A_194] :
      ( r1_tarski(A_194,'#skF_4')
      | ~ r1_tarski(A_194,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_1617])).

tff(c_1658,plain,(
    ! [B_16] :
      ( r1_tarski(k2_relat_1(B_16),'#skF_4')
      | ~ v5_relat_1(B_16,'#skF_3')
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_24,c_1645])).

tff(c_86,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_78,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_139,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_84,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1887,plain,(
    ! [A_231,B_232,C_233] :
      ( k1_relset_1(A_231,B_232,C_233) = k1_relat_1(C_233)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1901,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_1887])).

tff(c_2759,plain,(
    ! [B_295,A_296,C_297] :
      ( k1_xboole_0 = B_295
      | k1_relset_1(A_296,B_295,C_297) = A_296
      | ~ v1_funct_2(C_297,A_296,B_295)
      | ~ m1_subset_1(C_297,k1_zfmisc_1(k2_zfmisc_1(A_296,B_295))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2765,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_2759])).

tff(c_2779,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1901,c_2765])).

tff(c_2780,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_2779])).

tff(c_70,plain,(
    ! [B_33,A_32] :
      ( m1_subset_1(B_33,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_33),A_32)))
      | ~ r1_tarski(k2_relat_1(B_33),A_32)
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2791,plain,(
    ! [A_32] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_32)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_32)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2780,c_70])).

tff(c_2903,plain,(
    ! [A_305] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_305)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_305) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1553,c_86,c_2791])).

tff(c_76,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_88,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_76])).

tff(c_240,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_257,plain,(
    ! [B_59,A_60] :
      ( v1_relat_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_260,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_82,c_257])).

tff(c_266,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_260])).

tff(c_277,plain,(
    ! [C_61,B_62,A_63] :
      ( v5_relat_1(C_61,B_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_291,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_277])).

tff(c_339,plain,(
    ! [A_75,C_76,B_77] :
      ( r1_tarski(A_75,C_76)
      | ~ r1_tarski(B_77,C_76)
      | ~ r1_tarski(A_75,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_367,plain,(
    ! [A_80] :
      ( r1_tarski(A_80,'#skF_4')
      | ~ r1_tarski(A_80,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_339])).

tff(c_380,plain,(
    ! [B_16] :
      ( r1_tarski(k2_relat_1(B_16),'#skF_4')
      | ~ v5_relat_1(B_16,'#skF_3')
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_24,c_367])).

tff(c_747,plain,(
    ! [A_118,B_119,C_120] :
      ( k1_relset_1(A_118,B_119,C_120) = k1_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_761,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_747])).

tff(c_1402,plain,(
    ! [B_165,A_166,C_167] :
      ( k1_xboole_0 = B_165
      | k1_relset_1(A_166,B_165,C_167) = A_166
      | ~ v1_funct_2(C_167,A_166,B_165)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_166,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1408,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_1402])).

tff(c_1422,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_761,c_1408])).

tff(c_1423,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_1422])).

tff(c_72,plain,(
    ! [B_33,A_32] :
      ( v1_funct_2(B_33,k1_relat_1(B_33),A_32)
      | ~ r1_tarski(k2_relat_1(B_33),A_32)
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1437,plain,(
    ! [A_32] :
      ( v1_funct_2('#skF_5','#skF_2',A_32)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_32)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1423,c_72])).

tff(c_1505,plain,(
    ! [A_171] :
      ( v1_funct_2('#skF_5','#skF_2',A_171)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_86,c_1437])).

tff(c_1513,plain,
    ( v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_380,c_1505])).

tff(c_1523,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_291,c_1513])).

tff(c_1525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_1523])).

tff(c_1526,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_2942,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2903,c_1526])).

tff(c_2948,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1658,c_2942])).

tff(c_2958,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1553,c_1601,c_2948])).

tff(c_2960,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_2959,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_2974,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2960,c_2959])).

tff(c_105,plain,(
    ! [B_38] : k2_zfmisc_1(k1_xboole_0,B_38) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_109,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_26])).

tff(c_2963,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2959,c_109])).

tff(c_2994,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2974,c_2963])).

tff(c_40,plain,(
    ! [A_20] : k1_relat_1('#skF_1'(A_20,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3046,plain,(
    ! [A_20] : k1_relat_1('#skF_1'(A_20,'#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2960,c_2960,c_40])).

tff(c_48,plain,(
    ! [A_20] : v1_relat_1('#skF_1'(A_20,k1_xboole_0)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2965,plain,(
    ! [A_20] : v1_relat_1('#skF_1'(A_20,'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2959,c_48])).

tff(c_3044,plain,(
    ! [A_20] : v1_relat_1('#skF_1'(A_20,'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2974,c_2965])).

tff(c_34,plain,(
    ! [A_19] :
      ( k1_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3085,plain,(
    ! [A_321] :
      ( k1_relat_1(A_321) != '#skF_3'
      | A_321 = '#skF_3'
      | ~ v1_relat_1(A_321) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2960,c_2960,c_34])).

tff(c_3091,plain,(
    ! [A_20] :
      ( k1_relat_1('#skF_1'(A_20,'#skF_3')) != '#skF_3'
      | '#skF_1'(A_20,'#skF_3') = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_3044,c_3085])).

tff(c_3101,plain,(
    ! [A_20] : '#skF_1'(A_20,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3046,c_3091])).

tff(c_44,plain,(
    ! [A_20] : v1_funct_1('#skF_1'(A_20,k1_xboole_0)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2961,plain,(
    ! [A_20] : v1_funct_1('#skF_1'(A_20,'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2959,c_44])).

tff(c_3040,plain,(
    ! [A_20] : v1_funct_1('#skF_1'(A_20,'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2974,c_2961])).

tff(c_3110,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3101,c_3040])).

tff(c_6,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2968,plain,(
    ! [A_4] : r1_tarski('#skF_2',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2959,c_6])).

tff(c_3002,plain,(
    ! [A_4] : r1_tarski('#skF_3',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2974,c_2968])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2966,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2959,c_2959,c_28])).

tff(c_3005,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2974,c_2974,c_2966])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2967,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2959,c_2959,c_30])).

tff(c_2995,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2974,c_2974,c_2967])).

tff(c_3926,plain,(
    ! [B_457,A_458] :
      ( v1_funct_2(B_457,k1_relat_1(B_457),A_458)
      | ~ r1_tarski(k2_relat_1(B_457),A_458)
      | ~ v1_funct_1(B_457)
      | ~ v1_relat_1(B_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3935,plain,(
    ! [A_458] :
      ( v1_funct_2('#skF_3','#skF_3',A_458)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_458)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2995,c_3926])).

tff(c_3938,plain,(
    ! [A_458] : v1_funct_2('#skF_3','#skF_3',A_458) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2994,c_3110,c_3002,c_3005,c_3935])).

tff(c_10,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2962,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2959,c_2959,c_10])).

tff(c_3010,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2974,c_2974,c_2962])).

tff(c_2984,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2974,c_82])).

tff(c_3058,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3010,c_2984])).

tff(c_3150,plain,(
    ! [B_324,A_325] :
      ( v1_relat_1(B_324)
      | ~ m1_subset_1(B_324,k1_zfmisc_1(A_325))
      | ~ v1_relat_1(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3153,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3058,c_3150])).

tff(c_3159,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2994,c_3153])).

tff(c_3084,plain,(
    ! [A_19] :
      ( k1_relat_1(A_19) != '#skF_3'
      | A_19 = '#skF_3'
      | ~ v1_relat_1(A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2960,c_2960,c_34])).

tff(c_3171,plain,
    ( k1_relat_1('#skF_5') != '#skF_3'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3159,c_3084])).

tff(c_3173,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3171])).

tff(c_3357,plain,(
    ! [A_368,B_369,C_370] :
      ( k1_relset_1(A_368,B_369,C_370) = k1_relat_1(C_370)
      | ~ m1_subset_1(C_370,k1_zfmisc_1(k2_zfmisc_1(A_368,B_369))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3377,plain,(
    ! [A_373,C_374] :
      ( k1_relset_1(A_373,'#skF_3',C_374) = k1_relat_1(C_374)
      | ~ m1_subset_1(C_374,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3010,c_3357])).

tff(c_3383,plain,(
    ! [A_373] : k1_relset_1(A_373,'#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3058,c_3377])).

tff(c_2985,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2974,c_84])).

tff(c_12,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_66,plain,(
    ! [B_30,C_31] :
      ( k1_relset_1(k1_xboole_0,B_30,C_31) = k1_xboole_0
      | ~ v1_funct_2(C_31,k1_xboole_0,B_30)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_91,plain,(
    ! [B_30,C_31] :
      ( k1_relset_1(k1_xboole_0,B_30,C_31) = k1_xboole_0
      | ~ v1_funct_2(C_31,k1_xboole_0,B_30)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_66])).

tff(c_3635,plain,(
    ! [B_400,C_401] :
      ( k1_relset_1('#skF_3',B_400,C_401) = '#skF_3'
      | ~ v1_funct_2(C_401,'#skF_3',B_400)
      | ~ m1_subset_1(C_401,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2960,c_2960,c_2960,c_2960,c_91])).

tff(c_3642,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2985,c_3635])).

tff(c_3652,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3058,c_3383,c_3642])).

tff(c_3654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3173,c_3652])).

tff(c_3655,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3171])).

tff(c_32,plain,(
    ! [A_19] :
      ( k2_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3132,plain,(
    ! [A_19] :
      ( k2_relat_1(A_19) != '#skF_3'
      | A_19 = '#skF_3'
      | ~ v1_relat_1(A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2960,c_2960,c_32])).

tff(c_3170,plain,
    ( k2_relat_1('#skF_5') != '#skF_3'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3159,c_3132])).

tff(c_3172,plain,(
    k2_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3170])).

tff(c_3657,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3655,c_3172])).

tff(c_3665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3005,c_3657])).

tff(c_3666,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3170])).

tff(c_2964,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_2',B_6) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2959,c_2959,c_12])).

tff(c_3021,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_3',B_6) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2974,c_2974,c_2964])).

tff(c_3163,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2974,c_3058,c_3021,c_2974,c_88])).

tff(c_3669,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3666,c_3163])).

tff(c_3942,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3938,c_3669])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.17/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.17/2.01  
% 5.17/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.17/2.01  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.17/2.01  
% 5.17/2.01  %Foreground sorts:
% 5.17/2.01  
% 5.17/2.01  
% 5.17/2.01  %Background operators:
% 5.17/2.01  
% 5.17/2.01  
% 5.17/2.01  %Foreground operators:
% 5.17/2.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.17/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.17/2.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.17/2.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.17/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.17/2.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.17/2.01  tff('#skF_5', type, '#skF_5': $i).
% 5.17/2.01  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.17/2.01  tff('#skF_2', type, '#skF_2': $i).
% 5.17/2.01  tff('#skF_3', type, '#skF_3': $i).
% 5.17/2.01  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.17/2.01  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.17/2.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.17/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.17/2.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.17/2.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.17/2.01  tff('#skF_4', type, '#skF_4': $i).
% 5.17/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.17/2.01  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.17/2.01  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.17/2.01  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.17/2.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.17/2.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.17/2.01  
% 5.17/2.03  tff(f_67, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.17/2.03  tff(f_155, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 5.17/2.03  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.17/2.03  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.17/2.03  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 5.17/2.03  tff(f_32, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.17/2.03  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.17/2.03  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.17/2.03  tff(f_135, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 5.17/2.03  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.17/2.03  tff(f_95, axiom, (![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 5.17/2.03  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 5.17/2.03  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.17/2.03  tff(f_70, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.17/2.03  tff(c_26, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.17/2.03  tff(c_82, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.17/2.03  tff(c_1544, plain, (![B_176, A_177]: (v1_relat_1(B_176) | ~m1_subset_1(B_176, k1_zfmisc_1(A_177)) | ~v1_relat_1(A_177))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.17/2.03  tff(c_1547, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_82, c_1544])).
% 5.17/2.03  tff(c_1553, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1547])).
% 5.17/2.03  tff(c_1587, plain, (![C_183, B_184, A_185]: (v5_relat_1(C_183, B_184) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_185, B_184))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.17/2.03  tff(c_1601, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_82, c_1587])).
% 5.17/2.03  tff(c_24, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(B_16), A_15) | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.17/2.03  tff(c_80, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.17/2.03  tff(c_1617, plain, (![A_189, C_190, B_191]: (r1_tarski(A_189, C_190) | ~r1_tarski(B_191, C_190) | ~r1_tarski(A_189, B_191))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.17/2.03  tff(c_1645, plain, (![A_194]: (r1_tarski(A_194, '#skF_4') | ~r1_tarski(A_194, '#skF_3'))), inference(resolution, [status(thm)], [c_80, c_1617])).
% 5.17/2.03  tff(c_1658, plain, (![B_16]: (r1_tarski(k2_relat_1(B_16), '#skF_4') | ~v5_relat_1(B_16, '#skF_3') | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_24, c_1645])).
% 5.17/2.03  tff(c_86, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.17/2.03  tff(c_78, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.17/2.03  tff(c_139, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_78])).
% 5.17/2.03  tff(c_84, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.17/2.03  tff(c_1887, plain, (![A_231, B_232, C_233]: (k1_relset_1(A_231, B_232, C_233)=k1_relat_1(C_233) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.17/2.03  tff(c_1901, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_1887])).
% 5.17/2.03  tff(c_2759, plain, (![B_295, A_296, C_297]: (k1_xboole_0=B_295 | k1_relset_1(A_296, B_295, C_297)=A_296 | ~v1_funct_2(C_297, A_296, B_295) | ~m1_subset_1(C_297, k1_zfmisc_1(k2_zfmisc_1(A_296, B_295))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.17/2.03  tff(c_2765, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_82, c_2759])).
% 5.17/2.03  tff(c_2779, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1901, c_2765])).
% 5.17/2.03  tff(c_2780, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_139, c_2779])).
% 5.17/2.03  tff(c_70, plain, (![B_33, A_32]: (m1_subset_1(B_33, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_33), A_32))) | ~r1_tarski(k2_relat_1(B_33), A_32) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.17/2.03  tff(c_2791, plain, (![A_32]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_32))) | ~r1_tarski(k2_relat_1('#skF_5'), A_32) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2780, c_70])).
% 5.17/2.03  tff(c_2903, plain, (![A_305]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_305))) | ~r1_tarski(k2_relat_1('#skF_5'), A_305))), inference(demodulation, [status(thm), theory('equality')], [c_1553, c_86, c_2791])).
% 5.17/2.03  tff(c_76, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.17/2.03  tff(c_88, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_76])).
% 5.17/2.03  tff(c_240, plain, (~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_88])).
% 5.17/2.03  tff(c_257, plain, (![B_59, A_60]: (v1_relat_1(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.17/2.03  tff(c_260, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_82, c_257])).
% 5.17/2.03  tff(c_266, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_260])).
% 5.17/2.03  tff(c_277, plain, (![C_61, B_62, A_63]: (v5_relat_1(C_61, B_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.17/2.03  tff(c_291, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_82, c_277])).
% 5.17/2.03  tff(c_339, plain, (![A_75, C_76, B_77]: (r1_tarski(A_75, C_76) | ~r1_tarski(B_77, C_76) | ~r1_tarski(A_75, B_77))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.17/2.03  tff(c_367, plain, (![A_80]: (r1_tarski(A_80, '#skF_4') | ~r1_tarski(A_80, '#skF_3'))), inference(resolution, [status(thm)], [c_80, c_339])).
% 5.17/2.03  tff(c_380, plain, (![B_16]: (r1_tarski(k2_relat_1(B_16), '#skF_4') | ~v5_relat_1(B_16, '#skF_3') | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_24, c_367])).
% 5.17/2.03  tff(c_747, plain, (![A_118, B_119, C_120]: (k1_relset_1(A_118, B_119, C_120)=k1_relat_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.17/2.03  tff(c_761, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_747])).
% 5.17/2.03  tff(c_1402, plain, (![B_165, A_166, C_167]: (k1_xboole_0=B_165 | k1_relset_1(A_166, B_165, C_167)=A_166 | ~v1_funct_2(C_167, A_166, B_165) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_166, B_165))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.17/2.03  tff(c_1408, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_82, c_1402])).
% 5.17/2.03  tff(c_1422, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_761, c_1408])).
% 5.17/2.03  tff(c_1423, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_139, c_1422])).
% 5.17/2.03  tff(c_72, plain, (![B_33, A_32]: (v1_funct_2(B_33, k1_relat_1(B_33), A_32) | ~r1_tarski(k2_relat_1(B_33), A_32) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.17/2.03  tff(c_1437, plain, (![A_32]: (v1_funct_2('#skF_5', '#skF_2', A_32) | ~r1_tarski(k2_relat_1('#skF_5'), A_32) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1423, c_72])).
% 5.17/2.03  tff(c_1505, plain, (![A_171]: (v1_funct_2('#skF_5', '#skF_2', A_171) | ~r1_tarski(k2_relat_1('#skF_5'), A_171))), inference(demodulation, [status(thm), theory('equality')], [c_266, c_86, c_1437])).
% 5.17/2.03  tff(c_1513, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_380, c_1505])).
% 5.17/2.03  tff(c_1523, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_266, c_291, c_1513])).
% 5.17/2.03  tff(c_1525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_1523])).
% 5.17/2.03  tff(c_1526, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_88])).
% 5.17/2.03  tff(c_2942, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_2903, c_1526])).
% 5.17/2.03  tff(c_2948, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1658, c_2942])).
% 5.17/2.03  tff(c_2958, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1553, c_1601, c_2948])).
% 5.17/2.03  tff(c_2960, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_78])).
% 5.17/2.03  tff(c_2959, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_78])).
% 5.17/2.03  tff(c_2974, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2960, c_2959])).
% 5.17/2.03  tff(c_105, plain, (![B_38]: (k2_zfmisc_1(k1_xboole_0, B_38)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.17/2.03  tff(c_109, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_105, c_26])).
% 5.17/2.03  tff(c_2963, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2959, c_109])).
% 5.17/2.03  tff(c_2994, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2974, c_2963])).
% 5.17/2.03  tff(c_40, plain, (![A_20]: (k1_relat_1('#skF_1'(A_20, k1_xboole_0))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.17/2.03  tff(c_3046, plain, (![A_20]: (k1_relat_1('#skF_1'(A_20, '#skF_3'))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2960, c_2960, c_40])).
% 5.17/2.03  tff(c_48, plain, (![A_20]: (v1_relat_1('#skF_1'(A_20, k1_xboole_0)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.17/2.03  tff(c_2965, plain, (![A_20]: (v1_relat_1('#skF_1'(A_20, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2959, c_48])).
% 5.17/2.03  tff(c_3044, plain, (![A_20]: (v1_relat_1('#skF_1'(A_20, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2974, c_2965])).
% 5.17/2.03  tff(c_34, plain, (![A_19]: (k1_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.17/2.03  tff(c_3085, plain, (![A_321]: (k1_relat_1(A_321)!='#skF_3' | A_321='#skF_3' | ~v1_relat_1(A_321))), inference(demodulation, [status(thm), theory('equality')], [c_2960, c_2960, c_34])).
% 5.17/2.03  tff(c_3091, plain, (![A_20]: (k1_relat_1('#skF_1'(A_20, '#skF_3'))!='#skF_3' | '#skF_1'(A_20, '#skF_3')='#skF_3')), inference(resolution, [status(thm)], [c_3044, c_3085])).
% 5.17/2.03  tff(c_3101, plain, (![A_20]: ('#skF_1'(A_20, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3046, c_3091])).
% 5.17/2.03  tff(c_44, plain, (![A_20]: (v1_funct_1('#skF_1'(A_20, k1_xboole_0)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.17/2.03  tff(c_2961, plain, (![A_20]: (v1_funct_1('#skF_1'(A_20, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2959, c_44])).
% 5.17/2.03  tff(c_3040, plain, (![A_20]: (v1_funct_1('#skF_1'(A_20, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2974, c_2961])).
% 5.17/2.03  tff(c_3110, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3101, c_3040])).
% 5.17/2.03  tff(c_6, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.17/2.03  tff(c_2968, plain, (![A_4]: (r1_tarski('#skF_2', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_2959, c_6])).
% 5.17/2.03  tff(c_3002, plain, (![A_4]: (r1_tarski('#skF_3', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_2974, c_2968])).
% 5.17/2.03  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.17/2.03  tff(c_2966, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2959, c_2959, c_28])).
% 5.17/2.03  tff(c_3005, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2974, c_2974, c_2966])).
% 5.17/2.03  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.17/2.03  tff(c_2967, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2959, c_2959, c_30])).
% 5.17/2.03  tff(c_2995, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2974, c_2974, c_2967])).
% 5.17/2.03  tff(c_3926, plain, (![B_457, A_458]: (v1_funct_2(B_457, k1_relat_1(B_457), A_458) | ~r1_tarski(k2_relat_1(B_457), A_458) | ~v1_funct_1(B_457) | ~v1_relat_1(B_457))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.17/2.03  tff(c_3935, plain, (![A_458]: (v1_funct_2('#skF_3', '#skF_3', A_458) | ~r1_tarski(k2_relat_1('#skF_3'), A_458) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2995, c_3926])).
% 5.17/2.03  tff(c_3938, plain, (![A_458]: (v1_funct_2('#skF_3', '#skF_3', A_458))), inference(demodulation, [status(thm), theory('equality')], [c_2994, c_3110, c_3002, c_3005, c_3935])).
% 5.17/2.03  tff(c_10, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.17/2.03  tff(c_2962, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2959, c_2959, c_10])).
% 5.17/2.03  tff(c_3010, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2974, c_2974, c_2962])).
% 5.17/2.03  tff(c_2984, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2974, c_82])).
% 5.17/2.03  tff(c_3058, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3010, c_2984])).
% 5.17/2.03  tff(c_3150, plain, (![B_324, A_325]: (v1_relat_1(B_324) | ~m1_subset_1(B_324, k1_zfmisc_1(A_325)) | ~v1_relat_1(A_325))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.17/2.03  tff(c_3153, plain, (v1_relat_1('#skF_5') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3058, c_3150])).
% 5.17/2.03  tff(c_3159, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2994, c_3153])).
% 5.17/2.03  tff(c_3084, plain, (![A_19]: (k1_relat_1(A_19)!='#skF_3' | A_19='#skF_3' | ~v1_relat_1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_2960, c_2960, c_34])).
% 5.17/2.03  tff(c_3171, plain, (k1_relat_1('#skF_5')!='#skF_3' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_3159, c_3084])).
% 5.17/2.03  tff(c_3173, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(splitLeft, [status(thm)], [c_3171])).
% 5.17/2.03  tff(c_3357, plain, (![A_368, B_369, C_370]: (k1_relset_1(A_368, B_369, C_370)=k1_relat_1(C_370) | ~m1_subset_1(C_370, k1_zfmisc_1(k2_zfmisc_1(A_368, B_369))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.17/2.03  tff(c_3377, plain, (![A_373, C_374]: (k1_relset_1(A_373, '#skF_3', C_374)=k1_relat_1(C_374) | ~m1_subset_1(C_374, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3010, c_3357])).
% 5.17/2.03  tff(c_3383, plain, (![A_373]: (k1_relset_1(A_373, '#skF_3', '#skF_5')=k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_3058, c_3377])).
% 5.17/2.03  tff(c_2985, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2974, c_84])).
% 5.17/2.03  tff(c_12, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.17/2.03  tff(c_66, plain, (![B_30, C_31]: (k1_relset_1(k1_xboole_0, B_30, C_31)=k1_xboole_0 | ~v1_funct_2(C_31, k1_xboole_0, B_30) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_30))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.17/2.03  tff(c_91, plain, (![B_30, C_31]: (k1_relset_1(k1_xboole_0, B_30, C_31)=k1_xboole_0 | ~v1_funct_2(C_31, k1_xboole_0, B_30) | ~m1_subset_1(C_31, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_66])).
% 5.17/2.03  tff(c_3635, plain, (![B_400, C_401]: (k1_relset_1('#skF_3', B_400, C_401)='#skF_3' | ~v1_funct_2(C_401, '#skF_3', B_400) | ~m1_subset_1(C_401, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2960, c_2960, c_2960, c_2960, c_91])).
% 5.17/2.03  tff(c_3642, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_2985, c_3635])).
% 5.17/2.03  tff(c_3652, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3058, c_3383, c_3642])).
% 5.17/2.03  tff(c_3654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3173, c_3652])).
% 5.17/2.03  tff(c_3655, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_3171])).
% 5.17/2.03  tff(c_32, plain, (![A_19]: (k2_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.17/2.03  tff(c_3132, plain, (![A_19]: (k2_relat_1(A_19)!='#skF_3' | A_19='#skF_3' | ~v1_relat_1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_2960, c_2960, c_32])).
% 5.17/2.03  tff(c_3170, plain, (k2_relat_1('#skF_5')!='#skF_3' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_3159, c_3132])).
% 5.17/2.03  tff(c_3172, plain, (k2_relat_1('#skF_5')!='#skF_3'), inference(splitLeft, [status(thm)], [c_3170])).
% 5.17/2.03  tff(c_3657, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3655, c_3172])).
% 5.17/2.03  tff(c_3665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3005, c_3657])).
% 5.17/2.03  tff(c_3666, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_3170])).
% 5.17/2.03  tff(c_2964, plain, (![B_6]: (k2_zfmisc_1('#skF_2', B_6)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2959, c_2959, c_12])).
% 5.17/2.03  tff(c_3021, plain, (![B_6]: (k2_zfmisc_1('#skF_3', B_6)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2974, c_2974, c_2964])).
% 5.17/2.03  tff(c_3163, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2974, c_3058, c_3021, c_2974, c_88])).
% 5.17/2.03  tff(c_3669, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3666, c_3163])).
% 5.17/2.03  tff(c_3942, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3938, c_3669])).
% 5.17/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.17/2.03  
% 5.17/2.03  Inference rules
% 5.17/2.03  ----------------------
% 5.17/2.03  #Ref     : 0
% 5.17/2.03  #Sup     : 787
% 5.17/2.03  #Fact    : 0
% 5.17/2.03  #Define  : 0
% 5.17/2.03  #Split   : 11
% 5.17/2.03  #Chain   : 0
% 5.17/2.03  #Close   : 0
% 5.17/2.03  
% 5.17/2.03  Ordering : KBO
% 5.17/2.03  
% 5.17/2.03  Simplification rules
% 5.17/2.03  ----------------------
% 5.17/2.03  #Subsume      : 121
% 5.17/2.03  #Demod        : 743
% 5.17/2.03  #Tautology    : 428
% 5.17/2.03  #SimpNegUnit  : 70
% 5.17/2.03  #BackRed      : 39
% 5.17/2.03  
% 5.17/2.03  #Partial instantiations: 0
% 5.17/2.03  #Strategies tried      : 1
% 5.17/2.03  
% 5.17/2.03  Timing (in seconds)
% 5.17/2.03  ----------------------
% 5.17/2.03  Preprocessing        : 0.37
% 5.17/2.03  Parsing              : 0.20
% 5.17/2.03  CNF conversion       : 0.02
% 5.17/2.03  Main loop            : 0.83
% 5.17/2.03  Inferencing          : 0.28
% 5.17/2.03  Reduction            : 0.29
% 5.17/2.03  Demodulation         : 0.21
% 5.17/2.03  BG Simplification    : 0.03
% 5.17/2.04  Subsumption          : 0.16
% 5.17/2.04  Abstraction          : 0.04
% 5.17/2.04  MUC search           : 0.00
% 5.17/2.04  Cooper               : 0.00
% 5.17/2.04  Total                : 1.25
% 5.17/2.04  Index Insertion      : 0.00
% 5.17/2.04  Index Deletion       : 0.00
% 5.17/2.04  Index Matching       : 0.00
% 5.17/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
