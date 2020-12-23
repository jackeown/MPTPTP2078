%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:41 EST 2020

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :  191 (1431 expanded)
%              Number of leaves         :   36 ( 470 expanded)
%              Depth                    :   13
%              Number of atoms          :  340 (3742 expanded)
%              Number of equality atoms :  129 (1254 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
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

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_114,axiom,(
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

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_45,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1673,plain,(
    ! [C_239,A_240,B_241] :
      ( v1_relat_1(C_239)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1685,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1673])).

tff(c_70,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_64,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_62,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1899,plain,(
    ! [A_276,B_277,C_278] :
      ( k2_relset_1(A_276,B_277,C_278) = k2_relat_1(C_278)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1909,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1899])).

tff(c_1917,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1909])).

tff(c_34,plain,(
    ! [A_16] :
      ( k1_relat_1(k2_funct_1(A_16)) = k2_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_140,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_148,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_140])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_173,plain,(
    ! [A_50,B_51] :
      ( ~ r2_hidden('#skF_1'(A_50,B_51),B_51)
      | r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_178,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_173])).

tff(c_289,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_296,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_289])).

tff(c_303,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_296])).

tff(c_18,plain,(
    ! [A_11] :
      ( k2_relat_1(A_11) != k1_xboole_0
      | k1_xboole_0 = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_157,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_148,c_18])).

tff(c_180,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_306,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_180])).

tff(c_68,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_318,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_331,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_318])).

tff(c_476,plain,(
    ! [B_110,A_111,C_112] :
      ( k1_xboole_0 = B_110
      | k1_relset_1(A_111,B_110,C_112) = A_111
      | ~ v1_funct_2(C_112,A_111,B_110)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_111,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_482,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_476])).

tff(c_490,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_331,c_482])).

tff(c_491,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_490])).

tff(c_32,plain,(
    ! [A_16] :
      ( k2_relat_1(k2_funct_1(A_16)) = k1_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,(
    ! [A_15] :
      ( v1_relat_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    ! [A_15] :
      ( v1_funct_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_60,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_110,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_113,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_110])).

tff(c_116,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_113])).

tff(c_124,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_127,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_124])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_127])).

tff(c_137,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_345,plain,(
    ! [B_87,A_88] :
      ( v1_funct_2(B_87,k1_relat_1(B_87),A_88)
      | ~ r1_tarski(k2_relat_1(B_87),A_88)
      | ~ v1_funct_1(B_87)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_803,plain,(
    ! [A_137,A_138] :
      ( v1_funct_2(k2_funct_1(A_137),k2_relat_1(A_137),A_138)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_137)),A_138)
      | ~ v1_funct_1(k2_funct_1(A_137))
      | ~ v1_relat_1(k2_funct_1(A_137))
      | ~ v2_funct_1(A_137)
      | ~ v1_funct_1(A_137)
      | ~ v1_relat_1(A_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_345])).

tff(c_806,plain,(
    ! [A_138] :
      ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',A_138)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_5')),A_138)
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v1_relat_1(k2_funct_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_803])).

tff(c_814,plain,(
    ! [A_138] :
      ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',A_138)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_5')),A_138)
      | ~ v1_relat_1(k2_funct_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_70,c_64,c_137,c_806])).

tff(c_817,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_814])).

tff(c_866,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_817])).

tff(c_870,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_70,c_866])).

tff(c_872,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_814])).

tff(c_411,plain,(
    ! [B_103,A_104] :
      ( m1_subset_1(B_103,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_103),A_104)))
      | ~ r1_tarski(k2_relat_1(B_103),A_104)
      | ~ v1_funct_1(B_103)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_909,plain,(
    ! [A_142,A_143] :
      ( m1_subset_1(k2_funct_1(A_142),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_142),A_143)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_142)),A_143)
      | ~ v1_funct_1(k2_funct_1(A_142))
      | ~ v1_relat_1(k2_funct_1(A_142))
      | ~ v2_funct_1(A_142)
      | ~ v1_funct_1(A_142)
      | ~ v1_relat_1(A_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_411])).

tff(c_936,plain,(
    ! [A_143] :
      ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_143)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_5')),A_143)
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v1_relat_1(k2_funct_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_909])).

tff(c_956,plain,(
    ! [A_145] :
      ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_145)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_5')),A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_70,c_64,c_872,c_137,c_936])).

tff(c_136,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_139,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_996,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_5')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_956,c_139])).

tff(c_999,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_996])).

tff(c_1002,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_70,c_64,c_178,c_491,c_999])).

tff(c_1003,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1015,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1003,c_1003,c_16])).

tff(c_20,plain,(
    ! [A_11] :
      ( k1_relat_1(A_11) != k1_xboole_0
      | k1_xboole_0 = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_156,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_148,c_20])).

tff(c_172,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_1005,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1003,c_172])).

tff(c_1033,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1015,c_1005])).

tff(c_1034,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_14,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1050,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1034,c_1034,c_14])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1048,plain,(
    ! [A_7] : m1_subset_1('#skF_5',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1034,c_10])).

tff(c_1181,plain,(
    ! [A_176,B_177,C_178] :
      ( k2_relset_1(A_176,B_177,C_178) = k2_relat_1(C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1185,plain,(
    ! [A_176,B_177] : k2_relset_1(A_176,B_177,'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1048,c_1181])).

tff(c_1188,plain,(
    ! [A_179,B_180] : k2_relset_1(A_179,B_180,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_1185])).

tff(c_1192,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1188,c_62])).

tff(c_1206,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1192,c_1048])).

tff(c_1213,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1192,c_148])).

tff(c_1219,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1192,c_70])).

tff(c_1209,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1192,c_1192,c_1050])).

tff(c_1218,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1192,c_64])).

tff(c_99,plain,(
    ! [A_37] :
      ( k1_relat_1(A_37) != k1_xboole_0
      | k1_xboole_0 = A_37
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_106,plain,(
    ! [A_15] :
      ( k1_relat_1(k2_funct_1(A_15)) != k1_xboole_0
      | k2_funct_1(A_15) = k1_xboole_0
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(resolution,[status(thm)],[c_26,c_99])).

tff(c_1177,plain,(
    ! [A_175] :
      ( k1_relat_1(k2_funct_1(A_175)) != '#skF_5'
      | k2_funct_1(A_175) = '#skF_5'
      | ~ v1_funct_1(A_175)
      | ~ v1_relat_1(A_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1034,c_1034,c_106])).

tff(c_1180,plain,(
    ! [A_16] :
      ( k2_relat_1(A_16) != '#skF_5'
      | k2_funct_1(A_16) = '#skF_5'
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1177])).

tff(c_1659,plain,(
    ! [A_238] :
      ( k2_relat_1(A_238) != '#skF_4'
      | k2_funct_1(A_238) = '#skF_4'
      | ~ v1_funct_1(A_238)
      | ~ v1_relat_1(A_238)
      | ~ v2_funct_1(A_238)
      | ~ v1_funct_1(A_238)
      | ~ v1_relat_1(A_238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1192,c_1192,c_1180])).

tff(c_1662,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1218,c_1659])).

tff(c_1665,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1213,c_1219,c_1209,c_1662])).

tff(c_1214,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1192,c_139])).

tff(c_1666,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1665,c_1214])).

tff(c_1670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1206,c_1666])).

tff(c_1671,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_1672,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_1868,plain,(
    ! [A_271,B_272,C_273] :
      ( k1_relset_1(A_271,B_272,C_273) = k1_relat_1(C_273)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1884,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1672,c_1868])).

tff(c_2072,plain,(
    ! [B_306,C_307,A_308] :
      ( k1_xboole_0 = B_306
      | v1_funct_2(C_307,A_308,B_306)
      | k1_relset_1(A_308,B_306,C_307) != A_308
      | ~ m1_subset_1(C_307,k1_zfmisc_1(k2_zfmisc_1(A_308,B_306))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2078,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_1672,c_2072])).

tff(c_2088,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1884,c_2078])).

tff(c_2089,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1671,c_2088])).

tff(c_2095,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2089])).

tff(c_2098,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2095])).

tff(c_2101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1685,c_70,c_64,c_1917,c_2098])).

tff(c_2102,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2089])).

tff(c_1693,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1685,c_20])).

tff(c_1724,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1693])).

tff(c_2119,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2102,c_1724])).

tff(c_1694,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1685,c_18])).

tff(c_1725,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1694])).

tff(c_1920,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1917,c_1725])).

tff(c_2111,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2102,c_1920])).

tff(c_1885,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1868])).

tff(c_52,plain,(
    ! [B_27,A_26,C_28] :
      ( k1_xboole_0 = B_27
      | k1_relset_1(A_26,B_27,C_28) = A_26
      | ~ v1_funct_2(C_28,A_26,B_27)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2157,plain,(
    ! [B_309,A_310,C_311] :
      ( B_309 = '#skF_3'
      | k1_relset_1(A_310,B_309,C_311) = A_310
      | ~ v1_funct_2(C_311,A_310,B_309)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_310,B_309))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2102,c_52])).

tff(c_2166,plain,
    ( '#skF_3' = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_2157])).

tff(c_2172,plain,
    ( '#skF_3' = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1885,c_2166])).

tff(c_2174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2119,c_2111,c_2172])).

tff(c_2175,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1694])).

tff(c_2177,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2175,c_1724])).

tff(c_2187,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2175,c_2175,c_16])).

tff(c_2201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2177,c_2187])).

tff(c_2202,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1693])).

tff(c_2212,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2202,c_2202,c_14])).

tff(c_2210,plain,(
    ! [A_7] : m1_subset_1('#skF_5',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2202,c_10])).

tff(c_2517,plain,(
    ! [A_355,B_356,C_357] :
      ( k2_relset_1(A_355,B_356,C_357) = k2_relat_1(C_357)
      | ~ m1_subset_1(C_357,k1_zfmisc_1(k2_zfmisc_1(A_355,B_356))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2525,plain,(
    ! [A_355,B_356] : k2_relset_1(A_355,B_356,'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2210,c_2517])).

tff(c_2529,plain,(
    ! [A_358,B_359] : k2_relset_1(A_358,B_359,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2212,c_2525])).

tff(c_2533,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2529,c_62])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2211,plain,(
    ! [A_6] : r1_tarski('#skF_5',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2202,c_8])).

tff(c_2555,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2533,c_2211])).

tff(c_2554,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2533,c_2533,c_2212])).

tff(c_2558,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2533,c_1685])).

tff(c_2562,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2533,c_70])).

tff(c_2203,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1693])).

tff(c_2219,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2202,c_2203])).

tff(c_2556,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2533,c_2533,c_2219])).

tff(c_2577,plain,(
    ! [B_361,A_362] :
      ( v1_funct_2(B_361,k1_relat_1(B_361),A_362)
      | ~ r1_tarski(k2_relat_1(B_361),A_362)
      | ~ v1_funct_1(B_361)
      | ~ v1_relat_1(B_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2580,plain,(
    ! [A_362] :
      ( v1_funct_2('#skF_4','#skF_4',A_362)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_362)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2556,c_2577])).

tff(c_2585,plain,(
    ! [A_362] :
      ( v1_funct_2('#skF_4','#skF_4',A_362)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_362) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2562,c_2580])).

tff(c_2671,plain,(
    ! [A_362] : v1_funct_2('#skF_4','#skF_4',A_362) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2555,c_2554,c_2585])).

tff(c_2319,plain,(
    ! [A_329] :
      ( k2_relat_1(k2_funct_1(A_329)) = k1_relat_1(A_329)
      | ~ v2_funct_1(A_329)
      | ~ v1_funct_1(A_329)
      | ~ v1_relat_1(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1684,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1672,c_1673])).

tff(c_1716,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) != k1_xboole_0
    | k2_funct_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1684,c_18])).

tff(c_2260,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2202,c_2202,c_1716])).

tff(c_2261,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2260])).

tff(c_2325,plain,
    ( k1_relat_1('#skF_5') != '#skF_5'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2319,c_2261])).

tff(c_2332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1685,c_70,c_64,c_2219,c_2325])).

tff(c_2333,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2260])).

tff(c_1715,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) != k1_xboole_0
    | k2_funct_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1684,c_20])).

tff(c_2245,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2202,c_2202,c_1715])).

tff(c_2246,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2245])).

tff(c_2335,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2333,c_2246])).

tff(c_2342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2219,c_2335])).

tff(c_2343,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2245])).

tff(c_2354,plain,(
    ~ v1_funct_2('#skF_5','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2343,c_1671])).

tff(c_2548,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2533,c_2354])).

tff(c_2674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2671,c_2548])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n012.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 19:26:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.11/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.77  
% 4.53/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.77  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.53/1.77  
% 4.53/1.77  %Foreground sorts:
% 4.53/1.77  
% 4.53/1.77  
% 4.53/1.77  %Background operators:
% 4.53/1.77  
% 4.53/1.77  
% 4.53/1.77  %Foreground operators:
% 4.53/1.77  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.53/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.53/1.77  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.53/1.77  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.53/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.53/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.53/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.53/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.53/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.53/1.77  tff('#skF_5', type, '#skF_5': $i).
% 4.53/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.53/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.53/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.53/1.77  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.53/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.53/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.53/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.53/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.53/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.53/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.53/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.53/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.53/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.53/1.77  
% 4.66/1.79  tff(f_143, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.66/1.79  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.66/1.79  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.66/1.79  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 4.66/1.79  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.66/1.79  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 4.66/1.79  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.66/1.79  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.66/1.79  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.66/1.79  tff(f_126, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 4.66/1.79  tff(f_45, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.66/1.79  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.66/1.79  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.66/1.79  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.66/1.79  tff(c_1673, plain, (![C_239, A_240, B_241]: (v1_relat_1(C_239) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.66/1.79  tff(c_1685, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_1673])).
% 4.66/1.79  tff(c_70, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.66/1.79  tff(c_64, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.66/1.79  tff(c_62, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.66/1.79  tff(c_1899, plain, (![A_276, B_277, C_278]: (k2_relset_1(A_276, B_277, C_278)=k2_relat_1(C_278) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.79  tff(c_1909, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_1899])).
% 4.66/1.79  tff(c_1917, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1909])).
% 4.66/1.79  tff(c_34, plain, (![A_16]: (k1_relat_1(k2_funct_1(A_16))=k2_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.66/1.79  tff(c_140, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.66/1.79  tff(c_148, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_140])).
% 4.66/1.79  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.66/1.79  tff(c_173, plain, (![A_50, B_51]: (~r2_hidden('#skF_1'(A_50, B_51), B_51) | r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.66/1.79  tff(c_178, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_173])).
% 4.66/1.79  tff(c_289, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.79  tff(c_296, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_289])).
% 4.66/1.79  tff(c_303, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_296])).
% 4.66/1.79  tff(c_18, plain, (![A_11]: (k2_relat_1(A_11)!=k1_xboole_0 | k1_xboole_0=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.66/1.79  tff(c_157, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_148, c_18])).
% 4.66/1.79  tff(c_180, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_157])).
% 4.66/1.79  tff(c_306, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_303, c_180])).
% 4.66/1.79  tff(c_68, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.66/1.79  tff(c_318, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.66/1.79  tff(c_331, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_318])).
% 4.66/1.79  tff(c_476, plain, (![B_110, A_111, C_112]: (k1_xboole_0=B_110 | k1_relset_1(A_111, B_110, C_112)=A_111 | ~v1_funct_2(C_112, A_111, B_110) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_111, B_110))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.66/1.79  tff(c_482, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_476])).
% 4.66/1.79  tff(c_490, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_331, c_482])).
% 4.66/1.79  tff(c_491, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_306, c_490])).
% 4.66/1.79  tff(c_32, plain, (![A_16]: (k2_relat_1(k2_funct_1(A_16))=k1_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.66/1.79  tff(c_26, plain, (![A_15]: (v1_relat_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.66/1.79  tff(c_24, plain, (![A_15]: (v1_funct_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.66/1.79  tff(c_60, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.66/1.79  tff(c_110, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_60])).
% 4.66/1.79  tff(c_113, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_110])).
% 4.66/1.79  tff(c_116, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_113])).
% 4.66/1.79  tff(c_124, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.66/1.79  tff(c_127, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_124])).
% 4.66/1.79  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_127])).
% 4.66/1.79  tff(c_137, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_60])).
% 4.66/1.79  tff(c_345, plain, (![B_87, A_88]: (v1_funct_2(B_87, k1_relat_1(B_87), A_88) | ~r1_tarski(k2_relat_1(B_87), A_88) | ~v1_funct_1(B_87) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.66/1.79  tff(c_803, plain, (![A_137, A_138]: (v1_funct_2(k2_funct_1(A_137), k2_relat_1(A_137), A_138) | ~r1_tarski(k2_relat_1(k2_funct_1(A_137)), A_138) | ~v1_funct_1(k2_funct_1(A_137)) | ~v1_relat_1(k2_funct_1(A_137)) | ~v2_funct_1(A_137) | ~v1_funct_1(A_137) | ~v1_relat_1(A_137))), inference(superposition, [status(thm), theory('equality')], [c_34, c_345])).
% 4.66/1.79  tff(c_806, plain, (![A_138]: (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', A_138) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_5')), A_138) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_303, c_803])).
% 4.66/1.79  tff(c_814, plain, (![A_138]: (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', A_138) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_5')), A_138) | ~v1_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_70, c_64, c_137, c_806])).
% 4.66/1.79  tff(c_817, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_814])).
% 4.66/1.79  tff(c_866, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_817])).
% 4.66/1.79  tff(c_870, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_70, c_866])).
% 4.66/1.79  tff(c_872, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_814])).
% 4.66/1.79  tff(c_411, plain, (![B_103, A_104]: (m1_subset_1(B_103, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_103), A_104))) | ~r1_tarski(k2_relat_1(B_103), A_104) | ~v1_funct_1(B_103) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.66/1.79  tff(c_909, plain, (![A_142, A_143]: (m1_subset_1(k2_funct_1(A_142), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_142), A_143))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_142)), A_143) | ~v1_funct_1(k2_funct_1(A_142)) | ~v1_relat_1(k2_funct_1(A_142)) | ~v2_funct_1(A_142) | ~v1_funct_1(A_142) | ~v1_relat_1(A_142))), inference(superposition, [status(thm), theory('equality')], [c_34, c_411])).
% 4.66/1.79  tff(c_936, plain, (![A_143]: (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_143))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_5')), A_143) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_303, c_909])).
% 4.66/1.79  tff(c_956, plain, (![A_145]: (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_145))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_5')), A_145))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_70, c_64, c_872, c_137, c_936])).
% 4.66/1.79  tff(c_136, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_60])).
% 4.66/1.79  tff(c_139, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_136])).
% 4.66/1.79  tff(c_996, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_5')), '#skF_3')), inference(resolution, [status(thm)], [c_956, c_139])).
% 4.66/1.79  tff(c_999, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_32, c_996])).
% 4.66/1.79  tff(c_1002, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_70, c_64, c_178, c_491, c_999])).
% 4.66/1.79  tff(c_1003, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_157])).
% 4.66/1.79  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.66/1.79  tff(c_1015, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1003, c_1003, c_16])).
% 4.66/1.79  tff(c_20, plain, (![A_11]: (k1_relat_1(A_11)!=k1_xboole_0 | k1_xboole_0=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.66/1.79  tff(c_156, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_148, c_20])).
% 4.66/1.79  tff(c_172, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_156])).
% 4.66/1.79  tff(c_1005, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1003, c_172])).
% 4.66/1.79  tff(c_1033, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1015, c_1005])).
% 4.66/1.79  tff(c_1034, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_156])).
% 4.66/1.79  tff(c_14, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.66/1.79  tff(c_1050, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1034, c_1034, c_14])).
% 4.66/1.79  tff(c_10, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.66/1.79  tff(c_1048, plain, (![A_7]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_1034, c_10])).
% 4.66/1.79  tff(c_1181, plain, (![A_176, B_177, C_178]: (k2_relset_1(A_176, B_177, C_178)=k2_relat_1(C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.79  tff(c_1185, plain, (![A_176, B_177]: (k2_relset_1(A_176, B_177, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1048, c_1181])).
% 4.66/1.79  tff(c_1188, plain, (![A_179, B_180]: (k2_relset_1(A_179, B_180, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1050, c_1185])).
% 4.66/1.79  tff(c_1192, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1188, c_62])).
% 4.66/1.79  tff(c_1206, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_1192, c_1048])).
% 4.66/1.79  tff(c_1213, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1192, c_148])).
% 4.66/1.79  tff(c_1219, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1192, c_70])).
% 4.66/1.79  tff(c_1209, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1192, c_1192, c_1050])).
% 4.66/1.79  tff(c_1218, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1192, c_64])).
% 4.66/1.79  tff(c_99, plain, (![A_37]: (k1_relat_1(A_37)!=k1_xboole_0 | k1_xboole_0=A_37 | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.66/1.79  tff(c_106, plain, (![A_15]: (k1_relat_1(k2_funct_1(A_15))!=k1_xboole_0 | k2_funct_1(A_15)=k1_xboole_0 | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(resolution, [status(thm)], [c_26, c_99])).
% 4.66/1.79  tff(c_1177, plain, (![A_175]: (k1_relat_1(k2_funct_1(A_175))!='#skF_5' | k2_funct_1(A_175)='#skF_5' | ~v1_funct_1(A_175) | ~v1_relat_1(A_175))), inference(demodulation, [status(thm), theory('equality')], [c_1034, c_1034, c_106])).
% 4.66/1.79  tff(c_1180, plain, (![A_16]: (k2_relat_1(A_16)!='#skF_5' | k2_funct_1(A_16)='#skF_5' | ~v1_funct_1(A_16) | ~v1_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1177])).
% 4.66/1.79  tff(c_1659, plain, (![A_238]: (k2_relat_1(A_238)!='#skF_4' | k2_funct_1(A_238)='#skF_4' | ~v1_funct_1(A_238) | ~v1_relat_1(A_238) | ~v2_funct_1(A_238) | ~v1_funct_1(A_238) | ~v1_relat_1(A_238))), inference(demodulation, [status(thm), theory('equality')], [c_1192, c_1192, c_1180])).
% 4.66/1.79  tff(c_1662, plain, (k2_relat_1('#skF_4')!='#skF_4' | k2_funct_1('#skF_4')='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1218, c_1659])).
% 4.66/1.79  tff(c_1665, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1213, c_1219, c_1209, c_1662])).
% 4.66/1.79  tff(c_1214, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1192, c_139])).
% 4.66/1.79  tff(c_1666, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1665, c_1214])).
% 4.66/1.79  tff(c_1670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1206, c_1666])).
% 4.66/1.79  tff(c_1671, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_136])).
% 4.66/1.79  tff(c_1672, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_136])).
% 4.66/1.80  tff(c_1868, plain, (![A_271, B_272, C_273]: (k1_relset_1(A_271, B_272, C_273)=k1_relat_1(C_273) | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.66/1.80  tff(c_1884, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_1672, c_1868])).
% 4.66/1.80  tff(c_2072, plain, (![B_306, C_307, A_308]: (k1_xboole_0=B_306 | v1_funct_2(C_307, A_308, B_306) | k1_relset_1(A_308, B_306, C_307)!=A_308 | ~m1_subset_1(C_307, k1_zfmisc_1(k2_zfmisc_1(A_308, B_306))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.66/1.80  tff(c_2078, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_1672, c_2072])).
% 4.66/1.80  tff(c_2088, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1884, c_2078])).
% 4.66/1.80  tff(c_2089, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1671, c_2088])).
% 4.66/1.80  tff(c_2095, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_2089])).
% 4.66/1.80  tff(c_2098, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_34, c_2095])).
% 4.66/1.80  tff(c_2101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1685, c_70, c_64, c_1917, c_2098])).
% 4.66/1.80  tff(c_2102, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2089])).
% 4.66/1.80  tff(c_1693, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1685, c_20])).
% 4.66/1.80  tff(c_1724, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1693])).
% 4.66/1.80  tff(c_2119, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2102, c_1724])).
% 4.66/1.80  tff(c_1694, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1685, c_18])).
% 4.66/1.80  tff(c_1725, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1694])).
% 4.66/1.80  tff(c_1920, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1917, c_1725])).
% 4.66/1.80  tff(c_2111, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2102, c_1920])).
% 4.66/1.80  tff(c_1885, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_1868])).
% 4.66/1.80  tff(c_52, plain, (![B_27, A_26, C_28]: (k1_xboole_0=B_27 | k1_relset_1(A_26, B_27, C_28)=A_26 | ~v1_funct_2(C_28, A_26, B_27) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.66/1.80  tff(c_2157, plain, (![B_309, A_310, C_311]: (B_309='#skF_3' | k1_relset_1(A_310, B_309, C_311)=A_310 | ~v1_funct_2(C_311, A_310, B_309) | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_310, B_309))))), inference(demodulation, [status(thm), theory('equality')], [c_2102, c_52])).
% 4.66/1.80  tff(c_2166, plain, ('#skF_3'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_2157])).
% 4.66/1.80  tff(c_2172, plain, ('#skF_3'='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1885, c_2166])).
% 4.66/1.80  tff(c_2174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2119, c_2111, c_2172])).
% 4.66/1.80  tff(c_2175, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1694])).
% 4.66/1.80  tff(c_2177, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2175, c_1724])).
% 4.66/1.80  tff(c_2187, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2175, c_2175, c_16])).
% 4.66/1.80  tff(c_2201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2177, c_2187])).
% 4.66/1.80  tff(c_2202, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1693])).
% 4.66/1.80  tff(c_2212, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2202, c_2202, c_14])).
% 4.66/1.80  tff(c_2210, plain, (![A_7]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_2202, c_10])).
% 4.66/1.80  tff(c_2517, plain, (![A_355, B_356, C_357]: (k2_relset_1(A_355, B_356, C_357)=k2_relat_1(C_357) | ~m1_subset_1(C_357, k1_zfmisc_1(k2_zfmisc_1(A_355, B_356))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.80  tff(c_2525, plain, (![A_355, B_356]: (k2_relset_1(A_355, B_356, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_2210, c_2517])).
% 4.66/1.80  tff(c_2529, plain, (![A_358, B_359]: (k2_relset_1(A_358, B_359, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2212, c_2525])).
% 4.66/1.80  tff(c_2533, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2529, c_62])).
% 4.66/1.80  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.66/1.80  tff(c_2211, plain, (![A_6]: (r1_tarski('#skF_5', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_2202, c_8])).
% 4.66/1.80  tff(c_2555, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_2533, c_2211])).
% 4.66/1.80  tff(c_2554, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2533, c_2533, c_2212])).
% 4.66/1.80  tff(c_2558, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2533, c_1685])).
% 4.66/1.80  tff(c_2562, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2533, c_70])).
% 4.66/1.80  tff(c_2203, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1693])).
% 4.66/1.80  tff(c_2219, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2202, c_2203])).
% 4.66/1.80  tff(c_2556, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2533, c_2533, c_2219])).
% 4.66/1.80  tff(c_2577, plain, (![B_361, A_362]: (v1_funct_2(B_361, k1_relat_1(B_361), A_362) | ~r1_tarski(k2_relat_1(B_361), A_362) | ~v1_funct_1(B_361) | ~v1_relat_1(B_361))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.66/1.80  tff(c_2580, plain, (![A_362]: (v1_funct_2('#skF_4', '#skF_4', A_362) | ~r1_tarski(k2_relat_1('#skF_4'), A_362) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2556, c_2577])).
% 4.66/1.80  tff(c_2585, plain, (![A_362]: (v1_funct_2('#skF_4', '#skF_4', A_362) | ~r1_tarski(k2_relat_1('#skF_4'), A_362))), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2562, c_2580])).
% 4.66/1.80  tff(c_2671, plain, (![A_362]: (v1_funct_2('#skF_4', '#skF_4', A_362))), inference(demodulation, [status(thm), theory('equality')], [c_2555, c_2554, c_2585])).
% 4.66/1.80  tff(c_2319, plain, (![A_329]: (k2_relat_1(k2_funct_1(A_329))=k1_relat_1(A_329) | ~v2_funct_1(A_329) | ~v1_funct_1(A_329) | ~v1_relat_1(A_329))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.66/1.80  tff(c_1684, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_1672, c_1673])).
% 4.66/1.80  tff(c_1716, plain, (k2_relat_1(k2_funct_1('#skF_5'))!=k1_xboole_0 | k2_funct_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_1684, c_18])).
% 4.66/1.80  tff(c_2260, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2202, c_2202, c_1716])).
% 4.66/1.80  tff(c_2261, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_2260])).
% 4.66/1.80  tff(c_2325, plain, (k1_relat_1('#skF_5')!='#skF_5' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2319, c_2261])).
% 4.66/1.80  tff(c_2332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1685, c_70, c_64, c_2219, c_2325])).
% 4.66/1.80  tff(c_2333, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_2260])).
% 4.66/1.80  tff(c_1715, plain, (k1_relat_1(k2_funct_1('#skF_5'))!=k1_xboole_0 | k2_funct_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_1684, c_20])).
% 4.66/1.80  tff(c_2245, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2202, c_2202, c_1715])).
% 4.66/1.80  tff(c_2246, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_2245])).
% 4.66/1.80  tff(c_2335, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2333, c_2246])).
% 4.66/1.80  tff(c_2342, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2219, c_2335])).
% 4.66/1.80  tff(c_2343, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_2245])).
% 4.66/1.80  tff(c_2354, plain, (~v1_funct_2('#skF_5', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2343, c_1671])).
% 4.66/1.80  tff(c_2548, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2533, c_2354])).
% 4.66/1.80  tff(c_2674, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2671, c_2548])).
% 4.66/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.66/1.80  
% 4.66/1.80  Inference rules
% 4.66/1.80  ----------------------
% 4.66/1.80  #Ref     : 0
% 4.66/1.80  #Sup     : 530
% 4.66/1.80  #Fact    : 0
% 4.66/1.80  #Define  : 0
% 4.66/1.80  #Split   : 20
% 4.66/1.80  #Chain   : 0
% 4.66/1.80  #Close   : 0
% 4.66/1.80  
% 4.66/1.80  Ordering : KBO
% 4.66/1.80  
% 4.66/1.80  Simplification rules
% 4.66/1.80  ----------------------
% 4.66/1.80  #Subsume      : 87
% 4.66/1.80  #Demod        : 687
% 4.66/1.80  #Tautology    : 268
% 4.66/1.80  #SimpNegUnit  : 11
% 4.66/1.80  #BackRed      : 129
% 4.66/1.80  
% 4.66/1.80  #Partial instantiations: 0
% 4.66/1.80  #Strategies tried      : 1
% 4.66/1.80  
% 4.66/1.80  Timing (in seconds)
% 4.66/1.80  ----------------------
% 4.66/1.80  Preprocessing        : 0.35
% 4.66/1.80  Parsing              : 0.19
% 4.66/1.80  CNF conversion       : 0.02
% 4.66/1.80  Main loop            : 0.67
% 4.66/1.80  Inferencing          : 0.26
% 4.66/1.80  Reduction            : 0.21
% 4.66/1.80  Demodulation         : 0.15
% 4.66/1.80  BG Simplification    : 0.03
% 4.66/1.80  Subsumption          : 0.11
% 4.66/1.80  Abstraction          : 0.03
% 4.66/1.80  MUC search           : 0.00
% 4.66/1.80  Cooper               : 0.00
% 4.66/1.80  Total                : 1.07
% 4.66/1.80  Index Insertion      : 0.00
% 4.66/1.80  Index Deletion       : 0.00
% 4.66/1.80  Index Matching       : 0.00
% 4.66/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
