%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:49 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 628 expanded)
%              Number of leaves         :   29 ( 218 expanded)
%              Depth                    :   17
%              Number of atoms          :  219 (1554 expanded)
%              Number of equality atoms :   68 ( 498 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_89,axiom,(
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

tff(f_71,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2312,plain,(
    ! [A_320] :
      ( r1_tarski(A_320,k2_zfmisc_1(k1_relat_1(A_320),k2_relat_1(A_320)))
      | ~ v1_relat_1(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_8] :
      ( r1_tarski(A_8,k2_zfmisc_1(k1_relat_1(A_8),k2_relat_1(A_8)))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_802,plain,(
    ! [A_188,B_189,C_190] :
      ( k1_relset_1(A_188,B_189,C_190) = k1_relat_1(C_190)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1104,plain,(
    ! [A_225,B_226,A_227] :
      ( k1_relset_1(A_225,B_226,A_227) = k1_relat_1(A_227)
      | ~ r1_tarski(A_227,k2_zfmisc_1(A_225,B_226)) ) ),
    inference(resolution,[status(thm)],[c_12,c_802])).

tff(c_1120,plain,(
    ! [A_8] :
      ( k1_relset_1(k1_relat_1(A_8),k2_relat_1(A_8),A_8) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_16,c_1104])).

tff(c_995,plain,(
    ! [B_210,C_211,A_212] :
      ( k1_xboole_0 = B_210
      | v1_funct_2(C_211,A_212,B_210)
      | k1_relset_1(A_212,B_210,C_211) != A_212
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_212,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1643,plain,(
    ! [B_279,A_280,A_281] :
      ( k1_xboole_0 = B_279
      | v1_funct_2(A_280,A_281,B_279)
      | k1_relset_1(A_281,B_279,A_280) != A_281
      | ~ r1_tarski(A_280,k2_zfmisc_1(A_281,B_279)) ) ),
    inference(resolution,[status(thm)],[c_12,c_995])).

tff(c_2026,plain,(
    ! [A_306] :
      ( k2_relat_1(A_306) = k1_xboole_0
      | v1_funct_2(A_306,k1_relat_1(A_306),k2_relat_1(A_306))
      | k1_relset_1(k1_relat_1(A_306),k2_relat_1(A_306),A_306) != k1_relat_1(A_306)
      | ~ v1_relat_1(A_306) ) ),
    inference(resolution,[status(thm)],[c_16,c_1643])).

tff(c_42,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_40,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40])).

tff(c_91,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_2033,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2026,c_91])).

tff(c_2045,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2033])).

tff(c_2048,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2045])).

tff(c_2054,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1120,c_2048])).

tff(c_2060,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2054])).

tff(c_2061,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2045])).

tff(c_22,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_1'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_93,plain,(
    ! [C_42,B_43,A_44] :
      ( ~ v1_xboole_0(C_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(C_42))
      | ~ r2_hidden(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_97,plain,(
    ! [B_45,A_46,A_47] :
      ( ~ v1_xboole_0(B_45)
      | ~ r2_hidden(A_46,A_47)
      | ~ r1_tarski(A_47,B_45) ) ),
    inference(resolution,[status(thm)],[c_12,c_93])).

tff(c_101,plain,(
    ! [B_48,A_49] :
      ( ~ v1_xboole_0(B_48)
      | ~ r1_tarski(A_49,B_48)
      | k1_xboole_0 = A_49 ) ),
    inference(resolution,[status(thm)],[c_22,c_97])).

tff(c_105,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(A_8),k2_relat_1(A_8)))
      | k1_xboole_0 = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_16,c_101])).

tff(c_2076,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_2'),k1_xboole_0))
    | k1_xboole_0 = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2061,c_105])).

tff(c_2089,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2,c_6,c_2076])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_151,plain,(
    ! [A_78,B_79,C_80] :
      ( m1_subset_1(k1_relset_1(A_78,B_79,C_80),k1_zfmisc_1(A_78))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_209,plain,(
    ! [A_89,B_90,C_91] :
      ( r1_tarski(k1_relset_1(A_89,B_90,C_91),A_89)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(resolution,[status(thm)],[c_151,c_10])).

tff(c_219,plain,(
    ! [B_2,C_91] :
      ( r1_tarski(k1_relset_1(k1_xboole_0,B_2,C_91),k1_xboole_0)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_209])).

tff(c_221,plain,(
    ! [A_89,B_90,A_3] :
      ( r1_tarski(k1_relset_1(A_89,B_90,A_3),A_89)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_89,B_90)) ) ),
    inference(resolution,[status(thm)],[c_12,c_209])).

tff(c_28,plain,(
    ! [A_29] :
      ( v1_funct_2(k1_xboole_0,A_29,k1_xboole_0)
      | k1_xboole_0 = A_29
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_29,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_49,plain,(
    ! [A_29] :
      ( v1_funct_2(k1_xboole_0,A_29,k1_xboole_0)
      | k1_xboole_0 = A_29
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_28])).

tff(c_106,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_110,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_106])).

tff(c_293,plain,(
    ! [A_105,B_106,A_107] :
      ( r1_tarski(k1_relset_1(A_105,B_106,A_107),A_105)
      | ~ r1_tarski(A_107,k2_zfmisc_1(A_105,B_106)) ) ),
    inference(resolution,[status(thm)],[c_12,c_209])).

tff(c_244,plain,(
    ! [B_96,C_97] :
      ( r1_tarski(k1_relset_1(k1_xboole_0,B_96,C_97),k1_xboole_0)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_209])).

tff(c_100,plain,(
    ! [B_45,A_15] :
      ( ~ v1_xboole_0(B_45)
      | ~ r1_tarski(A_15,B_45)
      | k1_xboole_0 = A_15 ) ),
    inference(resolution,[status(thm)],[c_22,c_97])).

tff(c_251,plain,(
    ! [B_96,C_97] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | k1_relset_1(k1_xboole_0,B_96,C_97) = k1_xboole_0
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_244,c_100])).

tff(c_257,plain,(
    ! [B_98,C_99] :
      ( k1_relset_1(k1_xboole_0,B_98,C_99) = k1_xboole_0
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_251])).

tff(c_266,plain,(
    ! [B_98,A_3] :
      ( k1_relset_1(k1_xboole_0,B_98,A_3) = k1_xboole_0
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_257])).

tff(c_296,plain,(
    ! [B_98,B_106,A_107] :
      ( k1_relset_1(k1_xboole_0,B_98,k1_relset_1(k1_xboole_0,B_106,A_107)) = k1_xboole_0
      | ~ r1_tarski(A_107,k2_zfmisc_1(k1_xboole_0,B_106)) ) ),
    inference(resolution,[status(thm)],[c_293,c_266])).

tff(c_325,plain,(
    ! [B_110,B_111,A_112] :
      ( k1_relset_1(k1_xboole_0,B_110,k1_relset_1(k1_xboole_0,B_111,A_112)) = k1_xboole_0
      | ~ r1_tarski(A_112,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_296])).

tff(c_334,plain,(
    ! [B_111,A_112,B_110] :
      ( r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_relset_1(k1_xboole_0,B_111,A_112),k2_zfmisc_1(k1_xboole_0,B_110))
      | ~ r1_tarski(A_112,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_221])).

tff(c_352,plain,(
    ! [B_111,A_112] :
      ( r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_relset_1(k1_xboole_0,B_111,A_112),k1_xboole_0)
      | ~ r1_tarski(A_112,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_334])).

tff(c_359,plain,(
    ! [B_113,A_114] :
      ( ~ r1_tarski(k1_relset_1(k1_xboole_0,B_113,A_114),k1_xboole_0)
      | ~ r1_tarski(A_114,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_352])).

tff(c_366,plain,(
    ! [A_3,B_90] :
      ( ~ r1_tarski(A_3,k1_xboole_0)
      | ~ r1_tarski(A_3,k2_zfmisc_1(k1_xboole_0,B_90)) ) ),
    inference(resolution,[status(thm)],[c_221,c_359])).

tff(c_396,plain,(
    ! [A_118] :
      ( ~ r1_tarski(A_118,k1_xboole_0)
      | ~ r1_tarski(A_118,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_366])).

tff(c_446,plain,(
    ! [B_126,C_127] :
      ( ~ r1_tarski(k1_relset_1(k1_xboole_0,B_126,C_127),k1_xboole_0)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_219,c_396])).

tff(c_465,plain,(
    ! [C_128] : ~ m1_subset_1(C_128,k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_219,c_446])).

tff(c_476,plain,(
    ! [A_3] : ~ r1_tarski(A_3,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_465])).

tff(c_123,plain,(
    ! [A_67,B_68,C_69] :
      ( k1_relset_1(A_67,B_68,C_69) = k1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_180,plain,(
    ! [A_83,B_84,A_85] :
      ( k1_relset_1(A_83,B_84,A_85) = k1_relat_1(A_85)
      | ~ r1_tarski(A_85,k2_zfmisc_1(A_83,B_84)) ) ),
    inference(resolution,[status(thm)],[c_12,c_123])).

tff(c_190,plain,(
    ! [A_8] :
      ( k1_relset_1(k1_relat_1(A_8),k2_relat_1(A_8),A_8) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_16,c_180])).

tff(c_267,plain,(
    ! [B_100,C_101,A_102] :
      ( k1_xboole_0 = B_100
      | v1_funct_2(C_101,A_102,B_100)
      | k1_relset_1(A_102,B_100,C_101) != A_102
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_561,plain,(
    ! [B_140,A_141,A_142] :
      ( k1_xboole_0 = B_140
      | v1_funct_2(A_141,A_142,B_140)
      | k1_relset_1(A_142,B_140,A_141) != A_142
      | ~ r1_tarski(A_141,k2_zfmisc_1(A_142,B_140)) ) ),
    inference(resolution,[status(thm)],[c_12,c_267])).

tff(c_722,plain,(
    ! [A_170] :
      ( k2_relat_1(A_170) = k1_xboole_0
      | v1_funct_2(A_170,k1_relat_1(A_170),k2_relat_1(A_170))
      | k1_relset_1(k1_relat_1(A_170),k2_relat_1(A_170),A_170) != k1_relat_1(A_170)
      | ~ v1_relat_1(A_170) ) ),
    inference(resolution,[status(thm)],[c_16,c_561])).

tff(c_725,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_722,c_91])).

tff(c_728,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_725])).

tff(c_729,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_728])).

tff(c_732,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_729])).

tff(c_736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_732])).

tff(c_737,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_728])).

tff(c_752,plain,
    ( r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),k1_xboole_0))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_737,c_16])).

tff(c_762,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6,c_752])).

tff(c_764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_476,c_762])).

tff(c_766,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_814,plain,(
    ! [A_191,C_192] :
      ( k1_relset_1(A_191,k1_xboole_0,C_192) = k1_relat_1(C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_802])).

tff(c_820,plain,(
    ! [A_191] : k1_relset_1(A_191,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_766,c_814])).

tff(c_849,plain,(
    ! [A_200,B_201,C_202] :
      ( m1_subset_1(k1_relset_1(A_200,B_201,C_202),k1_zfmisc_1(A_200))
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_867,plain,(
    ! [A_191] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_191))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_191,k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_849])).

tff(c_877,plain,(
    ! [A_203] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_203)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_766,c_6,c_867])).

tff(c_898,plain,(
    ! [A_204] : r1_tarski(k1_relat_1(k1_xboole_0),A_204) ),
    inference(resolution,[status(thm)],[c_877,c_10])).

tff(c_906,plain,(
    ! [A_204] :
      ( ~ v1_xboole_0(A_204)
      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_898,c_100])).

tff(c_907,plain,(
    ! [A_204] : ~ v1_xboole_0(A_204) ),
    inference(splitLeft,[status(thm)],[c_906])).

tff(c_909,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_907,c_2])).

tff(c_910,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_906])).

tff(c_876,plain,(
    ! [A_191] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_191)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_766,c_6,c_867])).

tff(c_954,plain,(
    ! [A_208] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_208)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_910,c_876])).

tff(c_20,plain,(
    ! [A_12,B_13,C_14] :
      ( k1_relset_1(A_12,B_13,C_14) = k1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_967,plain,(
    ! [A_12,B_13] : k1_relset_1(A_12,B_13,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_954,c_20])).

tff(c_979,plain,(
    ! [A_12,B_13] : k1_relset_1(A_12,B_13,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_910,c_967])).

tff(c_32,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_928,plain,(
    ! [C_205,B_206] :
      ( v1_funct_2(C_205,k1_xboole_0,B_206)
      | k1_relset_1(k1_xboole_0,B_206,C_205) != k1_xboole_0
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_32])).

tff(c_939,plain,(
    ! [B_206] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_206)
      | k1_relset_1(k1_xboole_0,B_206,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_766,c_928])).

tff(c_1079,plain,(
    ! [B_206] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_206) ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_939])).

tff(c_2120,plain,(
    ! [B_206] : v1_funct_2('#skF_2','#skF_2',B_206) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2089,c_2089,c_1079])).

tff(c_2128,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2089,c_2089,c_910])).

tff(c_2063,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2061,c_91])).

tff(c_2175,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2089,c_2063])).

tff(c_2183,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_2175])).

tff(c_2305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2120,c_2183])).

tff(c_2306,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2311,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_12,c_2306])).

tff(c_2315,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2312,c_2311])).

tff(c_2319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2315])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:43:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.05/1.66  
% 4.05/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.05/1.66  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2
% 4.05/1.66  
% 4.05/1.66  %Foreground sorts:
% 4.05/1.66  
% 4.05/1.66  
% 4.05/1.66  %Background operators:
% 4.05/1.66  
% 4.05/1.66  
% 4.05/1.66  %Foreground operators:
% 4.05/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.05/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.05/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.05/1.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.05/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.05/1.66  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 4.05/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.05/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.05/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.05/1.66  tff('#skF_2', type, '#skF_2': $i).
% 4.05/1.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.05/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.05/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.05/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.05/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.05/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.05/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.05/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.05/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.05/1.66  
% 4.18/1.68  tff(f_100, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.18/1.68  tff(f_47, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 4.18/1.68  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.18/1.68  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.18/1.68  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.18/1.68  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.18/1.68  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.18/1.68  tff(f_71, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 4.18/1.68  tff(f_43, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.18/1.68  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.18/1.68  tff(c_44, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.18/1.68  tff(c_2312, plain, (![A_320]: (r1_tarski(A_320, k2_zfmisc_1(k1_relat_1(A_320), k2_relat_1(A_320))) | ~v1_relat_1(A_320))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.18/1.68  tff(c_12, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.18/1.68  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.18/1.68  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.18/1.68  tff(c_16, plain, (![A_8]: (r1_tarski(A_8, k2_zfmisc_1(k1_relat_1(A_8), k2_relat_1(A_8))) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.18/1.68  tff(c_802, plain, (![A_188, B_189, C_190]: (k1_relset_1(A_188, B_189, C_190)=k1_relat_1(C_190) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.18/1.68  tff(c_1104, plain, (![A_225, B_226, A_227]: (k1_relset_1(A_225, B_226, A_227)=k1_relat_1(A_227) | ~r1_tarski(A_227, k2_zfmisc_1(A_225, B_226)))), inference(resolution, [status(thm)], [c_12, c_802])).
% 4.18/1.68  tff(c_1120, plain, (![A_8]: (k1_relset_1(k1_relat_1(A_8), k2_relat_1(A_8), A_8)=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_16, c_1104])).
% 4.18/1.68  tff(c_995, plain, (![B_210, C_211, A_212]: (k1_xboole_0=B_210 | v1_funct_2(C_211, A_212, B_210) | k1_relset_1(A_212, B_210, C_211)!=A_212 | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_212, B_210))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.18/1.68  tff(c_1643, plain, (![B_279, A_280, A_281]: (k1_xboole_0=B_279 | v1_funct_2(A_280, A_281, B_279) | k1_relset_1(A_281, B_279, A_280)!=A_281 | ~r1_tarski(A_280, k2_zfmisc_1(A_281, B_279)))), inference(resolution, [status(thm)], [c_12, c_995])).
% 4.18/1.68  tff(c_2026, plain, (![A_306]: (k2_relat_1(A_306)=k1_xboole_0 | v1_funct_2(A_306, k1_relat_1(A_306), k2_relat_1(A_306)) | k1_relset_1(k1_relat_1(A_306), k2_relat_1(A_306), A_306)!=k1_relat_1(A_306) | ~v1_relat_1(A_306))), inference(resolution, [status(thm)], [c_16, c_1643])).
% 4.18/1.68  tff(c_42, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.18/1.68  tff(c_40, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.18/1.68  tff(c_46, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40])).
% 4.18/1.68  tff(c_91, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_46])).
% 4.18/1.68  tff(c_2033, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2026, c_91])).
% 4.18/1.68  tff(c_2045, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2033])).
% 4.18/1.68  tff(c_2048, plain, (k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_2045])).
% 4.18/1.68  tff(c_2054, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1120, c_2048])).
% 4.18/1.68  tff(c_2060, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_2054])).
% 4.18/1.68  tff(c_2061, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2045])).
% 4.18/1.68  tff(c_22, plain, (![A_15]: (r2_hidden('#skF_1'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.18/1.68  tff(c_93, plain, (![C_42, B_43, A_44]: (~v1_xboole_0(C_42) | ~m1_subset_1(B_43, k1_zfmisc_1(C_42)) | ~r2_hidden(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.18/1.68  tff(c_97, plain, (![B_45, A_46, A_47]: (~v1_xboole_0(B_45) | ~r2_hidden(A_46, A_47) | ~r1_tarski(A_47, B_45))), inference(resolution, [status(thm)], [c_12, c_93])).
% 4.18/1.68  tff(c_101, plain, (![B_48, A_49]: (~v1_xboole_0(B_48) | ~r1_tarski(A_49, B_48) | k1_xboole_0=A_49)), inference(resolution, [status(thm)], [c_22, c_97])).
% 4.18/1.68  tff(c_105, plain, (![A_8]: (~v1_xboole_0(k2_zfmisc_1(k1_relat_1(A_8), k2_relat_1(A_8))) | k1_xboole_0=A_8 | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_16, c_101])).
% 4.18/1.68  tff(c_2076, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_2'), k1_xboole_0)) | k1_xboole_0='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2061, c_105])).
% 4.18/1.68  tff(c_2089, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2, c_6, c_2076])).
% 4.18/1.68  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.18/1.68  tff(c_151, plain, (![A_78, B_79, C_80]: (m1_subset_1(k1_relset_1(A_78, B_79, C_80), k1_zfmisc_1(A_78)) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.18/1.68  tff(c_10, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.18/1.68  tff(c_209, plain, (![A_89, B_90, C_91]: (r1_tarski(k1_relset_1(A_89, B_90, C_91), A_89) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(resolution, [status(thm)], [c_151, c_10])).
% 4.18/1.68  tff(c_219, plain, (![B_2, C_91]: (r1_tarski(k1_relset_1(k1_xboole_0, B_2, C_91), k1_xboole_0) | ~m1_subset_1(C_91, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_209])).
% 4.18/1.68  tff(c_221, plain, (![A_89, B_90, A_3]: (r1_tarski(k1_relset_1(A_89, B_90, A_3), A_89) | ~r1_tarski(A_3, k2_zfmisc_1(A_89, B_90)))), inference(resolution, [status(thm)], [c_12, c_209])).
% 4.18/1.68  tff(c_28, plain, (![A_29]: (v1_funct_2(k1_xboole_0, A_29, k1_xboole_0) | k1_xboole_0=A_29 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_29, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.18/1.68  tff(c_49, plain, (![A_29]: (v1_funct_2(k1_xboole_0, A_29, k1_xboole_0) | k1_xboole_0=A_29 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_28])).
% 4.18/1.68  tff(c_106, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_49])).
% 4.18/1.68  tff(c_110, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_106])).
% 4.18/1.68  tff(c_293, plain, (![A_105, B_106, A_107]: (r1_tarski(k1_relset_1(A_105, B_106, A_107), A_105) | ~r1_tarski(A_107, k2_zfmisc_1(A_105, B_106)))), inference(resolution, [status(thm)], [c_12, c_209])).
% 4.18/1.68  tff(c_244, plain, (![B_96, C_97]: (r1_tarski(k1_relset_1(k1_xboole_0, B_96, C_97), k1_xboole_0) | ~m1_subset_1(C_97, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_209])).
% 4.18/1.68  tff(c_100, plain, (![B_45, A_15]: (~v1_xboole_0(B_45) | ~r1_tarski(A_15, B_45) | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_22, c_97])).
% 4.18/1.68  tff(c_251, plain, (![B_96, C_97]: (~v1_xboole_0(k1_xboole_0) | k1_relset_1(k1_xboole_0, B_96, C_97)=k1_xboole_0 | ~m1_subset_1(C_97, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_244, c_100])).
% 4.18/1.68  tff(c_257, plain, (![B_98, C_99]: (k1_relset_1(k1_xboole_0, B_98, C_99)=k1_xboole_0 | ~m1_subset_1(C_99, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_251])).
% 4.18/1.68  tff(c_266, plain, (![B_98, A_3]: (k1_relset_1(k1_xboole_0, B_98, A_3)=k1_xboole_0 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_257])).
% 4.18/1.68  tff(c_296, plain, (![B_98, B_106, A_107]: (k1_relset_1(k1_xboole_0, B_98, k1_relset_1(k1_xboole_0, B_106, A_107))=k1_xboole_0 | ~r1_tarski(A_107, k2_zfmisc_1(k1_xboole_0, B_106)))), inference(resolution, [status(thm)], [c_293, c_266])).
% 4.18/1.68  tff(c_325, plain, (![B_110, B_111, A_112]: (k1_relset_1(k1_xboole_0, B_110, k1_relset_1(k1_xboole_0, B_111, A_112))=k1_xboole_0 | ~r1_tarski(A_112, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_296])).
% 4.18/1.68  tff(c_334, plain, (![B_111, A_112, B_110]: (r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_relset_1(k1_xboole_0, B_111, A_112), k2_zfmisc_1(k1_xboole_0, B_110)) | ~r1_tarski(A_112, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_325, c_221])).
% 4.18/1.68  tff(c_352, plain, (![B_111, A_112]: (r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_relset_1(k1_xboole_0, B_111, A_112), k1_xboole_0) | ~r1_tarski(A_112, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_334])).
% 4.18/1.68  tff(c_359, plain, (![B_113, A_114]: (~r1_tarski(k1_relset_1(k1_xboole_0, B_113, A_114), k1_xboole_0) | ~r1_tarski(A_114, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_110, c_352])).
% 4.18/1.68  tff(c_366, plain, (![A_3, B_90]: (~r1_tarski(A_3, k1_xboole_0) | ~r1_tarski(A_3, k2_zfmisc_1(k1_xboole_0, B_90)))), inference(resolution, [status(thm)], [c_221, c_359])).
% 4.18/1.68  tff(c_396, plain, (![A_118]: (~r1_tarski(A_118, k1_xboole_0) | ~r1_tarski(A_118, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_366])).
% 4.18/1.68  tff(c_446, plain, (![B_126, C_127]: (~r1_tarski(k1_relset_1(k1_xboole_0, B_126, C_127), k1_xboole_0) | ~m1_subset_1(C_127, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_219, c_396])).
% 4.18/1.68  tff(c_465, plain, (![C_128]: (~m1_subset_1(C_128, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_219, c_446])).
% 4.18/1.68  tff(c_476, plain, (![A_3]: (~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_465])).
% 4.18/1.68  tff(c_123, plain, (![A_67, B_68, C_69]: (k1_relset_1(A_67, B_68, C_69)=k1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.18/1.68  tff(c_180, plain, (![A_83, B_84, A_85]: (k1_relset_1(A_83, B_84, A_85)=k1_relat_1(A_85) | ~r1_tarski(A_85, k2_zfmisc_1(A_83, B_84)))), inference(resolution, [status(thm)], [c_12, c_123])).
% 4.18/1.68  tff(c_190, plain, (![A_8]: (k1_relset_1(k1_relat_1(A_8), k2_relat_1(A_8), A_8)=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_16, c_180])).
% 4.18/1.68  tff(c_267, plain, (![B_100, C_101, A_102]: (k1_xboole_0=B_100 | v1_funct_2(C_101, A_102, B_100) | k1_relset_1(A_102, B_100, C_101)!=A_102 | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_100))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.18/1.68  tff(c_561, plain, (![B_140, A_141, A_142]: (k1_xboole_0=B_140 | v1_funct_2(A_141, A_142, B_140) | k1_relset_1(A_142, B_140, A_141)!=A_142 | ~r1_tarski(A_141, k2_zfmisc_1(A_142, B_140)))), inference(resolution, [status(thm)], [c_12, c_267])).
% 4.18/1.68  tff(c_722, plain, (![A_170]: (k2_relat_1(A_170)=k1_xboole_0 | v1_funct_2(A_170, k1_relat_1(A_170), k2_relat_1(A_170)) | k1_relset_1(k1_relat_1(A_170), k2_relat_1(A_170), A_170)!=k1_relat_1(A_170) | ~v1_relat_1(A_170))), inference(resolution, [status(thm)], [c_16, c_561])).
% 4.18/1.68  tff(c_725, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_722, c_91])).
% 4.18/1.68  tff(c_728, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_725])).
% 4.18/1.68  tff(c_729, plain, (k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_728])).
% 4.18/1.68  tff(c_732, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_190, c_729])).
% 4.18/1.68  tff(c_736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_732])).
% 4.18/1.68  tff(c_737, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_728])).
% 4.18/1.68  tff(c_752, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), k1_xboole_0)) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_737, c_16])).
% 4.18/1.68  tff(c_762, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6, c_752])).
% 4.18/1.68  tff(c_764, plain, $false, inference(negUnitSimplification, [status(thm)], [c_476, c_762])).
% 4.18/1.68  tff(c_766, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_49])).
% 4.18/1.68  tff(c_814, plain, (![A_191, C_192]: (k1_relset_1(A_191, k1_xboole_0, C_192)=k1_relat_1(C_192) | ~m1_subset_1(C_192, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_802])).
% 4.18/1.68  tff(c_820, plain, (![A_191]: (k1_relset_1(A_191, k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_766, c_814])).
% 4.18/1.68  tff(c_849, plain, (![A_200, B_201, C_202]: (m1_subset_1(k1_relset_1(A_200, B_201, C_202), k1_zfmisc_1(A_200)) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.18/1.68  tff(c_867, plain, (![A_191]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_191)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_191, k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_820, c_849])).
% 4.18/1.68  tff(c_877, plain, (![A_203]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_203)))), inference(demodulation, [status(thm), theory('equality')], [c_766, c_6, c_867])).
% 4.18/1.68  tff(c_898, plain, (![A_204]: (r1_tarski(k1_relat_1(k1_xboole_0), A_204))), inference(resolution, [status(thm)], [c_877, c_10])).
% 4.18/1.68  tff(c_906, plain, (![A_204]: (~v1_xboole_0(A_204) | k1_relat_1(k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_898, c_100])).
% 4.18/1.68  tff(c_907, plain, (![A_204]: (~v1_xboole_0(A_204))), inference(splitLeft, [status(thm)], [c_906])).
% 4.18/1.68  tff(c_909, plain, $false, inference(negUnitSimplification, [status(thm)], [c_907, c_2])).
% 4.18/1.68  tff(c_910, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_906])).
% 4.18/1.68  tff(c_876, plain, (![A_191]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_191)))), inference(demodulation, [status(thm), theory('equality')], [c_766, c_6, c_867])).
% 4.18/1.68  tff(c_954, plain, (![A_208]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_208)))), inference(demodulation, [status(thm), theory('equality')], [c_910, c_876])).
% 4.18/1.68  tff(c_20, plain, (![A_12, B_13, C_14]: (k1_relset_1(A_12, B_13, C_14)=k1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.18/1.68  tff(c_967, plain, (![A_12, B_13]: (k1_relset_1(A_12, B_13, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_954, c_20])).
% 4.18/1.68  tff(c_979, plain, (![A_12, B_13]: (k1_relset_1(A_12, B_13, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_910, c_967])).
% 4.18/1.68  tff(c_32, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_30))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.18/1.68  tff(c_928, plain, (![C_205, B_206]: (v1_funct_2(C_205, k1_xboole_0, B_206) | k1_relset_1(k1_xboole_0, B_206, C_205)!=k1_xboole_0 | ~m1_subset_1(C_205, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_32])).
% 4.18/1.68  tff(c_939, plain, (![B_206]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_206) | k1_relset_1(k1_xboole_0, B_206, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_766, c_928])).
% 4.18/1.68  tff(c_1079, plain, (![B_206]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_206))), inference(demodulation, [status(thm), theory('equality')], [c_979, c_939])).
% 4.18/1.68  tff(c_2120, plain, (![B_206]: (v1_funct_2('#skF_2', '#skF_2', B_206))), inference(demodulation, [status(thm), theory('equality')], [c_2089, c_2089, c_1079])).
% 4.18/1.68  tff(c_2128, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2089, c_2089, c_910])).
% 4.18/1.68  tff(c_2063, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2061, c_91])).
% 4.18/1.68  tff(c_2175, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2089, c_2063])).
% 4.18/1.68  tff(c_2183, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_2175])).
% 4.18/1.68  tff(c_2305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2120, c_2183])).
% 4.18/1.68  tff(c_2306, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_46])).
% 4.18/1.68  tff(c_2311, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_2306])).
% 4.18/1.68  tff(c_2315, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2312, c_2311])).
% 4.18/1.68  tff(c_2319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_2315])).
% 4.18/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.18/1.68  
% 4.18/1.68  Inference rules
% 4.18/1.68  ----------------------
% 4.18/1.68  #Ref     : 0
% 4.18/1.68  #Sup     : 487
% 4.18/1.68  #Fact    : 0
% 4.18/1.68  #Define  : 0
% 4.18/1.68  #Split   : 6
% 4.18/1.68  #Chain   : 0
% 4.18/1.68  #Close   : 0
% 4.18/1.68  
% 4.18/1.68  Ordering : KBO
% 4.18/1.68  
% 4.18/1.68  Simplification rules
% 4.18/1.68  ----------------------
% 4.18/1.68  #Subsume      : 143
% 4.18/1.68  #Demod        : 472
% 4.18/1.68  #Tautology    : 172
% 4.18/1.68  #SimpNegUnit  : 7
% 4.18/1.68  #BackRed      : 61
% 4.18/1.68  
% 4.18/1.68  #Partial instantiations: 0
% 4.18/1.68  #Strategies tried      : 1
% 4.18/1.68  
% 4.18/1.68  Timing (in seconds)
% 4.18/1.68  ----------------------
% 4.18/1.69  Preprocessing        : 0.31
% 4.18/1.69  Parsing              : 0.16
% 4.18/1.69  CNF conversion       : 0.02
% 4.18/1.69  Main loop            : 0.60
% 4.18/1.69  Inferencing          : 0.22
% 4.18/1.69  Reduction            : 0.18
% 4.18/1.69  Demodulation         : 0.12
% 4.18/1.69  BG Simplification    : 0.03
% 4.18/1.69  Subsumption          : 0.12
% 4.18/1.69  Abstraction          : 0.04
% 4.18/1.69  MUC search           : 0.00
% 4.18/1.69  Cooper               : 0.00
% 4.18/1.69  Total                : 0.95
% 4.18/1.69  Index Insertion      : 0.00
% 4.18/1.69  Index Deletion       : 0.00
% 4.18/1.69  Index Matching       : 0.00
% 4.18/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
