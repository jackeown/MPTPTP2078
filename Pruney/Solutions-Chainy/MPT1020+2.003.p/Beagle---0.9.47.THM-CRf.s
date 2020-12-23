%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:50 EST 2020

% Result     : Theorem 8.15s
% Output     : CNFRefutation 8.52s
% Verified   : 
% Statistics : Number of formulae       :  400 (19891 expanded)
%              Number of leaves         :   56 (6769 expanded)
%              Depth                    :   20
%              Number of atoms          :  782 (63202 expanded)
%              Number of equality atoms :  238 (10884 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_118,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_216,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_138,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_194,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( ( k2_relset_1(A,B,C) = B
              & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
              & v2_funct_1(C) )
           => ( A = k1_xboole_0
              | B = k1_xboole_0
              | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_150,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_68,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_148,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_74,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_170,plain,(
    ! [A_83,B_84] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_83,B_84)),B_84) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_173,plain,(
    ! [B_4] : r1_tarski(k2_relat_1(k1_xboole_0),B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_170])).

tff(c_165,plain,(
    ! [A_82] :
      ( r2_hidden('#skF_1'(A_82),A_82)
      | k1_xboole_0 = A_82 ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_32,plain,(
    ! [B_21,A_20] :
      ( ~ r1_tarski(B_21,A_20)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_189,plain,(
    ! [A_89] :
      ( ~ r1_tarski(A_89,'#skF_1'(A_89))
      | k1_xboole_0 = A_89 ) ),
    inference(resolution,[status(thm)],[c_165,c_32])).

tff(c_194,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_173,c_189])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_94,plain,(
    ! [A_75] :
      ( v1_relat_1(A_75)
      | ~ v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_98,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_94])).

tff(c_207,plain,(
    ! [A_91,B_92] :
      ( v1_xboole_0(k7_relat_1(A_91,B_92))
      | ~ v1_relat_1(A_91)
      | ~ v1_xboole_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_179,plain,(
    ! [B_86,A_87] :
      ( ~ v1_xboole_0(B_86)
      | B_86 = A_87
      | ~ v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_182,plain,(
    ! [A_87] :
      ( k1_xboole_0 = A_87
      | ~ v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_2,c_179])).

tff(c_253,plain,(
    ! [A_101,B_102] :
      ( k7_relat_1(A_101,B_102) = k1_xboole_0
      | ~ v1_relat_1(A_101)
      | ~ v1_xboole_0(A_101) ) ),
    inference(resolution,[status(thm)],[c_207,c_182])).

tff(c_257,plain,(
    ! [B_102] :
      ( k7_relat_1(k1_xboole_0,B_102) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_253])).

tff(c_261,plain,(
    ! [B_102] : k7_relat_1(k1_xboole_0,B_102) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_257])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_1439,plain,(
    ! [A_275,B_276,D_277] :
      ( r2_relset_1(A_275,B_276,D_277,D_277)
      | ~ m1_subset_1(D_277,k1_zfmisc_1(k2_zfmisc_1(A_275,B_276))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1449,plain,(
    r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_1439])).

tff(c_86,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_84,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_76,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_20,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_231,plain,(
    ! [B_97,A_98] :
      ( v1_relat_1(B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_98))
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_234,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_80,c_231])).

tff(c_240,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_234])).

tff(c_291,plain,(
    ! [C_105,B_106,A_107] :
      ( v5_relat_1(C_105,B_106)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_107,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_304,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_291])).

tff(c_1450,plain,(
    ! [B_278,A_279] :
      ( k2_relat_1(B_278) = A_279
      | ~ v2_funct_2(B_278,A_279)
      | ~ v5_relat_1(B_278,A_279)
      | ~ v1_relat_1(B_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1459,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_304,c_1450])).

tff(c_1468,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_1459])).

tff(c_1627,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1468])).

tff(c_82,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_1673,plain,(
    ! [C_324,B_325,A_326] :
      ( v2_funct_2(C_324,B_325)
      | ~ v3_funct_2(C_324,A_326,B_325)
      | ~ v1_funct_1(C_324)
      | ~ m1_subset_1(C_324,k1_zfmisc_1(k2_zfmisc_1(A_326,B_325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1676,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_1673])).

tff(c_1688,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_1676])).

tff(c_1690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1627,c_1688])).

tff(c_1691,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1468])).

tff(c_1705,plain,(
    ! [A_331,B_332,C_333] :
      ( k2_relset_1(A_331,B_332,C_333) = k2_relat_1(C_333)
      | ~ m1_subset_1(C_333,k1_zfmisc_1(k2_zfmisc_1(A_331,B_332))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1708,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_1705])).

tff(c_1719,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1691,c_1708])).

tff(c_1731,plain,(
    ! [C_336,A_337,B_338] :
      ( v2_funct_1(C_336)
      | ~ v3_funct_2(C_336,A_337,B_338)
      | ~ v1_funct_1(C_336)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_337,B_338))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1734,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_1731])).

tff(c_1746,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_1734])).

tff(c_70,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_8432,plain,(
    ! [C_853,D_854,B_855,A_856] :
      ( k2_funct_1(C_853) = D_854
      | k1_xboole_0 = B_855
      | k1_xboole_0 = A_856
      | ~ v2_funct_1(C_853)
      | ~ r2_relset_1(A_856,A_856,k1_partfun1(A_856,B_855,B_855,A_856,C_853,D_854),k6_partfun1(A_856))
      | k2_relset_1(A_856,B_855,C_853) != B_855
      | ~ m1_subset_1(D_854,k1_zfmisc_1(k2_zfmisc_1(B_855,A_856)))
      | ~ v1_funct_2(D_854,B_855,A_856)
      | ~ v1_funct_1(D_854)
      | ~ m1_subset_1(C_853,k1_zfmisc_1(k2_zfmisc_1(A_856,B_855)))
      | ~ v1_funct_2(C_853,A_856,B_855)
      | ~ v1_funct_1(C_853) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_8435,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_8432])).

tff(c_8441,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_78,c_76,c_72,c_1719,c_1746,c_8435])).

tff(c_8444,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_8441])).

tff(c_8480,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8444,c_2])).

tff(c_99,plain,(
    ! [A_76] : k6_relat_1(A_76) = k6_partfun1(A_76) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_26,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_105,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_26])).

tff(c_8477,plain,(
    k6_partfun1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8444,c_8444,c_105])).

tff(c_8475,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8444,c_8444,c_10])).

tff(c_2518,plain,(
    ! [C_450,D_451,B_452,A_453] :
      ( k2_funct_1(C_450) = D_451
      | k1_xboole_0 = B_452
      | k1_xboole_0 = A_453
      | ~ v2_funct_1(C_450)
      | ~ r2_relset_1(A_453,A_453,k1_partfun1(A_453,B_452,B_452,A_453,C_450,D_451),k6_partfun1(A_453))
      | k2_relset_1(A_453,B_452,C_450) != B_452
      | ~ m1_subset_1(D_451,k1_zfmisc_1(k2_zfmisc_1(B_452,A_453)))
      | ~ v1_funct_2(D_451,B_452,A_453)
      | ~ v1_funct_1(D_451)
      | ~ m1_subset_1(C_450,k1_zfmisc_1(k2_zfmisc_1(A_453,B_452)))
      | ~ v1_funct_2(C_450,A_453,B_452)
      | ~ v1_funct_1(C_450) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_2521,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_2518])).

tff(c_2527,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_78,c_76,c_72,c_1719,c_1746,c_2521])).

tff(c_2530,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2527])).

tff(c_2564,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2530,c_98])).

tff(c_2563,plain,(
    k6_partfun1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2530,c_2530,c_105])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2562,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2530,c_2530,c_8])).

tff(c_60,plain,(
    ! [A_61] : k6_relat_1(A_61) = k6_partfun1(A_61) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( k9_relat_1(k6_relat_1(A_17),B_18) = B_18
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1412,plain,(
    ! [A_265,B_266] :
      ( k9_relat_1(k6_partfun1(A_265),B_266) = B_266
      | ~ m1_subset_1(B_266,k1_zfmisc_1(A_265)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_28])).

tff(c_1420,plain,(
    k9_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_72,c_1412])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( k2_relat_1(k7_relat_1(B_14,A_13)) = k9_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_321,plain,(
    ! [B_111] :
      ( v2_funct_2(B_111,k2_relat_1(B_111))
      | ~ v5_relat_1(B_111,k2_relat_1(B_111))
      | ~ v1_relat_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1929,plain,(
    ! [B_391,A_392] :
      ( v2_funct_2(k7_relat_1(B_391,A_392),k2_relat_1(k7_relat_1(B_391,A_392)))
      | ~ v5_relat_1(k7_relat_1(B_391,A_392),k9_relat_1(B_391,A_392))
      | ~ v1_relat_1(k7_relat_1(B_391,A_392))
      | ~ v1_relat_1(B_391) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_321])).

tff(c_1955,plain,(
    ! [B_398,A_399] :
      ( v2_funct_2(k7_relat_1(B_398,A_399),k9_relat_1(B_398,A_399))
      | ~ v5_relat_1(k7_relat_1(B_398,A_399),k9_relat_1(B_398,A_399))
      | ~ v1_relat_1(k7_relat_1(B_398,A_399))
      | ~ v1_relat_1(B_398)
      | ~ v1_relat_1(B_398) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1929])).

tff(c_1964,plain,
    ( v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'),k9_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'))
    | ~ v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'))
    | ~ v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_1955])).

tff(c_1974,plain,
    ( v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'),'#skF_4')
    | ~ v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'))
    | ~ v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1420,c_1964])).

tff(c_1980,plain,(
    ~ v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1974])).

tff(c_2645,plain,(
    ~ v1_relat_1(k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2562,c_1980])).

tff(c_2653,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2564,c_2563,c_2645])).

tff(c_2654,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2527])).

tff(c_1883,plain,(
    ! [A_377,B_378] :
      ( k2_funct_2(A_377,B_378) = k2_funct_1(B_378)
      | ~ m1_subset_1(B_378,k1_zfmisc_1(k2_zfmisc_1(A_377,A_377)))
      | ~ v3_funct_2(B_378,A_377,A_377)
      | ~ v1_funct_2(B_378,A_377,A_377)
      | ~ v1_funct_1(B_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1886,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_1883])).

tff(c_1900,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_1886])).

tff(c_68,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_1904,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1900,c_68])).

tff(c_2656,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2654,c_1904])).

tff(c_2660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1449,c_2656])).

tff(c_2662,plain,(
    v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1974])).

tff(c_3212,plain,(
    ! [C_505,D_506,B_507,A_508] :
      ( k2_funct_1(C_505) = D_506
      | k1_xboole_0 = B_507
      | k1_xboole_0 = A_508
      | ~ v2_funct_1(C_505)
      | ~ r2_relset_1(A_508,A_508,k1_partfun1(A_508,B_507,B_507,A_508,C_505,D_506),k6_partfun1(A_508))
      | k2_relset_1(A_508,B_507,C_505) != B_507
      | ~ m1_subset_1(D_506,k1_zfmisc_1(k2_zfmisc_1(B_507,A_508)))
      | ~ v1_funct_2(D_506,B_507,A_508)
      | ~ v1_funct_1(D_506)
      | ~ m1_subset_1(C_505,k1_zfmisc_1(k2_zfmisc_1(A_508,B_507)))
      | ~ v1_funct_2(C_505,A_508,B_507)
      | ~ v1_funct_1(C_505) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_3215,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_3212])).

tff(c_3221,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_78,c_76,c_72,c_1719,c_1746,c_3215])).

tff(c_3224,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3221])).

tff(c_3260,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3224,c_2])).

tff(c_3257,plain,(
    k6_partfun1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3224,c_3224,c_105])).

tff(c_3256,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3224,c_3224,c_8])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k7_relat_1(A_9,B_10))
      | ~ v1_relat_1(A_9)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1419,plain,(
    k9_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_80,c_1412])).

tff(c_1967,plain,
    ( v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3'),k9_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3'))
    | ~ v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3'))
    | ~ v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1419,c_1955])).

tff(c_1975,plain,
    ( v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3'),'#skF_3')
    | ~ v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3'))
    | ~ v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1419,c_1967])).

tff(c_2676,plain,
    ( v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3'),'#skF_3')
    | ~ v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2662,c_2662,c_1975])).

tff(c_2677,plain,(
    ~ v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2676])).

tff(c_2680,plain,
    ( ~ v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_16,c_2677])).

tff(c_2683,plain,(
    ~ v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2662,c_2680])).

tff(c_3341,plain,(
    ~ v1_xboole_0(k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3256,c_2683])).

tff(c_3352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3260,c_3257,c_3341])).

tff(c_3353,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3221])).

tff(c_3355,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3353,c_1904])).

tff(c_3359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1449,c_3355])).

tff(c_3361,plain,(
    v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2676])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( v1_xboole_0(k7_relat_1(A_9,B_10))
      | ~ v1_relat_1(A_9)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1432,plain,(
    ! [A_272,B_273,A_274] :
      ( k7_relat_1(A_272,B_273) = A_274
      | ~ v1_xboole_0(A_274)
      | ~ v1_relat_1(A_272)
      | ~ v1_xboole_0(A_272) ) ),
    inference(resolution,[status(thm)],[c_207,c_4])).

tff(c_1774,plain,(
    ! [A_354,B_355,A_352,B_353] :
      ( k7_relat_1(A_354,B_355) = k7_relat_1(A_352,B_353)
      | ~ v1_relat_1(A_354)
      | ~ v1_xboole_0(A_354)
      | ~ v1_relat_1(A_352)
      | ~ v1_xboole_0(A_352) ) ),
    inference(resolution,[status(thm)],[c_18,c_1432])).

tff(c_1871,plain,(
    ! [B_374,A_372,A_376,B_375,B_373] :
      ( k7_relat_1(k7_relat_1(A_376,B_374),B_373) = k7_relat_1(A_372,B_375)
      | ~ v1_relat_1(k7_relat_1(A_376,B_374))
      | ~ v1_relat_1(A_372)
      | ~ v1_xboole_0(A_372)
      | ~ v1_relat_1(A_376)
      | ~ v1_xboole_0(A_376) ) ),
    inference(resolution,[status(thm)],[c_18,c_1774])).

tff(c_1914,plain,(
    ! [A_380,B_379,A_383,B_381,B_382] :
      ( k7_relat_1(k7_relat_1(A_383,B_382),B_381) = k7_relat_1(A_380,B_379)
      | ~ v1_relat_1(A_380)
      | ~ v1_xboole_0(A_380)
      | ~ v1_relat_1(A_383)
      | ~ v1_xboole_0(A_383) ) ),
    inference(resolution,[status(thm)],[c_16,c_1871])).

tff(c_1919,plain,(
    ! [B_379,A_383,B_381,B_10,B_382,A_9] :
      ( k7_relat_1(k7_relat_1(A_9,B_10),B_379) = k7_relat_1(k7_relat_1(A_383,B_382),B_381)
      | ~ v1_relat_1(k7_relat_1(A_9,B_10))
      | ~ v1_relat_1(A_383)
      | ~ v1_xboole_0(A_383)
      | ~ v1_relat_1(A_9)
      | ~ v1_xboole_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_1914])).

tff(c_3363,plain,(
    ! [B_379,A_383,B_382,B_381] :
      ( k7_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3'),B_379) = k7_relat_1(k7_relat_1(A_383,B_382),B_381)
      | ~ v1_relat_1(A_383)
      | ~ v1_xboole_0(A_383)
      | ~ v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_3361,c_1919])).

tff(c_3366,plain,(
    ! [B_379,A_383,B_382,B_381] :
      ( k7_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3'),B_379) = k7_relat_1(k7_relat_1(A_383,B_382),B_381)
      | ~ v1_relat_1(A_383)
      | ~ v1_xboole_0(A_383)
      | ~ v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2662,c_3363])).

tff(c_8019,plain,(
    ~ v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3366])).

tff(c_8549,plain,(
    ~ v1_xboole_0(k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8475,c_8019])).

tff(c_8566,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8480,c_8477,c_8549])).

tff(c_8567,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8441])).

tff(c_8569,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8567,c_1904])).

tff(c_8573,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1449,c_8569])).

tff(c_8575,plain,(
    v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3366])).

tff(c_8602,plain,(
    k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8575,c_182])).

tff(c_7746,plain,(
    ! [C_802,D_803,B_804,A_805] :
      ( k2_funct_1(C_802) = D_803
      | k1_xboole_0 = B_804
      | k1_xboole_0 = A_805
      | ~ v2_funct_1(C_802)
      | ~ r2_relset_1(A_805,A_805,k1_partfun1(A_805,B_804,B_804,A_805,C_802,D_803),k6_partfun1(A_805))
      | k2_relset_1(A_805,B_804,C_802) != B_804
      | ~ m1_subset_1(D_803,k1_zfmisc_1(k2_zfmisc_1(B_804,A_805)))
      | ~ v1_funct_2(D_803,B_804,A_805)
      | ~ v1_funct_1(D_803)
      | ~ m1_subset_1(C_802,k1_zfmisc_1(k2_zfmisc_1(A_805,B_804)))
      | ~ v1_funct_2(C_802,A_805,B_804)
      | ~ v1_funct_1(C_802) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_7749,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_7746])).

tff(c_7755,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_78,c_76,c_72,c_1719,c_1746,c_7749])).

tff(c_7758,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7755])).

tff(c_7794,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7758,c_2])).

tff(c_7791,plain,(
    k6_partfun1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7758,c_7758,c_105])).

tff(c_7790,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7758,c_7758,c_8])).

tff(c_6524,plain,(
    ! [C_730,D_731,B_732,A_733] :
      ( k2_funct_1(C_730) = D_731
      | k1_xboole_0 = B_732
      | k1_xboole_0 = A_733
      | ~ v2_funct_1(C_730)
      | ~ r2_relset_1(A_733,A_733,k1_partfun1(A_733,B_732,B_732,A_733,C_730,D_731),k6_partfun1(A_733))
      | k2_relset_1(A_733,B_732,C_730) != B_732
      | ~ m1_subset_1(D_731,k1_zfmisc_1(k2_zfmisc_1(B_732,A_733)))
      | ~ v1_funct_2(D_731,B_732,A_733)
      | ~ v1_funct_1(D_731)
      | ~ m1_subset_1(C_730,k1_zfmisc_1(k2_zfmisc_1(A_733,B_732)))
      | ~ v1_funct_2(C_730,A_733,B_732)
      | ~ v1_funct_1(C_730) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_6527,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_6524])).

tff(c_6533,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_78,c_76,c_72,c_1719,c_1746,c_6527])).

tff(c_6536,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_6533])).

tff(c_6571,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6536,c_2])).

tff(c_6568,plain,(
    k6_partfun1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6536,c_6536,c_105])).

tff(c_6567,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6536,c_6536,c_8])).

tff(c_6342,plain,(
    ~ v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3366])).

tff(c_6665,plain,(
    ~ v1_xboole_0(k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6567,c_6342])).

tff(c_6679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6571,c_6568,c_6665])).

tff(c_6680,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6533])).

tff(c_6682,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6680,c_1904])).

tff(c_6686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1449,c_6682])).

tff(c_6688,plain,(
    v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3366])).

tff(c_6715,plain,(
    k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6688,c_182])).

tff(c_5652,plain,(
    ! [C_673,D_674,B_675,A_676] :
      ( k2_funct_1(C_673) = D_674
      | k1_xboole_0 = B_675
      | k1_xboole_0 = A_676
      | ~ v2_funct_1(C_673)
      | ~ r2_relset_1(A_676,A_676,k1_partfun1(A_676,B_675,B_675,A_676,C_673,D_674),k6_partfun1(A_676))
      | k2_relset_1(A_676,B_675,C_673) != B_675
      | ~ m1_subset_1(D_674,k1_zfmisc_1(k2_zfmisc_1(B_675,A_676)))
      | ~ v1_funct_2(D_674,B_675,A_676)
      | ~ v1_funct_1(D_674)
      | ~ m1_subset_1(C_673,k1_zfmisc_1(k2_zfmisc_1(A_676,B_675)))
      | ~ v1_funct_2(C_673,A_676,B_675)
      | ~ v1_funct_1(C_673) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_5655,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_5652])).

tff(c_5661,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_78,c_76,c_72,c_1719,c_1746,c_5655])).

tff(c_5664,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5661])).

tff(c_5700,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5664,c_2])).

tff(c_5697,plain,(
    k6_partfun1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5664,c_5664,c_105])).

tff(c_5695,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5664,c_5664,c_10])).

tff(c_5239,plain,(
    ~ v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3366])).

tff(c_5769,plain,(
    ~ v1_xboole_0(k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5695,c_5239])).

tff(c_5784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5700,c_5697,c_5769])).

tff(c_5785,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5661])).

tff(c_5787,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5785,c_1904])).

tff(c_5791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1449,c_5787])).

tff(c_5793,plain,(
    v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3366])).

tff(c_5820,plain,(
    k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5793,c_182])).

tff(c_4968,plain,(
    ! [C_622,D_623,B_624,A_625] :
      ( k2_funct_1(C_622) = D_623
      | k1_xboole_0 = B_624
      | k1_xboole_0 = A_625
      | ~ v2_funct_1(C_622)
      | ~ r2_relset_1(A_625,A_625,k1_partfun1(A_625,B_624,B_624,A_625,C_622,D_623),k6_partfun1(A_625))
      | k2_relset_1(A_625,B_624,C_622) != B_624
      | ~ m1_subset_1(D_623,k1_zfmisc_1(k2_zfmisc_1(B_624,A_625)))
      | ~ v1_funct_2(D_623,B_624,A_625)
      | ~ v1_funct_1(D_623)
      | ~ m1_subset_1(C_622,k1_zfmisc_1(k2_zfmisc_1(A_625,B_624)))
      | ~ v1_funct_2(C_622,A_625,B_624)
      | ~ v1_funct_1(C_622) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_4971,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_4968])).

tff(c_4977,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_78,c_76,c_72,c_1719,c_1746,c_4971])).

tff(c_4980,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4977])).

tff(c_5016,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4980,c_2])).

tff(c_5013,plain,(
    k6_partfun1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4980,c_4980,c_105])).

tff(c_5011,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4980,c_4980,c_10])).

tff(c_3854,plain,(
    ! [C_554,D_555,B_556,A_557] :
      ( k2_funct_1(C_554) = D_555
      | k1_xboole_0 = B_556
      | k1_xboole_0 = A_557
      | ~ v2_funct_1(C_554)
      | ~ r2_relset_1(A_557,A_557,k1_partfun1(A_557,B_556,B_556,A_557,C_554,D_555),k6_partfun1(A_557))
      | k2_relset_1(A_557,B_556,C_554) != B_556
      | ~ m1_subset_1(D_555,k1_zfmisc_1(k2_zfmisc_1(B_556,A_557)))
      | ~ v1_funct_2(D_555,B_556,A_557)
      | ~ v1_funct_1(D_555)
      | ~ m1_subset_1(C_554,k1_zfmisc_1(k2_zfmisc_1(A_557,B_556)))
      | ~ v1_funct_2(C_554,A_557,B_556)
      | ~ v1_funct_1(C_554) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_3857,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_3854])).

tff(c_3863,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_78,c_76,c_72,c_1719,c_1746,c_3857])).

tff(c_3866,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3863])).

tff(c_3902,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3866,c_2])).

tff(c_3899,plain,(
    k6_partfun1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3866,c_3866,c_105])).

tff(c_3897,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3866,c_3866,c_10])).

tff(c_3498,plain,(
    ~ v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3366])).

tff(c_3982,plain,(
    ~ v1_xboole_0(k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3897,c_3498])).

tff(c_3994,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3902,c_3899,c_3982])).

tff(c_3995,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3863])).

tff(c_3997,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3995,c_1904])).

tff(c_4001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1449,c_3997])).

tff(c_4003,plain,(
    v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3366])).

tff(c_4030,plain,(
    k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4003,c_182])).

tff(c_4235,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4030,c_1420])).

tff(c_262,plain,(
    ! [B_103] : k7_relat_1(k1_xboole_0,B_103) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_257])).

tff(c_267,plain,(
    ! [B_103] :
      ( k9_relat_1(k1_xboole_0,B_103) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_22])).

tff(c_278,plain,(
    ! [B_103] : k9_relat_1(k1_xboole_0,B_103) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_194,c_267])).

tff(c_4256,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4235,c_278])).

tff(c_352,plain,(
    ! [A_120,B_121,D_122] :
      ( r2_relset_1(A_120,B_121,D_122,D_122)
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_362,plain,(
    r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_352])).

tff(c_372,plain,(
    ! [B_130,A_131] :
      ( k2_relat_1(B_130) = A_131
      | ~ v2_funct_2(B_130,A_131)
      | ~ v5_relat_1(B_130,A_131)
      | ~ v1_relat_1(B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_378,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_304,c_372])).

tff(c_384,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_378])).

tff(c_538,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_384])).

tff(c_586,plain,(
    ! [C_170,B_171,A_172] :
      ( v2_funct_2(C_170,B_171)
      | ~ v3_funct_2(C_170,A_172,B_171)
      | ~ v1_funct_1(C_170)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_172,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_589,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_586])).

tff(c_601,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_589])).

tff(c_603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_538,c_601])).

tff(c_604,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_384])).

tff(c_616,plain,(
    ! [A_173,B_174,C_175] :
      ( k2_relset_1(A_173,B_174,C_175) = k2_relat_1(C_175)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_619,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_616])).

tff(c_630,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_619])).

tff(c_643,plain,(
    ! [C_180,A_181,B_182] :
      ( v2_funct_1(C_180)
      | ~ v3_funct_2(C_180,A_181,B_182)
      | ~ v1_funct_1(C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_646,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_643])).

tff(c_658,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_646])).

tff(c_913,plain,(
    ! [C_250,D_251,B_252,A_253] :
      ( k2_funct_1(C_250) = D_251
      | k1_xboole_0 = B_252
      | k1_xboole_0 = A_253
      | ~ v2_funct_1(C_250)
      | ~ r2_relset_1(A_253,A_253,k1_partfun1(A_253,B_252,B_252,A_253,C_250,D_251),k6_partfun1(A_253))
      | k2_relset_1(A_253,B_252,C_250) != B_252
      | ~ m1_subset_1(D_251,k1_zfmisc_1(k2_zfmisc_1(B_252,A_253)))
      | ~ v1_funct_2(D_251,B_252,A_253)
      | ~ v1_funct_1(D_251)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_253,B_252)))
      | ~ v1_funct_2(C_250,A_253,B_252)
      | ~ v1_funct_1(C_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_916,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_913])).

tff(c_922,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_78,c_76,c_72,c_630,c_658,c_916])).

tff(c_925,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_922])).

tff(c_1202,plain,(
    ! [B_259] : k9_relat_1('#skF_2',B_259) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_925,c_278])).

tff(c_955,plain,(
    k6_partfun1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_925,c_105])).

tff(c_953,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_925,c_10])).

tff(c_334,plain,(
    ! [A_116,B_117] :
      ( k9_relat_1(k6_partfun1(A_116),B_117) = B_117
      | ~ m1_subset_1(B_117,k1_zfmisc_1(A_116)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_28])).

tff(c_342,plain,(
    k9_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_72,c_334])).

tff(c_1031,plain,(
    k9_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_953,c_342])).

tff(c_1035,plain,(
    k9_relat_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_955,c_1031])).

tff(c_1208,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1202,c_1035])).

tff(c_341,plain,(
    k9_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_80,c_334])).

tff(c_1032,plain,(
    k9_relat_1(k6_partfun1('#skF_2'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_953,c_341])).

tff(c_1036,plain,(
    k9_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_955,c_1032])).

tff(c_1206,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1202,c_1036])).

tff(c_1266,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1208,c_1206])).

tff(c_305,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_291])).

tff(c_1255,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1206,c_305])).

tff(c_1375,plain,(
    v5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_1255])).

tff(c_327,plain,
    ( v2_funct_2(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ v5_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_321])).

tff(c_329,plain,
    ( v2_funct_2(k1_xboole_0,k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_194,c_327])).

tff(c_330,plain,(
    ~ v5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_329])).

tff(c_942,plain,(
    ~ v5_relat_1('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_925,c_330])).

tff(c_1232,plain,(
    ~ v5_relat_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1206,c_1206,c_942])).

tff(c_1402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1375,c_1266,c_1266,c_1232])).

tff(c_1403,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_922])).

tff(c_809,plain,(
    ! [A_230,B_231] :
      ( k2_funct_2(A_230,B_231) = k2_funct_1(B_231)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(k2_zfmisc_1(A_230,A_230)))
      | ~ v3_funct_2(B_231,A_230,A_230)
      | ~ v1_funct_2(B_231,A_230,A_230)
      | ~ v1_funct_1(B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_812,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_809])).

tff(c_826,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_812])).

tff(c_841,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_826,c_68])).

tff(c_1405,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_841])).

tff(c_1409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_1405])).

tff(c_1411,plain,(
    v5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_329])).

tff(c_4283,plain,(
    v5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4256,c_4256,c_1411])).

tff(c_2661,plain,
    ( ~ v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'))
    | ~ v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'),'#skF_4')
    | v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1974])).

tff(c_3369,plain,
    ( ~ v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'))
    | ~ v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'),'#skF_4')
    | v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2662,c_2661])).

tff(c_3370,plain,(
    ~ v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3369])).

tff(c_4231,plain,(
    ~ v5_relat_1(k7_relat_1(k1_xboole_0,'#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4030,c_3370])).

tff(c_4239,plain,(
    ~ v5_relat_1(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_4231])).

tff(c_4266,plain,(
    ~ v5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4256,c_4239])).

tff(c_4441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4283,c_4266])).

tff(c_4442,plain,
    ( ~ v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'))
    | v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_3369])).

tff(c_4448,plain,(
    ~ v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4442])).

tff(c_4451,plain,
    ( ~ v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_16,c_4448])).

tff(c_4454,plain,(
    ~ v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2662,c_4451])).

tff(c_5084,plain,(
    ~ v1_xboole_0(k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5011,c_4454])).

tff(c_5097,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5016,c_5013,c_5084])).

tff(c_5098,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4977])).

tff(c_5100,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5098,c_1904])).

tff(c_5104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1449,c_5100])).

tff(c_5106,plain,(
    v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4442])).

tff(c_5105,plain,(
    v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_4442])).

tff(c_4443,plain,(
    v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_3369])).

tff(c_56,plain,(
    ! [B_58,A_57] :
      ( k2_relat_1(B_58) = A_57
      | ~ v2_funct_2(B_58,A_57)
      | ~ v5_relat_1(B_58,A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4447,plain,
    ( k2_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4')) = '#skF_4'
    | ~ v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_4443,c_56])).

tff(c_5825,plain,(
    k2_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5106,c_5105,c_4447])).

tff(c_5850,plain,(
    k2_relat_1(k7_relat_1(k1_xboole_0,'#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5820,c_5825])).

tff(c_5860,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_261,c_5850])).

tff(c_5854,plain,(
    v5_relat_1(k7_relat_1(k1_xboole_0,'#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5820,c_4443])).

tff(c_5864,plain,(
    v5_relat_1(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_5854])).

tff(c_5954,plain,(
    v5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5860,c_5864])).

tff(c_5894,plain,(
    ! [B_103] : k9_relat_1('#skF_4',B_103) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5860,c_5860,c_278])).

tff(c_5859,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5820,c_1419])).

tff(c_6136,plain,(
    k9_relat_1('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5860,c_5859])).

tff(c_6146,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5894,c_6136])).

tff(c_3360,plain,
    ( ~ v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3'),'#skF_3')
    | v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_2676])).

tff(c_3367,plain,(
    ~ v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3360])).

tff(c_5855,plain,(
    ~ v5_relat_1(k7_relat_1(k1_xboole_0,'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5820,c_3367])).

tff(c_5865,plain,(
    ~ v5_relat_1(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_5855])).

tff(c_6021,plain,(
    ~ v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5860,c_5865])).

tff(c_6168,plain,(
    ~ v5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6146,c_6021])).

tff(c_6179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5954,c_6168])).

tff(c_6180,plain,(
    v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_3360])).

tff(c_6181,plain,(
    v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_3360])).

tff(c_6184,plain,
    ( k2_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3')) = '#skF_3'
    | ~ v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_6181,c_56])).

tff(c_6187,plain,(
    k2_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3361,c_6180,c_6184])).

tff(c_6720,plain,(
    k2_relat_1(k7_relat_1(k1_xboole_0,'#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6715,c_6187])).

tff(c_6729,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_261,c_6720])).

tff(c_7026,plain,(
    ! [B_755] : k9_relat_1('#skF_3',B_755) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6729,c_6729,c_278])).

tff(c_6726,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6715,c_1420])).

tff(c_6827,plain,(
    k9_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6729,c_6726])).

tff(c_7030,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_7026,c_6827])).

tff(c_6723,plain,(
    v2_funct_2(k7_relat_1(k1_xboole_0,'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6715,c_6180])).

tff(c_6732,plain,(
    v2_funct_2(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_6723])).

tff(c_6837,plain,(
    v2_funct_2('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6729,c_6732])).

tff(c_6773,plain,(
    v5_relat_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6729,c_6729,c_1411])).

tff(c_6840,plain,
    ( k2_relat_1('#skF_3') = '#skF_3'
    | ~ v2_funct_2('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6773,c_56])).

tff(c_6843,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_6837,c_1691,c_6840])).

tff(c_6858,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6843,c_305])).

tff(c_7051,plain,(
    v5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7030,c_6858])).

tff(c_6189,plain,
    ( ~ v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'))
    | ~ v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'),'#skF_4')
    | v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2662,c_2661])).

tff(c_6190,plain,(
    ~ v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6189])).

tff(c_6721,plain,(
    ~ v5_relat_1(k7_relat_1(k1_xboole_0,'#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6715,c_6190])).

tff(c_6730,plain,(
    ~ v5_relat_1(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_6721])).

tff(c_6904,plain,(
    ~ v5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6729,c_6730])).

tff(c_7054,plain,(
    ~ v5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7030,c_6904])).

tff(c_7206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7051,c_7054])).

tff(c_7207,plain,
    ( ~ v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'))
    | v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_6189])).

tff(c_7237,plain,(
    ~ v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7207])).

tff(c_7251,plain,
    ( ~ v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_16,c_7237])).

tff(c_7254,plain,(
    ~ v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2662,c_7251])).

tff(c_7862,plain,(
    ~ v1_xboole_0(k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7790,c_7254])).

tff(c_7877,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7794,c_7791,c_7862])).

tff(c_7878,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7755])).

tff(c_7880,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7878,c_1904])).

tff(c_7884,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1449,c_7880])).

tff(c_7886,plain,(
    v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7207])).

tff(c_7885,plain,(
    v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_7207])).

tff(c_7208,plain,(
    v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_6189])).

tff(c_7212,plain,
    ( k2_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4')) = '#skF_4'
    | ~ v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_7208,c_56])).

tff(c_8607,plain,(
    k2_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2','#skF_2')),'#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7886,c_7885,c_7212])).

tff(c_8632,plain,(
    k2_relat_1(k7_relat_1(k1_xboole_0,'#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8602,c_8607])).

tff(c_8644,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_261,c_8632])).

tff(c_8685,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8644,c_8644,c_194])).

tff(c_237,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_231])).

tff(c_243,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_237])).

tff(c_1456,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_305,c_1450])).

tff(c_1465,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_1456])).

tff(c_1469,plain,(
    ~ v2_funct_2('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1465])).

tff(c_74,plain,(
    v3_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_1594,plain,(
    ! [C_311,B_312,A_313] :
      ( v2_funct_2(C_311,B_312)
      | ~ v3_funct_2(C_311,A_313,B_312)
      | ~ v1_funct_1(C_311)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_313,B_312))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1600,plain,
    ( v2_funct_2('#skF_4','#skF_2')
    | ~ v3_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_1594])).

tff(c_1612,plain,(
    v2_funct_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_1600])).

tff(c_1614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1469,c_1612])).

tff(c_1615,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1465])).

tff(c_8776,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8685,c_1615])).

tff(c_8790,plain,(
    r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8776,c_8776,c_1449])).

tff(c_30,plain,(
    ! [A_19] : k2_funct_1(k6_relat_1(A_19)) = k6_relat_1(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_147,plain,(
    ! [A_79] : k2_funct_1(k6_partfun1(A_79)) = k6_partfun1(A_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_30])).

tff(c_156,plain,(
    k6_partfun1(k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_147])).

tff(c_159,plain,(
    k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_156])).

tff(c_8689,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8644,c_8644,c_159])).

tff(c_8636,plain,(
    k2_relat_1(k7_relat_1(k1_xboole_0,'#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8602,c_6187])).

tff(c_8648,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_261,c_8636])).

tff(c_8701,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8644,c_8648])).

tff(c_8703,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8701,c_1904])).

tff(c_9030,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8790,c_8689,c_8776,c_8776,c_8703])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:11:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.15/2.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.52/2.93  
% 8.52/2.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.52/2.94  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 8.52/2.94  
% 8.52/2.94  %Foreground sorts:
% 8.52/2.94  
% 8.52/2.94  
% 8.52/2.94  %Background operators:
% 8.52/2.94  
% 8.52/2.94  
% 8.52/2.94  %Foreground operators:
% 8.52/2.94  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.52/2.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.52/2.94  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.52/2.94  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.52/2.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.52/2.94  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.52/2.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.52/2.94  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.52/2.94  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.52/2.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.52/2.94  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 8.52/2.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.52/2.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.52/2.94  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.52/2.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.52/2.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.52/2.94  tff('#skF_2', type, '#skF_2': $i).
% 8.52/2.94  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.52/2.94  tff('#skF_3', type, '#skF_3': $i).
% 8.52/2.94  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.52/2.94  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.52/2.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.52/2.94  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.52/2.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.52/2.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.52/2.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.52/2.94  tff('#skF_4', type, '#skF_4': $i).
% 8.52/2.94  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.52/2.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.52/2.94  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.52/2.94  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 8.52/2.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.52/2.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.52/2.94  
% 8.52/2.98  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.52/2.98  tff(f_67, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t194_relat_1)).
% 8.52/2.98  tff(f_118, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 8.52/2.98  tff(f_79, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.52/2.98  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.52/2.98  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 8.52/2.98  tff(f_59, axiom, (![A, B]: ((v1_xboole_0(A) & v1_relat_1(A)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc17_relat_1)).
% 8.52/2.98  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 8.52/2.98  tff(f_216, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 8.52/2.98  tff(f_97, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.52/2.98  tff(f_61, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.52/2.98  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.52/2.98  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.52/2.98  tff(f_138, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 8.52/2.98  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 8.52/2.98  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.52/2.98  tff(f_194, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 8.52/2.98  tff(f_150, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.52/2.98  tff(f_68, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 8.52/2.98  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 8.52/2.98  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 8.52/2.98  tff(f_148, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 8.52/2.98  tff(f_74, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 8.52/2.98  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.52/2.98  tff(c_170, plain, (![A_83, B_84]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_83, B_84)), B_84))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.52/2.98  tff(c_173, plain, (![B_4]: (r1_tarski(k2_relat_1(k1_xboole_0), B_4))), inference(superposition, [status(thm), theory('equality')], [c_10, c_170])).
% 8.52/2.98  tff(c_165, plain, (![A_82]: (r2_hidden('#skF_1'(A_82), A_82) | k1_xboole_0=A_82)), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.52/2.98  tff(c_32, plain, (![B_21, A_20]: (~r1_tarski(B_21, A_20) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.52/2.98  tff(c_189, plain, (![A_89]: (~r1_tarski(A_89, '#skF_1'(A_89)) | k1_xboole_0=A_89)), inference(resolution, [status(thm)], [c_165, c_32])).
% 8.52/2.98  tff(c_194, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_173, c_189])).
% 8.52/2.98  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.52/2.98  tff(c_94, plain, (![A_75]: (v1_relat_1(A_75) | ~v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.52/2.98  tff(c_98, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_94])).
% 8.52/2.98  tff(c_207, plain, (![A_91, B_92]: (v1_xboole_0(k7_relat_1(A_91, B_92)) | ~v1_relat_1(A_91) | ~v1_xboole_0(A_91))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.52/2.98  tff(c_179, plain, (![B_86, A_87]: (~v1_xboole_0(B_86) | B_86=A_87 | ~v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.52/2.98  tff(c_182, plain, (![A_87]: (k1_xboole_0=A_87 | ~v1_xboole_0(A_87))), inference(resolution, [status(thm)], [c_2, c_179])).
% 8.52/2.98  tff(c_253, plain, (![A_101, B_102]: (k7_relat_1(A_101, B_102)=k1_xboole_0 | ~v1_relat_1(A_101) | ~v1_xboole_0(A_101))), inference(resolution, [status(thm)], [c_207, c_182])).
% 8.52/2.98  tff(c_257, plain, (![B_102]: (k7_relat_1(k1_xboole_0, B_102)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_253])).
% 8.52/2.98  tff(c_261, plain, (![B_102]: (k7_relat_1(k1_xboole_0, B_102)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_98, c_257])).
% 8.52/2.98  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.52/2.98  tff(c_1439, plain, (![A_275, B_276, D_277]: (r2_relset_1(A_275, B_276, D_277, D_277) | ~m1_subset_1(D_277, k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.52/2.98  tff(c_1449, plain, (r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_1439])).
% 8.52/2.98  tff(c_86, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.52/2.98  tff(c_84, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.52/2.98  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.52/2.98  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.52/2.98  tff(c_76, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.52/2.98  tff(c_20, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.52/2.98  tff(c_231, plain, (![B_97, A_98]: (v1_relat_1(B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(A_98)) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.52/2.98  tff(c_234, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_80, c_231])).
% 8.52/2.98  tff(c_240, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_234])).
% 8.52/2.98  tff(c_291, plain, (![C_105, B_106, A_107]: (v5_relat_1(C_105, B_106) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_107, B_106))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.52/2.98  tff(c_304, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_80, c_291])).
% 8.52/2.98  tff(c_1450, plain, (![B_278, A_279]: (k2_relat_1(B_278)=A_279 | ~v2_funct_2(B_278, A_279) | ~v5_relat_1(B_278, A_279) | ~v1_relat_1(B_278))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.52/2.98  tff(c_1459, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_304, c_1450])).
% 8.52/2.98  tff(c_1468, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_240, c_1459])).
% 8.52/2.98  tff(c_1627, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_1468])).
% 8.52/2.98  tff(c_82, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.52/2.98  tff(c_1673, plain, (![C_324, B_325, A_326]: (v2_funct_2(C_324, B_325) | ~v3_funct_2(C_324, A_326, B_325) | ~v1_funct_1(C_324) | ~m1_subset_1(C_324, k1_zfmisc_1(k2_zfmisc_1(A_326, B_325))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.52/2.98  tff(c_1676, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_1673])).
% 8.52/2.98  tff(c_1688, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_1676])).
% 8.52/2.98  tff(c_1690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1627, c_1688])).
% 8.52/2.98  tff(c_1691, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_1468])).
% 8.52/2.98  tff(c_1705, plain, (![A_331, B_332, C_333]: (k2_relset_1(A_331, B_332, C_333)=k2_relat_1(C_333) | ~m1_subset_1(C_333, k1_zfmisc_1(k2_zfmisc_1(A_331, B_332))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.52/2.98  tff(c_1708, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_1705])).
% 8.52/2.98  tff(c_1719, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1691, c_1708])).
% 8.52/2.98  tff(c_1731, plain, (![C_336, A_337, B_338]: (v2_funct_1(C_336) | ~v3_funct_2(C_336, A_337, B_338) | ~v1_funct_1(C_336) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_337, B_338))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.52/2.98  tff(c_1734, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_1731])).
% 8.52/2.98  tff(c_1746, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_1734])).
% 8.52/2.98  tff(c_70, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.52/2.98  tff(c_8432, plain, (![C_853, D_854, B_855, A_856]: (k2_funct_1(C_853)=D_854 | k1_xboole_0=B_855 | k1_xboole_0=A_856 | ~v2_funct_1(C_853) | ~r2_relset_1(A_856, A_856, k1_partfun1(A_856, B_855, B_855, A_856, C_853, D_854), k6_partfun1(A_856)) | k2_relset_1(A_856, B_855, C_853)!=B_855 | ~m1_subset_1(D_854, k1_zfmisc_1(k2_zfmisc_1(B_855, A_856))) | ~v1_funct_2(D_854, B_855, A_856) | ~v1_funct_1(D_854) | ~m1_subset_1(C_853, k1_zfmisc_1(k2_zfmisc_1(A_856, B_855))) | ~v1_funct_2(C_853, A_856, B_855) | ~v1_funct_1(C_853))), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.52/2.98  tff(c_8435, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_8432])).
% 8.52/2.98  tff(c_8441, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_80, c_78, c_76, c_72, c_1719, c_1746, c_8435])).
% 8.52/2.98  tff(c_8444, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_8441])).
% 8.52/2.98  tff(c_8480, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8444, c_2])).
% 8.52/2.98  tff(c_99, plain, (![A_76]: (k6_relat_1(A_76)=k6_partfun1(A_76))), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.52/2.98  tff(c_26, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.52/2.98  tff(c_105, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_99, c_26])).
% 8.52/2.98  tff(c_8477, plain, (k6_partfun1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8444, c_8444, c_105])).
% 8.52/2.98  tff(c_8475, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8444, c_8444, c_10])).
% 8.52/2.98  tff(c_2518, plain, (![C_450, D_451, B_452, A_453]: (k2_funct_1(C_450)=D_451 | k1_xboole_0=B_452 | k1_xboole_0=A_453 | ~v2_funct_1(C_450) | ~r2_relset_1(A_453, A_453, k1_partfun1(A_453, B_452, B_452, A_453, C_450, D_451), k6_partfun1(A_453)) | k2_relset_1(A_453, B_452, C_450)!=B_452 | ~m1_subset_1(D_451, k1_zfmisc_1(k2_zfmisc_1(B_452, A_453))) | ~v1_funct_2(D_451, B_452, A_453) | ~v1_funct_1(D_451) | ~m1_subset_1(C_450, k1_zfmisc_1(k2_zfmisc_1(A_453, B_452))) | ~v1_funct_2(C_450, A_453, B_452) | ~v1_funct_1(C_450))), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.52/2.98  tff(c_2521, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_2518])).
% 8.52/2.98  tff(c_2527, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_80, c_78, c_76, c_72, c_1719, c_1746, c_2521])).
% 8.52/2.98  tff(c_2530, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2527])).
% 8.52/2.98  tff(c_2564, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2530, c_98])).
% 8.52/2.98  tff(c_2563, plain, (k6_partfun1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2530, c_2530, c_105])).
% 8.52/2.98  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.52/2.98  tff(c_2562, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2530, c_2530, c_8])).
% 8.52/2.98  tff(c_60, plain, (![A_61]: (k6_relat_1(A_61)=k6_partfun1(A_61))), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.52/2.98  tff(c_28, plain, (![A_17, B_18]: (k9_relat_1(k6_relat_1(A_17), B_18)=B_18 | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.52/2.98  tff(c_1412, plain, (![A_265, B_266]: (k9_relat_1(k6_partfun1(A_265), B_266)=B_266 | ~m1_subset_1(B_266, k1_zfmisc_1(A_265)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_28])).
% 8.52/2.98  tff(c_1420, plain, (k9_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_72, c_1412])).
% 8.52/2.98  tff(c_22, plain, (![B_14, A_13]: (k2_relat_1(k7_relat_1(B_14, A_13))=k9_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.52/2.98  tff(c_321, plain, (![B_111]: (v2_funct_2(B_111, k2_relat_1(B_111)) | ~v5_relat_1(B_111, k2_relat_1(B_111)) | ~v1_relat_1(B_111))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.52/2.98  tff(c_1929, plain, (![B_391, A_392]: (v2_funct_2(k7_relat_1(B_391, A_392), k2_relat_1(k7_relat_1(B_391, A_392))) | ~v5_relat_1(k7_relat_1(B_391, A_392), k9_relat_1(B_391, A_392)) | ~v1_relat_1(k7_relat_1(B_391, A_392)) | ~v1_relat_1(B_391))), inference(superposition, [status(thm), theory('equality')], [c_22, c_321])).
% 8.52/2.98  tff(c_1955, plain, (![B_398, A_399]: (v2_funct_2(k7_relat_1(B_398, A_399), k9_relat_1(B_398, A_399)) | ~v5_relat_1(k7_relat_1(B_398, A_399), k9_relat_1(B_398, A_399)) | ~v1_relat_1(k7_relat_1(B_398, A_399)) | ~v1_relat_1(B_398) | ~v1_relat_1(B_398))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1929])).
% 8.52/2.98  tff(c_1964, plain, (v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'), k9_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4')) | ~v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'), '#skF_4') | ~v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4')) | ~v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1420, c_1955])).
% 8.52/2.98  tff(c_1974, plain, (v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'), '#skF_4') | ~v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'), '#skF_4') | ~v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4')) | ~v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1420, c_1964])).
% 8.52/2.98  tff(c_1980, plain, (~v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1974])).
% 8.52/2.98  tff(c_2645, plain, (~v1_relat_1(k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2562, c_1980])).
% 8.52/2.98  tff(c_2653, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2564, c_2563, c_2645])).
% 8.52/2.98  tff(c_2654, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_2527])).
% 8.52/2.98  tff(c_1883, plain, (![A_377, B_378]: (k2_funct_2(A_377, B_378)=k2_funct_1(B_378) | ~m1_subset_1(B_378, k1_zfmisc_1(k2_zfmisc_1(A_377, A_377))) | ~v3_funct_2(B_378, A_377, A_377) | ~v1_funct_2(B_378, A_377, A_377) | ~v1_funct_1(B_378))), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.52/2.98  tff(c_1886, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_1883])).
% 8.52/2.98  tff(c_1900, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_1886])).
% 8.52/2.98  tff(c_68, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.52/2.98  tff(c_1904, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1900, c_68])).
% 8.52/2.98  tff(c_2656, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2654, c_1904])).
% 8.52/2.98  tff(c_2660, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1449, c_2656])).
% 8.52/2.98  tff(c_2662, plain, (v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitRight, [status(thm)], [c_1974])).
% 8.52/2.98  tff(c_3212, plain, (![C_505, D_506, B_507, A_508]: (k2_funct_1(C_505)=D_506 | k1_xboole_0=B_507 | k1_xboole_0=A_508 | ~v2_funct_1(C_505) | ~r2_relset_1(A_508, A_508, k1_partfun1(A_508, B_507, B_507, A_508, C_505, D_506), k6_partfun1(A_508)) | k2_relset_1(A_508, B_507, C_505)!=B_507 | ~m1_subset_1(D_506, k1_zfmisc_1(k2_zfmisc_1(B_507, A_508))) | ~v1_funct_2(D_506, B_507, A_508) | ~v1_funct_1(D_506) | ~m1_subset_1(C_505, k1_zfmisc_1(k2_zfmisc_1(A_508, B_507))) | ~v1_funct_2(C_505, A_508, B_507) | ~v1_funct_1(C_505))), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.52/2.98  tff(c_3215, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_3212])).
% 8.52/2.98  tff(c_3221, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_80, c_78, c_76, c_72, c_1719, c_1746, c_3215])).
% 8.52/2.98  tff(c_3224, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_3221])).
% 8.52/2.98  tff(c_3260, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3224, c_2])).
% 8.52/2.98  tff(c_3257, plain, (k6_partfun1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3224, c_3224, c_105])).
% 8.52/2.98  tff(c_3256, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3224, c_3224, c_8])).
% 8.52/2.98  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k7_relat_1(A_9, B_10)) | ~v1_relat_1(A_9) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.52/2.98  tff(c_1419, plain, (k9_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_80, c_1412])).
% 8.52/2.98  tff(c_1967, plain, (v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3'), k9_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3')) | ~v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3'), '#skF_3') | ~v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3')) | ~v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1419, c_1955])).
% 8.52/2.98  tff(c_1975, plain, (v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3'), '#skF_3') | ~v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3'), '#skF_3') | ~v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3')) | ~v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1419, c_1967])).
% 8.52/2.98  tff(c_2676, plain, (v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3'), '#skF_3') | ~v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3'), '#skF_3') | ~v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2662, c_2662, c_1975])).
% 8.52/2.98  tff(c_2677, plain, (~v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3'))), inference(splitLeft, [status(thm)], [c_2676])).
% 8.52/2.98  tff(c_2680, plain, (~v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_16, c_2677])).
% 8.52/2.98  tff(c_2683, plain, (~v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2662, c_2680])).
% 8.52/2.98  tff(c_3341, plain, (~v1_xboole_0(k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3256, c_2683])).
% 8.52/2.98  tff(c_3352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3260, c_3257, c_3341])).
% 8.52/2.98  tff(c_3353, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_3221])).
% 8.52/2.98  tff(c_3355, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3353, c_1904])).
% 8.52/2.98  tff(c_3359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1449, c_3355])).
% 8.52/2.98  tff(c_3361, plain, (v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3'))), inference(splitRight, [status(thm)], [c_2676])).
% 8.52/2.98  tff(c_18, plain, (![A_9, B_10]: (v1_xboole_0(k7_relat_1(A_9, B_10)) | ~v1_relat_1(A_9) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.52/2.98  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.52/2.98  tff(c_1432, plain, (![A_272, B_273, A_274]: (k7_relat_1(A_272, B_273)=A_274 | ~v1_xboole_0(A_274) | ~v1_relat_1(A_272) | ~v1_xboole_0(A_272))), inference(resolution, [status(thm)], [c_207, c_4])).
% 8.52/2.98  tff(c_1774, plain, (![A_354, B_355, A_352, B_353]: (k7_relat_1(A_354, B_355)=k7_relat_1(A_352, B_353) | ~v1_relat_1(A_354) | ~v1_xboole_0(A_354) | ~v1_relat_1(A_352) | ~v1_xboole_0(A_352))), inference(resolution, [status(thm)], [c_18, c_1432])).
% 8.52/2.98  tff(c_1871, plain, (![B_374, A_372, A_376, B_375, B_373]: (k7_relat_1(k7_relat_1(A_376, B_374), B_373)=k7_relat_1(A_372, B_375) | ~v1_relat_1(k7_relat_1(A_376, B_374)) | ~v1_relat_1(A_372) | ~v1_xboole_0(A_372) | ~v1_relat_1(A_376) | ~v1_xboole_0(A_376))), inference(resolution, [status(thm)], [c_18, c_1774])).
% 8.52/2.98  tff(c_1914, plain, (![A_380, B_379, A_383, B_381, B_382]: (k7_relat_1(k7_relat_1(A_383, B_382), B_381)=k7_relat_1(A_380, B_379) | ~v1_relat_1(A_380) | ~v1_xboole_0(A_380) | ~v1_relat_1(A_383) | ~v1_xboole_0(A_383))), inference(resolution, [status(thm)], [c_16, c_1871])).
% 8.52/2.98  tff(c_1919, plain, (![B_379, A_383, B_381, B_10, B_382, A_9]: (k7_relat_1(k7_relat_1(A_9, B_10), B_379)=k7_relat_1(k7_relat_1(A_383, B_382), B_381) | ~v1_relat_1(k7_relat_1(A_9, B_10)) | ~v1_relat_1(A_383) | ~v1_xboole_0(A_383) | ~v1_relat_1(A_9) | ~v1_xboole_0(A_9))), inference(resolution, [status(thm)], [c_18, c_1914])).
% 8.52/2.98  tff(c_3363, plain, (![B_379, A_383, B_382, B_381]: (k7_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3'), B_379)=k7_relat_1(k7_relat_1(A_383, B_382), B_381) | ~v1_relat_1(A_383) | ~v1_xboole_0(A_383) | ~v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2'))))), inference(resolution, [status(thm)], [c_3361, c_1919])).
% 8.52/2.98  tff(c_3366, plain, (![B_379, A_383, B_382, B_381]: (k7_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3'), B_379)=k7_relat_1(k7_relat_1(A_383, B_382), B_381) | ~v1_relat_1(A_383) | ~v1_xboole_0(A_383) | ~v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2662, c_3363])).
% 8.52/2.98  tff(c_8019, plain, (~v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_3366])).
% 8.52/2.98  tff(c_8549, plain, (~v1_xboole_0(k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8475, c_8019])).
% 8.52/2.98  tff(c_8566, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8480, c_8477, c_8549])).
% 8.52/2.98  tff(c_8567, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_8441])).
% 8.52/2.98  tff(c_8569, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8567, c_1904])).
% 8.52/2.98  tff(c_8573, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1449, c_8569])).
% 8.52/2.98  tff(c_8575, plain, (v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitRight, [status(thm)], [c_3366])).
% 8.52/2.98  tff(c_8602, plain, (k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_8575, c_182])).
% 8.52/2.98  tff(c_7746, plain, (![C_802, D_803, B_804, A_805]: (k2_funct_1(C_802)=D_803 | k1_xboole_0=B_804 | k1_xboole_0=A_805 | ~v2_funct_1(C_802) | ~r2_relset_1(A_805, A_805, k1_partfun1(A_805, B_804, B_804, A_805, C_802, D_803), k6_partfun1(A_805)) | k2_relset_1(A_805, B_804, C_802)!=B_804 | ~m1_subset_1(D_803, k1_zfmisc_1(k2_zfmisc_1(B_804, A_805))) | ~v1_funct_2(D_803, B_804, A_805) | ~v1_funct_1(D_803) | ~m1_subset_1(C_802, k1_zfmisc_1(k2_zfmisc_1(A_805, B_804))) | ~v1_funct_2(C_802, A_805, B_804) | ~v1_funct_1(C_802))), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.52/2.98  tff(c_7749, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_7746])).
% 8.52/2.98  tff(c_7755, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_80, c_78, c_76, c_72, c_1719, c_1746, c_7749])).
% 8.52/2.98  tff(c_7758, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_7755])).
% 8.52/2.98  tff(c_7794, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7758, c_2])).
% 8.52/2.98  tff(c_7791, plain, (k6_partfun1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7758, c_7758, c_105])).
% 8.52/2.98  tff(c_7790, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7758, c_7758, c_8])).
% 8.52/2.98  tff(c_6524, plain, (![C_730, D_731, B_732, A_733]: (k2_funct_1(C_730)=D_731 | k1_xboole_0=B_732 | k1_xboole_0=A_733 | ~v2_funct_1(C_730) | ~r2_relset_1(A_733, A_733, k1_partfun1(A_733, B_732, B_732, A_733, C_730, D_731), k6_partfun1(A_733)) | k2_relset_1(A_733, B_732, C_730)!=B_732 | ~m1_subset_1(D_731, k1_zfmisc_1(k2_zfmisc_1(B_732, A_733))) | ~v1_funct_2(D_731, B_732, A_733) | ~v1_funct_1(D_731) | ~m1_subset_1(C_730, k1_zfmisc_1(k2_zfmisc_1(A_733, B_732))) | ~v1_funct_2(C_730, A_733, B_732) | ~v1_funct_1(C_730))), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.52/2.98  tff(c_6527, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_6524])).
% 8.52/2.98  tff(c_6533, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_80, c_78, c_76, c_72, c_1719, c_1746, c_6527])).
% 8.52/2.98  tff(c_6536, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_6533])).
% 8.52/2.98  tff(c_6571, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6536, c_2])).
% 8.52/2.98  tff(c_6568, plain, (k6_partfun1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6536, c_6536, c_105])).
% 8.52/2.98  tff(c_6567, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6536, c_6536, c_8])).
% 8.52/2.98  tff(c_6342, plain, (~v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_3366])).
% 8.52/2.98  tff(c_6665, plain, (~v1_xboole_0(k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6567, c_6342])).
% 8.52/2.98  tff(c_6679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6571, c_6568, c_6665])).
% 8.52/2.98  tff(c_6680, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_6533])).
% 8.52/2.98  tff(c_6682, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6680, c_1904])).
% 8.52/2.98  tff(c_6686, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1449, c_6682])).
% 8.52/2.98  tff(c_6688, plain, (v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitRight, [status(thm)], [c_3366])).
% 8.52/2.98  tff(c_6715, plain, (k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_6688, c_182])).
% 8.52/2.98  tff(c_5652, plain, (![C_673, D_674, B_675, A_676]: (k2_funct_1(C_673)=D_674 | k1_xboole_0=B_675 | k1_xboole_0=A_676 | ~v2_funct_1(C_673) | ~r2_relset_1(A_676, A_676, k1_partfun1(A_676, B_675, B_675, A_676, C_673, D_674), k6_partfun1(A_676)) | k2_relset_1(A_676, B_675, C_673)!=B_675 | ~m1_subset_1(D_674, k1_zfmisc_1(k2_zfmisc_1(B_675, A_676))) | ~v1_funct_2(D_674, B_675, A_676) | ~v1_funct_1(D_674) | ~m1_subset_1(C_673, k1_zfmisc_1(k2_zfmisc_1(A_676, B_675))) | ~v1_funct_2(C_673, A_676, B_675) | ~v1_funct_1(C_673))), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.52/2.98  tff(c_5655, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_5652])).
% 8.52/2.98  tff(c_5661, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_80, c_78, c_76, c_72, c_1719, c_1746, c_5655])).
% 8.52/2.98  tff(c_5664, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_5661])).
% 8.52/2.98  tff(c_5700, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5664, c_2])).
% 8.52/2.98  tff(c_5697, plain, (k6_partfun1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5664, c_5664, c_105])).
% 8.52/2.98  tff(c_5695, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5664, c_5664, c_10])).
% 8.52/2.98  tff(c_5239, plain, (~v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_3366])).
% 8.52/2.98  tff(c_5769, plain, (~v1_xboole_0(k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5695, c_5239])).
% 8.52/2.98  tff(c_5784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5700, c_5697, c_5769])).
% 8.52/2.98  tff(c_5785, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_5661])).
% 8.52/2.98  tff(c_5787, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5785, c_1904])).
% 8.52/2.98  tff(c_5791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1449, c_5787])).
% 8.52/2.98  tff(c_5793, plain, (v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitRight, [status(thm)], [c_3366])).
% 8.52/2.98  tff(c_5820, plain, (k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_5793, c_182])).
% 8.52/2.98  tff(c_4968, plain, (![C_622, D_623, B_624, A_625]: (k2_funct_1(C_622)=D_623 | k1_xboole_0=B_624 | k1_xboole_0=A_625 | ~v2_funct_1(C_622) | ~r2_relset_1(A_625, A_625, k1_partfun1(A_625, B_624, B_624, A_625, C_622, D_623), k6_partfun1(A_625)) | k2_relset_1(A_625, B_624, C_622)!=B_624 | ~m1_subset_1(D_623, k1_zfmisc_1(k2_zfmisc_1(B_624, A_625))) | ~v1_funct_2(D_623, B_624, A_625) | ~v1_funct_1(D_623) | ~m1_subset_1(C_622, k1_zfmisc_1(k2_zfmisc_1(A_625, B_624))) | ~v1_funct_2(C_622, A_625, B_624) | ~v1_funct_1(C_622))), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.52/2.98  tff(c_4971, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_4968])).
% 8.52/2.98  tff(c_4977, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_80, c_78, c_76, c_72, c_1719, c_1746, c_4971])).
% 8.52/2.98  tff(c_4980, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_4977])).
% 8.52/2.98  tff(c_5016, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4980, c_2])).
% 8.52/2.98  tff(c_5013, plain, (k6_partfun1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4980, c_4980, c_105])).
% 8.52/2.98  tff(c_5011, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4980, c_4980, c_10])).
% 8.52/2.98  tff(c_3854, plain, (![C_554, D_555, B_556, A_557]: (k2_funct_1(C_554)=D_555 | k1_xboole_0=B_556 | k1_xboole_0=A_557 | ~v2_funct_1(C_554) | ~r2_relset_1(A_557, A_557, k1_partfun1(A_557, B_556, B_556, A_557, C_554, D_555), k6_partfun1(A_557)) | k2_relset_1(A_557, B_556, C_554)!=B_556 | ~m1_subset_1(D_555, k1_zfmisc_1(k2_zfmisc_1(B_556, A_557))) | ~v1_funct_2(D_555, B_556, A_557) | ~v1_funct_1(D_555) | ~m1_subset_1(C_554, k1_zfmisc_1(k2_zfmisc_1(A_557, B_556))) | ~v1_funct_2(C_554, A_557, B_556) | ~v1_funct_1(C_554))), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.52/2.98  tff(c_3857, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_3854])).
% 8.52/2.98  tff(c_3863, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_80, c_78, c_76, c_72, c_1719, c_1746, c_3857])).
% 8.52/2.98  tff(c_3866, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_3863])).
% 8.52/2.98  tff(c_3902, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3866, c_2])).
% 8.52/2.98  tff(c_3899, plain, (k6_partfun1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3866, c_3866, c_105])).
% 8.52/2.98  tff(c_3897, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3866, c_3866, c_10])).
% 8.52/2.98  tff(c_3498, plain, (~v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_3366])).
% 8.52/2.98  tff(c_3982, plain, (~v1_xboole_0(k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3897, c_3498])).
% 8.52/2.98  tff(c_3994, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3902, c_3899, c_3982])).
% 8.52/2.98  tff(c_3995, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_3863])).
% 8.52/2.98  tff(c_3997, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3995, c_1904])).
% 8.52/2.98  tff(c_4001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1449, c_3997])).
% 8.52/2.98  tff(c_4003, plain, (v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitRight, [status(thm)], [c_3366])).
% 8.52/2.98  tff(c_4030, plain, (k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_4003, c_182])).
% 8.52/2.98  tff(c_4235, plain, (k9_relat_1(k1_xboole_0, '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4030, c_1420])).
% 8.52/2.98  tff(c_262, plain, (![B_103]: (k7_relat_1(k1_xboole_0, B_103)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_98, c_257])).
% 8.52/2.98  tff(c_267, plain, (![B_103]: (k9_relat_1(k1_xboole_0, B_103)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_262, c_22])).
% 8.52/2.98  tff(c_278, plain, (![B_103]: (k9_relat_1(k1_xboole_0, B_103)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_98, c_194, c_267])).
% 8.52/2.98  tff(c_4256, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_4235, c_278])).
% 8.52/2.98  tff(c_352, plain, (![A_120, B_121, D_122]: (r2_relset_1(A_120, B_121, D_122, D_122) | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.52/2.98  tff(c_362, plain, (r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_352])).
% 8.52/2.98  tff(c_372, plain, (![B_130, A_131]: (k2_relat_1(B_130)=A_131 | ~v2_funct_2(B_130, A_131) | ~v5_relat_1(B_130, A_131) | ~v1_relat_1(B_130))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.52/2.98  tff(c_378, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_304, c_372])).
% 8.52/2.98  tff(c_384, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_240, c_378])).
% 8.52/2.98  tff(c_538, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_384])).
% 8.52/2.98  tff(c_586, plain, (![C_170, B_171, A_172]: (v2_funct_2(C_170, B_171) | ~v3_funct_2(C_170, A_172, B_171) | ~v1_funct_1(C_170) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_172, B_171))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.52/2.98  tff(c_589, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_586])).
% 8.52/2.98  tff(c_601, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_589])).
% 8.52/2.98  tff(c_603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_538, c_601])).
% 8.52/2.98  tff(c_604, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_384])).
% 8.52/2.98  tff(c_616, plain, (![A_173, B_174, C_175]: (k2_relset_1(A_173, B_174, C_175)=k2_relat_1(C_175) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.52/2.98  tff(c_619, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_616])).
% 8.52/2.98  tff(c_630, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_604, c_619])).
% 8.52/2.98  tff(c_643, plain, (![C_180, A_181, B_182]: (v2_funct_1(C_180) | ~v3_funct_2(C_180, A_181, B_182) | ~v1_funct_1(C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.52/2.98  tff(c_646, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_643])).
% 8.52/2.98  tff(c_658, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_646])).
% 8.52/2.98  tff(c_913, plain, (![C_250, D_251, B_252, A_253]: (k2_funct_1(C_250)=D_251 | k1_xboole_0=B_252 | k1_xboole_0=A_253 | ~v2_funct_1(C_250) | ~r2_relset_1(A_253, A_253, k1_partfun1(A_253, B_252, B_252, A_253, C_250, D_251), k6_partfun1(A_253)) | k2_relset_1(A_253, B_252, C_250)!=B_252 | ~m1_subset_1(D_251, k1_zfmisc_1(k2_zfmisc_1(B_252, A_253))) | ~v1_funct_2(D_251, B_252, A_253) | ~v1_funct_1(D_251) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_253, B_252))) | ~v1_funct_2(C_250, A_253, B_252) | ~v1_funct_1(C_250))), inference(cnfTransformation, [status(thm)], [f_194])).
% 8.52/2.98  tff(c_916, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_913])).
% 8.52/2.98  tff(c_922, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_80, c_78, c_76, c_72, c_630, c_658, c_916])).
% 8.52/2.98  tff(c_925, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_922])).
% 8.52/2.98  tff(c_1202, plain, (![B_259]: (k9_relat_1('#skF_2', B_259)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_925, c_925, c_278])).
% 8.52/2.98  tff(c_955, plain, (k6_partfun1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_925, c_925, c_105])).
% 8.52/2.98  tff(c_953, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_925, c_925, c_10])).
% 8.52/2.98  tff(c_334, plain, (![A_116, B_117]: (k9_relat_1(k6_partfun1(A_116), B_117)=B_117 | ~m1_subset_1(B_117, k1_zfmisc_1(A_116)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_28])).
% 8.52/2.98  tff(c_342, plain, (k9_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_72, c_334])).
% 8.52/2.98  tff(c_1031, plain, (k9_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_953, c_342])).
% 8.52/2.98  tff(c_1035, plain, (k9_relat_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_955, c_1031])).
% 8.52/2.98  tff(c_1208, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1202, c_1035])).
% 8.52/2.98  tff(c_341, plain, (k9_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_80, c_334])).
% 8.52/2.98  tff(c_1032, plain, (k9_relat_1(k6_partfun1('#skF_2'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_953, c_341])).
% 8.52/2.98  tff(c_1036, plain, (k9_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_955, c_1032])).
% 8.52/2.98  tff(c_1206, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1202, c_1036])).
% 8.52/2.98  tff(c_1266, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1208, c_1206])).
% 8.52/2.98  tff(c_305, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_291])).
% 8.52/2.98  tff(c_1255, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1206, c_305])).
% 8.52/2.98  tff(c_1375, plain, (v5_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1266, c_1255])).
% 8.52/2.98  tff(c_327, plain, (v2_funct_2(k1_xboole_0, k2_relat_1(k1_xboole_0)) | ~v5_relat_1(k1_xboole_0, k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_194, c_321])).
% 8.52/2.98  tff(c_329, plain, (v2_funct_2(k1_xboole_0, k1_xboole_0) | ~v5_relat_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_98, c_194, c_327])).
% 8.52/2.98  tff(c_330, plain, (~v5_relat_1(k1_xboole_0, k1_xboole_0)), inference(splitLeft, [status(thm)], [c_329])).
% 8.52/2.98  tff(c_942, plain, (~v5_relat_1('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_925, c_925, c_330])).
% 8.52/2.98  tff(c_1232, plain, (~v5_relat_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1206, c_1206, c_942])).
% 8.52/2.98  tff(c_1402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1375, c_1266, c_1266, c_1232])).
% 8.52/2.98  tff(c_1403, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_922])).
% 8.52/2.98  tff(c_809, plain, (![A_230, B_231]: (k2_funct_2(A_230, B_231)=k2_funct_1(B_231) | ~m1_subset_1(B_231, k1_zfmisc_1(k2_zfmisc_1(A_230, A_230))) | ~v3_funct_2(B_231, A_230, A_230) | ~v1_funct_2(B_231, A_230, A_230) | ~v1_funct_1(B_231))), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.52/2.98  tff(c_812, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_809])).
% 8.52/2.98  tff(c_826, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_812])).
% 8.52/2.98  tff(c_841, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_826, c_68])).
% 8.52/2.98  tff(c_1405, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1403, c_841])).
% 8.52/2.98  tff(c_1409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_362, c_1405])).
% 8.52/2.98  tff(c_1411, plain, (v5_relat_1(k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_329])).
% 8.52/2.98  tff(c_4283, plain, (v5_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4256, c_4256, c_1411])).
% 8.52/2.98  tff(c_2661, plain, (~v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4')) | ~v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'), '#skF_4') | v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_1974])).
% 8.52/2.98  tff(c_3369, plain, (~v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4')) | ~v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'), '#skF_4') | v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2662, c_2661])).
% 8.52/2.98  tff(c_3370, plain, (~v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_3369])).
% 8.52/2.98  tff(c_4231, plain, (~v5_relat_1(k7_relat_1(k1_xboole_0, '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4030, c_3370])).
% 8.52/2.98  tff(c_4239, plain, (~v5_relat_1(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_261, c_4231])).
% 8.52/2.98  tff(c_4266, plain, (~v5_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4256, c_4239])).
% 8.52/2.98  tff(c_4441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4283, c_4266])).
% 8.52/2.98  tff(c_4442, plain, (~v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4')) | v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_3369])).
% 8.52/2.98  tff(c_4448, plain, (~v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'))), inference(splitLeft, [status(thm)], [c_4442])).
% 8.52/2.98  tff(c_4451, plain, (~v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_16, c_4448])).
% 8.52/2.98  tff(c_4454, plain, (~v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2662, c_4451])).
% 8.52/2.98  tff(c_5084, plain, (~v1_xboole_0(k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5011, c_4454])).
% 8.52/2.98  tff(c_5097, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5016, c_5013, c_5084])).
% 8.52/2.98  tff(c_5098, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_4977])).
% 8.52/2.98  tff(c_5100, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5098, c_1904])).
% 8.52/2.98  tff(c_5104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1449, c_5100])).
% 8.52/2.98  tff(c_5106, plain, (v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'))), inference(splitRight, [status(thm)], [c_4442])).
% 8.52/2.98  tff(c_5105, plain, (v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_4442])).
% 8.52/2.98  tff(c_4443, plain, (v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_3369])).
% 8.52/2.98  tff(c_56, plain, (![B_58, A_57]: (k2_relat_1(B_58)=A_57 | ~v2_funct_2(B_58, A_57) | ~v5_relat_1(B_58, A_57) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.52/2.98  tff(c_4447, plain, (k2_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'))='#skF_4' | ~v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'), '#skF_4') | ~v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'))), inference(resolution, [status(thm)], [c_4443, c_56])).
% 8.52/2.98  tff(c_5825, plain, (k2_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5106, c_5105, c_4447])).
% 8.52/2.98  tff(c_5850, plain, (k2_relat_1(k7_relat_1(k1_xboole_0, '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5820, c_5825])).
% 8.52/2.98  tff(c_5860, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_194, c_261, c_5850])).
% 8.52/2.98  tff(c_5854, plain, (v5_relat_1(k7_relat_1(k1_xboole_0, '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5820, c_4443])).
% 8.52/2.98  tff(c_5864, plain, (v5_relat_1(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_261, c_5854])).
% 8.52/2.98  tff(c_5954, plain, (v5_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5860, c_5864])).
% 8.52/2.98  tff(c_5894, plain, (![B_103]: (k9_relat_1('#skF_4', B_103)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5860, c_5860, c_278])).
% 8.52/2.98  tff(c_5859, plain, (k9_relat_1(k1_xboole_0, '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5820, c_1419])).
% 8.52/2.98  tff(c_6136, plain, (k9_relat_1('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5860, c_5859])).
% 8.52/2.98  tff(c_6146, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5894, c_6136])).
% 8.52/2.98  tff(c_3360, plain, (~v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3'), '#skF_3') | v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_2676])).
% 8.52/2.98  tff(c_3367, plain, (~v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_3360])).
% 8.52/2.98  tff(c_5855, plain, (~v5_relat_1(k7_relat_1(k1_xboole_0, '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5820, c_3367])).
% 8.52/2.98  tff(c_5865, plain, (~v5_relat_1(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_261, c_5855])).
% 8.52/2.98  tff(c_6021, plain, (~v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5860, c_5865])).
% 8.52/2.98  tff(c_6168, plain, (~v5_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6146, c_6021])).
% 8.52/2.98  tff(c_6179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5954, c_6168])).
% 8.52/2.98  tff(c_6180, plain, (v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_3360])).
% 8.52/2.98  tff(c_6181, plain, (v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_3360])).
% 8.52/2.98  tff(c_6184, plain, (k2_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3'))='#skF_3' | ~v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3'), '#skF_3') | ~v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3'))), inference(resolution, [status(thm)], [c_6181, c_56])).
% 8.52/2.98  tff(c_6187, plain, (k2_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3361, c_6180, c_6184])).
% 8.52/2.98  tff(c_6720, plain, (k2_relat_1(k7_relat_1(k1_xboole_0, '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6715, c_6187])).
% 8.52/2.98  tff(c_6729, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_194, c_261, c_6720])).
% 8.52/2.98  tff(c_7026, plain, (![B_755]: (k9_relat_1('#skF_3', B_755)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6729, c_6729, c_278])).
% 8.52/2.98  tff(c_6726, plain, (k9_relat_1(k1_xboole_0, '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6715, c_1420])).
% 8.52/2.98  tff(c_6827, plain, (k9_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6729, c_6726])).
% 8.52/2.98  tff(c_7030, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_7026, c_6827])).
% 8.52/2.98  tff(c_6723, plain, (v2_funct_2(k7_relat_1(k1_xboole_0, '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6715, c_6180])).
% 8.52/2.98  tff(c_6732, plain, (v2_funct_2(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_261, c_6723])).
% 8.52/2.98  tff(c_6837, plain, (v2_funct_2('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6729, c_6732])).
% 8.52/2.98  tff(c_6773, plain, (v5_relat_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6729, c_6729, c_1411])).
% 8.52/2.98  tff(c_6840, plain, (k2_relat_1('#skF_3')='#skF_3' | ~v2_funct_2('#skF_3', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6773, c_56])).
% 8.52/2.98  tff(c_6843, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_240, c_6837, c_1691, c_6840])).
% 8.52/2.98  tff(c_6858, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6843, c_305])).
% 8.52/2.98  tff(c_7051, plain, (v5_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7030, c_6858])).
% 8.52/2.98  tff(c_6189, plain, (~v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4')) | ~v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'), '#skF_4') | v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2662, c_2661])).
% 8.52/2.98  tff(c_6190, plain, (~v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_6189])).
% 8.52/2.98  tff(c_6721, plain, (~v5_relat_1(k7_relat_1(k1_xboole_0, '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6715, c_6190])).
% 8.52/2.98  tff(c_6730, plain, (~v5_relat_1(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_261, c_6721])).
% 8.52/2.98  tff(c_6904, plain, (~v5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6729, c_6730])).
% 8.52/2.98  tff(c_7054, plain, (~v5_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7030, c_6904])).
% 8.52/2.98  tff(c_7206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7051, c_7054])).
% 8.52/2.98  tff(c_7207, plain, (~v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4')) | v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_6189])).
% 8.52/2.98  tff(c_7237, plain, (~v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'))), inference(splitLeft, [status(thm)], [c_7207])).
% 8.52/2.98  tff(c_7251, plain, (~v1_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_16, c_7237])).
% 8.52/2.98  tff(c_7254, plain, (~v1_xboole_0(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2662, c_7251])).
% 8.52/2.98  tff(c_7862, plain, (~v1_xboole_0(k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7790, c_7254])).
% 8.52/2.98  tff(c_7877, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7794, c_7791, c_7862])).
% 8.52/2.98  tff(c_7878, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_7755])).
% 8.52/2.98  tff(c_7880, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7878, c_1904])).
% 8.52/2.98  tff(c_7884, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1449, c_7880])).
% 8.52/2.98  tff(c_7886, plain, (v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'))), inference(splitRight, [status(thm)], [c_7207])).
% 8.52/2.98  tff(c_7885, plain, (v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_7207])).
% 8.52/2.98  tff(c_7208, plain, (v5_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_6189])).
% 8.52/2.98  tff(c_7212, plain, (k2_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'))='#skF_4' | ~v2_funct_2(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'), '#skF_4') | ~v1_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'))), inference(resolution, [status(thm)], [c_7208, c_56])).
% 8.52/2.98  tff(c_8607, plain, (k2_relat_1(k7_relat_1(k6_partfun1(k2_zfmisc_1('#skF_2', '#skF_2')), '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7886, c_7885, c_7212])).
% 8.52/2.98  tff(c_8632, plain, (k2_relat_1(k7_relat_1(k1_xboole_0, '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8602, c_8607])).
% 8.52/2.98  tff(c_8644, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_194, c_261, c_8632])).
% 8.52/2.98  tff(c_8685, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8644, c_8644, c_194])).
% 8.52/2.98  tff(c_237, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_231])).
% 8.52/2.98  tff(c_243, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_237])).
% 8.52/2.98  tff(c_1456, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_305, c_1450])).
% 8.52/2.98  tff(c_1465, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_1456])).
% 8.52/2.98  tff(c_1469, plain, (~v2_funct_2('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_1465])).
% 8.52/2.98  tff(c_74, plain, (v3_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.52/2.98  tff(c_1594, plain, (![C_311, B_312, A_313]: (v2_funct_2(C_311, B_312) | ~v3_funct_2(C_311, A_313, B_312) | ~v1_funct_1(C_311) | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_313, B_312))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.52/2.98  tff(c_1600, plain, (v2_funct_2('#skF_4', '#skF_2') | ~v3_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_1594])).
% 8.52/2.98  tff(c_1612, plain, (v2_funct_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_1600])).
% 8.52/2.98  tff(c_1614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1469, c_1612])).
% 8.52/2.98  tff(c_1615, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_1465])).
% 8.52/2.98  tff(c_8776, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8685, c_1615])).
% 8.52/2.98  tff(c_8790, plain, (r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8776, c_8776, c_1449])).
% 8.52/2.98  tff(c_30, plain, (![A_19]: (k2_funct_1(k6_relat_1(A_19))=k6_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.52/2.98  tff(c_147, plain, (![A_79]: (k2_funct_1(k6_partfun1(A_79))=k6_partfun1(A_79))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60, c_30])).
% 8.52/2.98  tff(c_156, plain, (k6_partfun1(k1_xboole_0)=k2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_105, c_147])).
% 8.52/2.98  tff(c_159, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_105, c_156])).
% 8.52/2.98  tff(c_8689, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8644, c_8644, c_159])).
% 8.52/2.98  tff(c_8636, plain, (k2_relat_1(k7_relat_1(k1_xboole_0, '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8602, c_6187])).
% 8.52/2.98  tff(c_8648, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_194, c_261, c_8636])).
% 8.52/2.98  tff(c_8701, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8644, c_8648])).
% 8.52/2.98  tff(c_8703, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8701, c_1904])).
% 8.52/2.98  tff(c_9030, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8790, c_8689, c_8776, c_8776, c_8703])).
% 8.52/2.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.52/2.98  
% 8.52/2.98  Inference rules
% 8.52/2.98  ----------------------
% 8.52/2.98  #Ref     : 0
% 8.52/2.98  #Sup     : 2136
% 8.52/2.98  #Fact    : 0
% 8.52/2.98  #Define  : 0
% 8.52/2.98  #Split   : 43
% 8.52/2.98  #Chain   : 0
% 8.52/2.98  #Close   : 0
% 8.52/2.98  
% 8.52/2.98  Ordering : KBO
% 8.52/2.98  
% 8.52/2.98  Simplification rules
% 8.52/2.98  ----------------------
% 8.52/2.98  #Subsume      : 440
% 8.52/2.98  #Demod        : 3344
% 8.52/2.98  #Tautology    : 894
% 8.52/2.98  #SimpNegUnit  : 6
% 8.52/2.98  #BackRed      : 802
% 8.52/2.98  
% 8.52/2.98  #Partial instantiations: 0
% 8.52/2.98  #Strategies tried      : 1
% 8.52/2.98  
% 8.52/2.98  Timing (in seconds)
% 8.52/2.98  ----------------------
% 8.52/2.98  Preprocessing        : 0.37
% 8.52/2.98  Parsing              : 0.19
% 8.52/2.98  CNF conversion       : 0.03
% 8.52/2.98  Main loop            : 1.66
% 8.52/2.98  Inferencing          : 0.50
% 8.52/2.98  Reduction            : 0.62
% 8.52/2.98  Demodulation         : 0.48
% 8.52/2.98  BG Simplification    : 0.06
% 8.52/2.98  Subsumption          : 0.34
% 8.52/2.98  Abstraction          : 0.07
% 8.52/2.98  MUC search           : 0.00
% 8.52/2.99  Cooper               : 0.00
% 8.52/2.99  Total                : 2.13
% 8.52/2.99  Index Insertion      : 0.00
% 8.52/2.99  Index Deletion       : 0.00
% 8.52/2.99  Index Matching       : 0.00
% 8.52/2.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
