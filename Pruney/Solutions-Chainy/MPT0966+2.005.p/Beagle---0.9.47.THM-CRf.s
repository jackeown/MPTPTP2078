%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:08 EST 2020

% Result     : Theorem 8.25s
% Output     : CNFRefutation 8.55s
% Verified   : 
% Statistics : Number of formulae       :  303 (3495 expanded)
%              Number of leaves         :   33 (1119 expanded)
%              Depth                    :   16
%              Number of atoms          :  574 (10280 expanded)
%              Number of equality atoms :  171 (3379 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_130,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_143,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_130])).

tff(c_11368,plain,(
    ! [C_870,A_871,B_872] :
      ( v4_relat_1(C_870,A_871)
      | ~ m1_subset_1(C_870,k1_zfmisc_1(k2_zfmisc_1(A_871,B_872))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_11383,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_11368])).

tff(c_22,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_11526,plain,(
    ! [A_895,B_896,C_897] :
      ( k2_relset_1(A_895,B_896,C_897) = k2_relat_1(C_897)
      | ~ m1_subset_1(C_897,k1_zfmisc_1(k2_zfmisc_1(A_895,B_896))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_11541,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_11526])).

tff(c_52,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_11543,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11541,c_52])).

tff(c_11780,plain,(
    ! [C_933,A_934,B_935] :
      ( m1_subset_1(C_933,k1_zfmisc_1(k2_zfmisc_1(A_934,B_935)))
      | ~ r1_tarski(k2_relat_1(C_933),B_935)
      | ~ r1_tarski(k1_relat_1(C_933),A_934)
      | ~ v1_relat_1(C_933) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_56,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_3370,plain,(
    ! [A_303,B_304,C_305] :
      ( k1_relset_1(A_303,B_304,C_305) = k1_relat_1(C_305)
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(A_303,B_304))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3385,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_3370])).

tff(c_3829,plain,(
    ! [B_370,A_371,C_372] :
      ( k1_xboole_0 = B_370
      | k1_relset_1(A_371,B_370,C_372) = A_371
      | ~ v1_funct_2(C_372,A_371,B_370)
      | ~ m1_subset_1(C_372,k1_zfmisc_1(k2_zfmisc_1(A_371,B_370))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3839,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_3829])).

tff(c_3850,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3385,c_3839])).

tff(c_3851,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3850])).

tff(c_3245,plain,(
    ! [C_286,A_287,B_288] :
      ( v4_relat_1(C_286,A_287)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(A_287,B_288))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3260,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_3245])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_370,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_385,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_370])).

tff(c_655,plain,(
    ! [B_117,A_118,C_119] :
      ( k1_xboole_0 = B_117
      | k1_relset_1(A_118,B_117,C_119) = A_118
      | ~ v1_funct_2(C_119,A_118,B_117)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_665,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_655])).

tff(c_676,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_385,c_665])).

tff(c_677,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_676])).

tff(c_312,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_327,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_312])).

tff(c_362,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_52])).

tff(c_528,plain,(
    ! [C_99,A_100,B_101] :
      ( m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ r1_tarski(k2_relat_1(C_99),B_101)
      | ~ r1_tarski(k1_relat_1(C_99),A_100)
      | ~ v1_relat_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2514,plain,(
    ! [C_246,A_247,B_248] :
      ( r1_tarski(C_246,k2_zfmisc_1(A_247,B_248))
      | ~ r1_tarski(k2_relat_1(C_246),B_248)
      | ~ r1_tarski(k1_relat_1(C_246),A_247)
      | ~ v1_relat_1(C_246) ) ),
    inference(resolution,[status(thm)],[c_528,c_16])).

tff(c_2516,plain,(
    ! [A_247] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_247,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_247)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_362,c_2514])).

tff(c_2524,plain,(
    ! [A_249] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_249,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_677,c_2516])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_384,plain,(
    ! [A_78,B_79,A_6] :
      ( k1_relset_1(A_78,B_79,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_78,B_79)) ) ),
    inference(resolution,[status(thm)],[c_18,c_370])).

tff(c_2530,plain,(
    ! [A_249] :
      ( k1_relset_1(A_249,'#skF_3','#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',A_249) ) ),
    inference(resolution,[status(thm)],[c_2524,c_384])).

tff(c_2556,plain,(
    ! [A_250] :
      ( k1_relset_1(A_250,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_250) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_2530])).

tff(c_2561,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_2556])).

tff(c_2522,plain,(
    ! [A_247] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_247,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_677,c_2516])).

tff(c_871,plain,(
    ! [B_137,C_138,A_139] :
      ( k1_xboole_0 = B_137
      | v1_funct_2(C_138,A_139,B_137)
      | k1_relset_1(A_139,B_137,C_138) != A_139
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_139,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2576,plain,(
    ! [B_252,A_253,A_254] :
      ( k1_xboole_0 = B_252
      | v1_funct_2(A_253,A_254,B_252)
      | k1_relset_1(A_254,B_252,A_253) != A_254
      | ~ r1_tarski(A_253,k2_zfmisc_1(A_254,B_252)) ) ),
    inference(resolution,[status(thm)],[c_18,c_871])).

tff(c_2601,plain,(
    ! [A_247] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2('#skF_4',A_247,'#skF_3')
      | k1_relset_1(A_247,'#skF_3','#skF_4') != A_247
      | ~ r1_tarski('#skF_1',A_247) ) ),
    inference(resolution,[status(thm)],[c_2522,c_2576])).

tff(c_3099,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2601])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3174,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3099,c_8])).

tff(c_101,plain,(
    ! [B_36,A_37] :
      ( B_36 = A_37
      | ~ r1_tarski(B_36,A_37)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_101])).

tff(c_222,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_361,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_222])).

tff(c_3209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3174,c_361])).

tff(c_3212,plain,(
    ! [A_281] :
      ( v1_funct_2('#skF_4',A_281,'#skF_3')
      | k1_relset_1(A_281,'#skF_3','#skF_4') != A_281
      | ~ r1_tarski('#skF_1',A_281) ) ),
    inference(splitRight,[status(thm)],[c_2601])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_60,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_48])).

tff(c_161,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_3218,plain,
    ( k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3212,c_161])).

tff(c_3223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2561,c_3218])).

tff(c_3224,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_3436,plain,(
    ! [A_316,B_317,C_318] :
      ( k2_relset_1(A_316,B_317,C_318) = k2_relat_1(C_318)
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(A_316,B_317))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3443,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_3436])).

tff(c_3452,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3224,c_3443])).

tff(c_3542,plain,(
    ! [C_330,A_331,B_332] :
      ( m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(A_331,B_332)))
      | ~ r1_tarski(k2_relat_1(C_330),B_332)
      | ~ r1_tarski(k1_relat_1(C_330),A_331)
      | ~ v1_relat_1(C_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_5433,plain,(
    ! [C_475,A_476,B_477] :
      ( r1_tarski(C_475,k2_zfmisc_1(A_476,B_477))
      | ~ r1_tarski(k2_relat_1(C_475),B_477)
      | ~ r1_tarski(k1_relat_1(C_475),A_476)
      | ~ v1_relat_1(C_475) ) ),
    inference(resolution,[status(thm)],[c_3542,c_16])).

tff(c_5435,plain,(
    ! [A_476,B_477] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_476,B_477))
      | ~ r1_tarski('#skF_3',B_477)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_476)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3452,c_5433])).

tff(c_5442,plain,(
    ! [A_478,B_479] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_478,B_479))
      | ~ r1_tarski('#skF_3',B_479)
      | ~ r1_tarski('#skF_1',A_478) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_3851,c_5435])).

tff(c_3384,plain,(
    ! [A_303,B_304,A_6] :
      ( k1_relset_1(A_303,B_304,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_303,B_304)) ) ),
    inference(resolution,[status(thm)],[c_18,c_3370])).

tff(c_5445,plain,(
    ! [A_478,B_479] :
      ( k1_relset_1(A_478,B_479,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_3',B_479)
      | ~ r1_tarski('#skF_1',A_478) ) ),
    inference(resolution,[status(thm)],[c_5442,c_3384])).

tff(c_5477,plain,(
    ! [A_480,B_481] :
      ( k1_relset_1(A_480,B_481,'#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_3',B_481)
      | ~ r1_tarski('#skF_1',A_480) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3851,c_5445])).

tff(c_5482,plain,(
    ! [A_482] :
      ( k1_relset_1(A_482,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_482) ) ),
    inference(resolution,[status(thm)],[c_6,c_5477])).

tff(c_5487,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_5482])).

tff(c_5516,plain,(
    ! [C_489,A_490] :
      ( r1_tarski(C_489,k2_zfmisc_1(A_490,k2_relat_1(C_489)))
      | ~ r1_tarski(k1_relat_1(C_489),A_490)
      | ~ v1_relat_1(C_489) ) ),
    inference(resolution,[status(thm)],[c_6,c_5433])).

tff(c_5563,plain,(
    ! [A_490] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_490,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_490)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3452,c_5516])).

tff(c_5583,plain,(
    ! [A_490] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_490,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_490) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_3851,c_5563])).

tff(c_3674,plain,(
    ! [B_348,C_349,A_350] :
      ( k1_xboole_0 = B_348
      | v1_funct_2(C_349,A_350,B_348)
      | k1_relset_1(A_350,B_348,C_349) != A_350
      | ~ m1_subset_1(C_349,k1_zfmisc_1(k2_zfmisc_1(A_350,B_348))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5777,plain,(
    ! [B_499,A_500,A_501] :
      ( k1_xboole_0 = B_499
      | v1_funct_2(A_500,A_501,B_499)
      | k1_relset_1(A_501,B_499,A_500) != A_501
      | ~ r1_tarski(A_500,k2_zfmisc_1(A_501,B_499)) ) ),
    inference(resolution,[status(thm)],[c_18,c_3674])).

tff(c_5808,plain,(
    ! [A_490] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2('#skF_4',A_490,'#skF_3')
      | k1_relset_1(A_490,'#skF_3','#skF_4') != A_490
      | ~ r1_tarski('#skF_1',A_490) ) ),
    inference(resolution,[status(thm)],[c_5583,c_5777])).

tff(c_5881,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5808])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5009,plain,(
    ! [C_451,A_452] :
      ( m1_subset_1(C_451,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_451),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_451),A_452)
      | ~ v1_relat_1(C_451) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3542])).

tff(c_5011,plain,(
    ! [A_452] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_452)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3452,c_5009])).

tff(c_5013,plain,(
    ! [A_452] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski('#skF_1',A_452) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_3851,c_5011])).

tff(c_5014,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_5013])).

tff(c_5895,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5881,c_5014])).

tff(c_5958,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5895])).

tff(c_5961,plain,(
    ! [A_507] :
      ( v1_funct_2('#skF_4',A_507,'#skF_3')
      | k1_relset_1(A_507,'#skF_3','#skF_4') != A_507
      | ~ r1_tarski('#skF_1',A_507) ) ),
    inference(splitRight,[status(thm)],[c_5808])).

tff(c_5967,plain,
    ( k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_5961,c_161])).

tff(c_5972,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5487,c_5967])).

tff(c_5974,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5013])).

tff(c_116,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_101])).

tff(c_6000,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5974,c_116])).

tff(c_3261,plain,(
    ! [C_289,A_290] :
      ( v4_relat_1(C_289,A_290)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3245])).

tff(c_3265,plain,(
    ! [A_6,A_290] :
      ( v4_relat_1(A_6,A_290)
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_3261])).

tff(c_202,plain,(
    ! [B_51,A_52] :
      ( r1_tarski(k1_relat_1(B_51),A_52)
      | ~ v4_relat_1(B_51,A_52)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_142,plain,(
    ! [A_6,A_40,B_41] :
      ( v1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_40,B_41)) ) ),
    inference(resolution,[status(thm)],[c_18,c_130])).

tff(c_3712,plain,(
    ! [B_353,A_354,B_355] :
      ( v1_relat_1(k1_relat_1(B_353))
      | ~ v4_relat_1(B_353,k2_zfmisc_1(A_354,B_355))
      | ~ v1_relat_1(B_353) ) ),
    inference(resolution,[status(thm)],[c_202,c_142])).

tff(c_3735,plain,(
    ! [A_6] :
      ( v1_relat_1(k1_relat_1(A_6))
      | ~ v1_relat_1(A_6)
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3265,c_3712])).

tff(c_3857,plain,
    ( v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3851,c_3735])).

tff(c_3873,plain,
    ( v1_relat_1('#skF_1')
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_3857])).

tff(c_3887,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3873])).

tff(c_6027,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6000,c_3887])).

tff(c_5973,plain,(
    ! [A_452] :
      ( ~ r1_tarski('#skF_1',A_452)
      | m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_5013])).

tff(c_6072,plain,(
    ! [A_452] :
      ( ~ r1_tarski('#skF_1',A_452)
      | m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6000,c_5973])).

tff(c_6075,plain,(
    ! [A_508] : ~ r1_tarski('#skF_1',A_508) ),
    inference(splitLeft,[status(thm)],[c_6072])).

tff(c_6080,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_6075])).

tff(c_6081,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6072])).

tff(c_6335,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_6081,c_16])).

tff(c_6339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6027,c_6335])).

tff(c_6341,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3873])).

tff(c_3266,plain,(
    ! [A_291,A_292] :
      ( v4_relat_1(A_291,A_292)
      | ~ r1_tarski(A_291,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_3261])).

tff(c_219,plain,(
    ! [B_51] :
      ( k1_relat_1(B_51) = k1_xboole_0
      | ~ v4_relat_1(B_51,k1_xboole_0)
      | ~ v1_relat_1(B_51) ) ),
    inference(resolution,[status(thm)],[c_202,c_116])).

tff(c_3271,plain,(
    ! [A_291] :
      ( k1_relat_1(A_291) = k1_xboole_0
      | ~ v1_relat_1(A_291)
      | ~ r1_tarski(A_291,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3266,c_219])).

tff(c_6357,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6341,c_3271])).

tff(c_6376,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_3851,c_6357])).

tff(c_144,plain,(
    ! [C_42] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_130])).

tff(c_149,plain,(
    ! [A_6] :
      ( v1_relat_1(A_6)
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_144])).

tff(c_218,plain,(
    ! [B_51] :
      ( v1_relat_1(k1_relat_1(B_51))
      | ~ v4_relat_1(B_51,k1_xboole_0)
      | ~ v1_relat_1(B_51) ) ),
    inference(resolution,[status(thm)],[c_202,c_149])).

tff(c_3866,plain,
    ( v1_relat_1('#skF_1')
    | ~ v4_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3851,c_218])).

tff(c_3879,plain,
    ( v1_relat_1('#skF_1')
    | ~ v4_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_3866])).

tff(c_6342,plain,(
    ~ v4_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3879])).

tff(c_6384,plain,(
    ~ v4_relat_1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6376,c_6342])).

tff(c_6426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3260,c_6384])).

tff(c_6428,plain,(
    v4_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3879])).

tff(c_6460,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6428,c_219])).

tff(c_6463,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_3851,c_6460])).

tff(c_6503,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6463,c_8])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6501,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6463,c_6463,c_14])).

tff(c_91,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_95,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_91])).

tff(c_110,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_95,c_101])).

tff(c_3272,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_6671,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6501,c_3272])).

tff(c_6676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6503,c_6671])).

tff(c_6677,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6690,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6677,c_10])).

tff(c_6698,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_6690])).

tff(c_6705,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6698])).

tff(c_6680,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6677,c_54])).

tff(c_6839,plain,(
    ! [A_547,B_548,C_549] :
      ( k1_relset_1(A_547,B_548,C_549) = k1_relat_1(C_549)
      | ~ m1_subset_1(C_549,k1_zfmisc_1(k2_zfmisc_1(A_547,B_548))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6894,plain,(
    ! [C_556] :
      ( k1_relset_1('#skF_1','#skF_2',C_556) = k1_relat_1(C_556)
      | ~ m1_subset_1(C_556,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6677,c_6839])).

tff(c_6902,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6680,c_6894])).

tff(c_7828,plain,(
    ! [B_676,A_677,C_678] :
      ( k1_xboole_0 = B_676
      | k1_relset_1(A_677,B_676,C_678) = A_677
      | ~ v1_funct_2(C_678,A_677,B_676)
      | ~ m1_subset_1(C_678,k1_zfmisc_1(k2_zfmisc_1(A_677,B_676))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_7834,plain,(
    ! [C_678] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_678) = '#skF_1'
      | ~ v1_funct_2(C_678,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_678,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6677,c_7828])).

tff(c_8109,plain,(
    ! [C_682] :
      ( k1_relset_1('#skF_1','#skF_2',C_682) = '#skF_1'
      | ~ v1_funct_2(C_682,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_682,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_7834])).

tff(c_8112,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_6680,c_8109])).

tff(c_8119,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6902,c_8112])).

tff(c_6980,plain,(
    ! [A_564,B_565,C_566] :
      ( k2_relset_1(A_564,B_565,C_566) = k2_relat_1(C_566)
      | ~ m1_subset_1(C_566,k1_zfmisc_1(k2_zfmisc_1(A_564,B_565))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7025,plain,(
    ! [C_570] :
      ( k2_relset_1('#skF_1','#skF_2',C_570) = k2_relat_1(C_570)
      | ~ m1_subset_1(C_570,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6677,c_6980])).

tff(c_7028,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6680,c_7025])).

tff(c_7034,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3224,c_7028])).

tff(c_7514,plain,(
    ! [C_631,A_632,B_633] :
      ( m1_subset_1(C_631,k1_zfmisc_1(k2_zfmisc_1(A_632,B_633)))
      | ~ r1_tarski(k2_relat_1(C_631),B_633)
      | ~ r1_tarski(k1_relat_1(C_631),A_632)
      | ~ v1_relat_1(C_631) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8600,plain,(
    ! [C_712,A_713,B_714] :
      ( r1_tarski(C_712,k2_zfmisc_1(A_713,B_714))
      | ~ r1_tarski(k2_relat_1(C_712),B_714)
      | ~ r1_tarski(k1_relat_1(C_712),A_713)
      | ~ v1_relat_1(C_712) ) ),
    inference(resolution,[status(thm)],[c_7514,c_16])).

tff(c_8970,plain,(
    ! [C_740,A_741] :
      ( r1_tarski(C_740,k2_zfmisc_1(A_741,k2_relat_1(C_740)))
      | ~ r1_tarski(k1_relat_1(C_740),A_741)
      | ~ v1_relat_1(C_740) ) ),
    inference(resolution,[status(thm)],[c_6,c_8600])).

tff(c_9020,plain,(
    ! [A_741] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_741,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_741)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7034,c_8970])).

tff(c_9041,plain,(
    ! [A_741] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_741,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_741) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_8119,c_9020])).

tff(c_9557,plain,(
    ! [B_750,A_751,A_752] :
      ( k1_xboole_0 = B_750
      | k1_relset_1(A_751,B_750,A_752) = A_751
      | ~ v1_funct_2(A_752,A_751,B_750)
      | ~ r1_tarski(A_752,k2_zfmisc_1(A_751,B_750)) ) ),
    inference(resolution,[status(thm)],[c_18,c_7828])).

tff(c_9588,plain,(
    ! [A_741] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1(A_741,'#skF_3','#skF_4') = A_741
      | ~ v1_funct_2('#skF_4',A_741,'#skF_3')
      | ~ r1_tarski('#skF_1',A_741) ) ),
    inference(resolution,[status(thm)],[c_9041,c_9557])).

tff(c_9897,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_9588])).

tff(c_8469,plain,(
    ! [C_704,A_705] :
      ( m1_subset_1(C_704,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_704),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_704),A_705)
      | ~ v1_relat_1(C_704) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_7514])).

tff(c_8471,plain,(
    ! [A_705] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_705)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7034,c_8469])).

tff(c_8473,plain,(
    ! [A_705] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski('#skF_1',A_705) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_8119,c_8471])).

tff(c_8556,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_8473])).

tff(c_9921,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9897,c_8556])).

tff(c_9979,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9921])).

tff(c_9981,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9588])).

tff(c_8602,plain,(
    ! [A_713,B_714] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_713,B_714))
      | ~ r1_tarski('#skF_3',B_714)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_713)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7034,c_8600])).

tff(c_8738,plain,(
    ! [A_721,B_722] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_721,B_722))
      | ~ r1_tarski('#skF_3',B_722)
      | ~ r1_tarski('#skF_1',A_721) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_8119,c_8602])).

tff(c_6853,plain,(
    ! [A_547,B_548,A_6] :
      ( k1_relset_1(A_547,B_548,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_547,B_548)) ) ),
    inference(resolution,[status(thm)],[c_18,c_6839])).

tff(c_8741,plain,(
    ! [A_721,B_722] :
      ( k1_relset_1(A_721,B_722,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_3',B_722)
      | ~ r1_tarski('#skF_1',A_721) ) ),
    inference(resolution,[status(thm)],[c_8738,c_6853])).

tff(c_8848,plain,(
    ! [A_725,B_726] :
      ( k1_relset_1(A_725,B_726,'#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_3',B_726)
      | ~ r1_tarski('#skF_1',A_725) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8119,c_8741])).

tff(c_8853,plain,(
    ! [A_727] :
      ( k1_relset_1(A_727,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_727) ) ),
    inference(resolution,[status(thm)],[c_6,c_8848])).

tff(c_8858,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_8853])).

tff(c_34,plain,(
    ! [C_24,A_22,B_23] :
      ( m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ r1_tarski(k2_relat_1(C_24),B_23)
      | ~ r1_tarski(k1_relat_1(C_24),A_22)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_7670,plain,(
    ! [B_653,C_654,A_655] :
      ( k1_xboole_0 = B_653
      | v1_funct_2(C_654,A_655,B_653)
      | k1_relset_1(A_655,B_653,C_654) != A_655
      | ~ m1_subset_1(C_654,k1_zfmisc_1(k2_zfmisc_1(A_655,B_653))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10029,plain,(
    ! [B_771,C_772,A_773] :
      ( k1_xboole_0 = B_771
      | v1_funct_2(C_772,A_773,B_771)
      | k1_relset_1(A_773,B_771,C_772) != A_773
      | ~ r1_tarski(k2_relat_1(C_772),B_771)
      | ~ r1_tarski(k1_relat_1(C_772),A_773)
      | ~ v1_relat_1(C_772) ) ),
    inference(resolution,[status(thm)],[c_34,c_7670])).

tff(c_10034,plain,(
    ! [B_771,A_773] :
      ( k1_xboole_0 = B_771
      | v1_funct_2('#skF_4',A_773,B_771)
      | k1_relset_1(A_773,B_771,'#skF_4') != A_773
      | ~ r1_tarski('#skF_3',B_771)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_773)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7034,c_10029])).

tff(c_10160,plain,(
    ! [B_776,A_777] :
      ( k1_xboole_0 = B_776
      | v1_funct_2('#skF_4',A_777,B_776)
      | k1_relset_1(A_777,B_776,'#skF_4') != A_777
      | ~ r1_tarski('#skF_3',B_776)
      | ~ r1_tarski('#skF_1',A_777) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_8119,c_10034])).

tff(c_10173,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_10160,c_161])).

tff(c_10183,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_8858,c_10173])).

tff(c_10185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9981,c_10183])).

tff(c_10187,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_8473])).

tff(c_10213,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10187,c_116])).

tff(c_7220,plain,(
    ! [B_595,A_596,B_597] :
      ( v1_relat_1(k1_relat_1(B_595))
      | ~ v4_relat_1(B_595,k2_zfmisc_1(A_596,B_597))
      | ~ v1_relat_1(B_595) ) ),
    inference(resolution,[status(thm)],[c_202,c_142])).

tff(c_7245,plain,(
    ! [A_6] :
      ( v1_relat_1(k1_relat_1(A_6))
      | ~ v1_relat_1(A_6)
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3265,c_7220])).

tff(c_8152,plain,
    ( v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8119,c_7245])).

tff(c_8192,plain,
    ( v1_relat_1('#skF_1')
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_8152])).

tff(c_8210,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_8192])).

tff(c_10226,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10213,c_8210])).

tff(c_10559,plain,(
    ! [A_793] : k2_zfmisc_1(A_793,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10213,c_10213,c_12])).

tff(c_10272,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10213,c_8])).

tff(c_10280,plain,(
    ! [C_778,A_779,B_780] :
      ( r1_tarski(C_778,k2_zfmisc_1(A_779,B_780))
      | ~ r1_tarski(k2_relat_1(C_778),B_780)
      | ~ r1_tarski(k1_relat_1(C_778),A_779)
      | ~ v1_relat_1(C_778) ) ),
    inference(resolution,[status(thm)],[c_7514,c_16])).

tff(c_10282,plain,(
    ! [A_779,B_780] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_779,B_780))
      | ~ r1_tarski('#skF_3',B_780)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_779)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7034,c_10280])).

tff(c_10287,plain,(
    ! [A_779,B_780] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_779,B_780))
      | ~ r1_tarski('#skF_3',B_780)
      | ~ r1_tarski('#skF_1',A_779) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_8119,c_10282])).

tff(c_10344,plain,(
    ! [A_779,B_780] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_779,B_780))
      | ~ r1_tarski('#skF_1',A_779) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10272,c_10287])).

tff(c_10567,plain,(
    ! [A_793] :
      ( r1_tarski('#skF_4','#skF_3')
      | ~ r1_tarski('#skF_1',A_793) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10559,c_10344])).

tff(c_10729,plain,(
    ! [A_794] : ~ r1_tarski('#skF_1',A_794) ),
    inference(negUnitSimplification,[status(thm)],[c_10226,c_10567])).

tff(c_10734,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_10729])).

tff(c_10736,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_8192])).

tff(c_10762,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10736,c_116])).

tff(c_10781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6705,c_10762])).

tff(c_10783,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6698])).

tff(c_10782,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6698])).

tff(c_10801,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10783,c_10782])).

tff(c_10796,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10782,c_8])).

tff(c_10818,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10801,c_10796])).

tff(c_11119,plain,(
    ! [A_842] :
      ( k1_relat_1(A_842) = '#skF_4'
      | ~ v1_relat_1(A_842)
      | ~ r1_tarski(A_842,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10783,c_10783,c_3271])).

tff(c_11123,plain,
    ( k1_relat_1('#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10818,c_11119])).

tff(c_11134,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_11123])).

tff(c_10794,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10782,c_10782,c_14])).

tff(c_10874,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10801,c_10801,c_10794])).

tff(c_11010,plain,(
    ! [A_819,B_820,C_821] :
      ( k1_relset_1(A_819,B_820,C_821) = k1_relat_1(C_821)
      | ~ m1_subset_1(C_821,k1_zfmisc_1(k2_zfmisc_1(A_819,B_820))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_11288,plain,(
    ! [B_858,C_859] :
      ( k1_relset_1('#skF_4',B_858,C_859) = k1_relat_1(C_859)
      | ~ m1_subset_1(C_859,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10874,c_11010])).

tff(c_11290,plain,(
    ! [B_858] : k1_relset_1('#skF_4',B_858,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6680,c_11288])).

tff(c_11295,plain,(
    ! [B_858] : k1_relset_1('#skF_4',B_858,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11134,c_11290])).

tff(c_40,plain,(
    ! [C_27,B_26] :
      ( v1_funct_2(C_27,k1_xboole_0,B_26)
      | k1_relset_1(k1_xboole_0,B_26,C_27) != k1_xboole_0
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_62,plain,(
    ! [C_27,B_26] :
      ( v1_funct_2(C_27,k1_xboole_0,B_26)
      | k1_relset_1(k1_xboole_0,B_26,C_27) != k1_xboole_0
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_40])).

tff(c_11298,plain,(
    ! [C_860,B_861] :
      ( v1_funct_2(C_860,'#skF_4',B_861)
      | k1_relset_1('#skF_4',B_861,C_860) != '#skF_4'
      | ~ m1_subset_1(C_860,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10783,c_10783,c_10783,c_10783,c_62])).

tff(c_11304,plain,(
    ! [B_861] :
      ( v1_funct_2('#skF_4','#skF_4',B_861)
      | k1_relset_1('#skF_4',B_861,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_6680,c_11298])).

tff(c_11315,plain,(
    ! [B_861] : v1_funct_2('#skF_4','#skF_4',B_861) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11295,c_11304])).

tff(c_10811,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10801,c_161])).

tff(c_11319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11315,c_10811])).

tff(c_11320,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_11795,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11780,c_11320])).

tff(c_11814,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_11543,c_11795])).

tff(c_11819,plain,
    ( ~ v4_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_11814])).

tff(c_11823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_11383,c_11819])).

tff(c_11824,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_11826,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11824,c_8])).

tff(c_11838,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11824,c_11824,c_12])).

tff(c_11825,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_11831,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11824,c_11825])).

tff(c_11862,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11838,c_11831,c_54])).

tff(c_11867,plain,(
    ! [A_941,B_942] :
      ( r1_tarski(A_941,B_942)
      | ~ m1_subset_1(A_941,k1_zfmisc_1(B_942)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_11875,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_11862,c_11867])).

tff(c_11876,plain,(
    ! [B_943,A_944] :
      ( B_943 = A_944
      | ~ r1_tarski(B_943,A_944)
      | ~ r1_tarski(A_944,B_943) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_11878,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_11875,c_11876])).

tff(c_11887,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11826,c_11878])).

tff(c_11897,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11887,c_11862])).

tff(c_11900,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11887,c_11887,c_11838])).

tff(c_11964,plain,(
    ! [C_951,A_952,B_953] :
      ( v1_relat_1(C_951)
      | ~ m1_subset_1(C_951,k1_zfmisc_1(k2_zfmisc_1(A_952,B_953))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_11977,plain,(
    ! [C_954] :
      ( v1_relat_1(C_954)
      | ~ m1_subset_1(C_954,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11900,c_11964])).

tff(c_11985,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11897,c_11977])).

tff(c_11846,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11824,c_11824,c_14])).

tff(c_11899,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11887,c_11887,c_11846])).

tff(c_12074,plain,(
    ! [C_973,A_974,B_975] :
      ( v4_relat_1(C_973,A_974)
      | ~ m1_subset_1(C_973,k1_zfmisc_1(k2_zfmisc_1(A_974,B_975))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12099,plain,(
    ! [A_984,A_985,B_986] :
      ( v4_relat_1(A_984,A_985)
      | ~ r1_tarski(A_984,k2_zfmisc_1(A_985,B_986)) ) ),
    inference(resolution,[status(thm)],[c_18,c_12074])).

tff(c_12116,plain,(
    ! [A_985,B_986] : v4_relat_1(k2_zfmisc_1(A_985,B_986),A_985) ),
    inference(resolution,[status(thm)],[c_6,c_12099])).

tff(c_12144,plain,(
    ! [B_992,A_993] :
      ( r1_tarski(k1_relat_1(B_992),A_993)
      | ~ v4_relat_1(B_992,A_993)
      | ~ v1_relat_1(B_992) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_11889,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_11826,c_11876])).

tff(c_11950,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ r1_tarski(A_3,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11887,c_11887,c_11889])).

tff(c_12186,plain,(
    ! [B_996] :
      ( k1_relat_1(B_996) = '#skF_4'
      | ~ v4_relat_1(B_996,'#skF_4')
      | ~ v1_relat_1(B_996) ) ),
    inference(resolution,[status(thm)],[c_12144,c_11950])).

tff(c_12190,plain,(
    ! [B_986] :
      ( k1_relat_1(k2_zfmisc_1('#skF_4',B_986)) = '#skF_4'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_4',B_986)) ) ),
    inference(resolution,[status(thm)],[c_12116,c_12186])).

tff(c_12201,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11985,c_11899,c_11899,c_12190])).

tff(c_11901,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11887,c_11826])).

tff(c_12426,plain,(
    ! [A_1027,B_1028,C_1029] :
      ( k1_relset_1(A_1027,B_1028,C_1029) = k1_relat_1(C_1029)
      | ~ m1_subset_1(C_1029,k1_zfmisc_1(k2_zfmisc_1(A_1027,B_1028))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_12539,plain,(
    ! [A_1044,B_1045,A_1046] :
      ( k1_relset_1(A_1044,B_1045,A_1046) = k1_relat_1(A_1046)
      | ~ r1_tarski(A_1046,k2_zfmisc_1(A_1044,B_1045)) ) ),
    inference(resolution,[status(thm)],[c_18,c_12426])).

tff(c_12553,plain,(
    ! [A_1044,B_1045] : k1_relset_1(A_1044,B_1045,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11901,c_12539])).

tff(c_12560,plain,(
    ! [A_1044,B_1045] : k1_relset_1(A_1044,B_1045,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12201,c_12553])).

tff(c_11903,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11887,c_11824])).

tff(c_12694,plain,(
    ! [C_1062,B_1063] :
      ( v1_funct_2(C_1062,'#skF_4',B_1063)
      | k1_relset_1('#skF_4',B_1063,C_1062) != '#skF_4'
      | ~ m1_subset_1(C_1062,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11903,c_11903,c_11903,c_11903,c_62])).

tff(c_12696,plain,(
    ! [B_1063] :
      ( v1_funct_2('#skF_4','#skF_4',B_1063)
      | k1_relset_1('#skF_4',B_1063,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_11897,c_12694])).

tff(c_12702,plain,(
    ! [B_1063] : v1_funct_2('#skF_4','#skF_4',B_1063) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12560,c_12696])).

tff(c_11865,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11862,c_11846,c_60])).

tff(c_11895,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11887,c_11865])).

tff(c_12707,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12702,c_11895])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:36:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.25/2.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.25/2.93  
% 8.25/2.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.25/2.94  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.25/2.94  
% 8.25/2.94  %Foreground sorts:
% 8.25/2.94  
% 8.25/2.94  
% 8.25/2.94  %Background operators:
% 8.25/2.94  
% 8.25/2.94  
% 8.25/2.94  %Foreground operators:
% 8.25/2.94  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.25/2.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.25/2.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.25/2.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.25/2.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.25/2.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.25/2.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.25/2.94  tff('#skF_2', type, '#skF_2': $i).
% 8.25/2.94  tff('#skF_3', type, '#skF_3': $i).
% 8.25/2.94  tff('#skF_1', type, '#skF_1': $i).
% 8.25/2.94  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.25/2.94  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.25/2.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.25/2.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.25/2.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.25/2.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.25/2.94  tff('#skF_4', type, '#skF_4': $i).
% 8.25/2.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.25/2.94  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.25/2.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.25/2.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.25/2.94  
% 8.55/2.97  tff(f_113, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 8.55/2.97  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.55/2.97  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.55/2.97  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 8.55/2.97  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.55/2.97  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 8.55/2.97  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.55/2.97  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.55/2.97  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.55/2.97  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.55/2.97  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.55/2.97  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.55/2.97  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.55/2.97  tff(c_130, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.55/2.97  tff(c_143, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_130])).
% 8.55/2.97  tff(c_11368, plain, (![C_870, A_871, B_872]: (v4_relat_1(C_870, A_871) | ~m1_subset_1(C_870, k1_zfmisc_1(k2_zfmisc_1(A_871, B_872))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.55/2.97  tff(c_11383, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_11368])).
% 8.55/2.97  tff(c_22, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(B_9), A_8) | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.55/2.97  tff(c_11526, plain, (![A_895, B_896, C_897]: (k2_relset_1(A_895, B_896, C_897)=k2_relat_1(C_897) | ~m1_subset_1(C_897, k1_zfmisc_1(k2_zfmisc_1(A_895, B_896))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.55/2.97  tff(c_11541, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_11526])).
% 8.55/2.97  tff(c_52, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.55/2.97  tff(c_11543, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11541, c_52])).
% 8.55/2.97  tff(c_11780, plain, (![C_933, A_934, B_935]: (m1_subset_1(C_933, k1_zfmisc_1(k2_zfmisc_1(A_934, B_935))) | ~r1_tarski(k2_relat_1(C_933), B_935) | ~r1_tarski(k1_relat_1(C_933), A_934) | ~v1_relat_1(C_933))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.55/2.97  tff(c_50, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.55/2.97  tff(c_68, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_50])).
% 8.55/2.97  tff(c_56, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.55/2.97  tff(c_3370, plain, (![A_303, B_304, C_305]: (k1_relset_1(A_303, B_304, C_305)=k1_relat_1(C_305) | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(A_303, B_304))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.55/2.97  tff(c_3385, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_3370])).
% 8.55/2.97  tff(c_3829, plain, (![B_370, A_371, C_372]: (k1_xboole_0=B_370 | k1_relset_1(A_371, B_370, C_372)=A_371 | ~v1_funct_2(C_372, A_371, B_370) | ~m1_subset_1(C_372, k1_zfmisc_1(k2_zfmisc_1(A_371, B_370))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.55/2.97  tff(c_3839, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_3829])).
% 8.55/2.97  tff(c_3850, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3385, c_3839])).
% 8.55/2.97  tff(c_3851, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_68, c_3850])).
% 8.55/2.97  tff(c_3245, plain, (![C_286, A_287, B_288]: (v4_relat_1(C_286, A_287) | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.55/2.97  tff(c_3260, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_3245])).
% 8.55/2.97  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.55/2.97  tff(c_370, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.55/2.97  tff(c_385, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_370])).
% 8.55/2.97  tff(c_655, plain, (![B_117, A_118, C_119]: (k1_xboole_0=B_117 | k1_relset_1(A_118, B_117, C_119)=A_118 | ~v1_funct_2(C_119, A_118, B_117) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.55/2.97  tff(c_665, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_655])).
% 8.55/2.97  tff(c_676, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_385, c_665])).
% 8.55/2.97  tff(c_677, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_68, c_676])).
% 8.55/2.97  tff(c_312, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.55/2.97  tff(c_327, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_312])).
% 8.55/2.97  tff(c_362, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_327, c_52])).
% 8.55/2.97  tff(c_528, plain, (![C_99, A_100, B_101]: (m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~r1_tarski(k2_relat_1(C_99), B_101) | ~r1_tarski(k1_relat_1(C_99), A_100) | ~v1_relat_1(C_99))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.55/2.97  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.55/2.97  tff(c_2514, plain, (![C_246, A_247, B_248]: (r1_tarski(C_246, k2_zfmisc_1(A_247, B_248)) | ~r1_tarski(k2_relat_1(C_246), B_248) | ~r1_tarski(k1_relat_1(C_246), A_247) | ~v1_relat_1(C_246))), inference(resolution, [status(thm)], [c_528, c_16])).
% 8.55/2.97  tff(c_2516, plain, (![A_247]: (r1_tarski('#skF_4', k2_zfmisc_1(A_247, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_247) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_362, c_2514])).
% 8.55/2.97  tff(c_2524, plain, (![A_249]: (r1_tarski('#skF_4', k2_zfmisc_1(A_249, '#skF_3')) | ~r1_tarski('#skF_1', A_249))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_677, c_2516])).
% 8.55/2.97  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.55/2.97  tff(c_384, plain, (![A_78, B_79, A_6]: (k1_relset_1(A_78, B_79, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_78, B_79)))), inference(resolution, [status(thm)], [c_18, c_370])).
% 8.55/2.97  tff(c_2530, plain, (![A_249]: (k1_relset_1(A_249, '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', A_249))), inference(resolution, [status(thm)], [c_2524, c_384])).
% 8.55/2.97  tff(c_2556, plain, (![A_250]: (k1_relset_1(A_250, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_250))), inference(demodulation, [status(thm), theory('equality')], [c_677, c_2530])).
% 8.55/2.97  tff(c_2561, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_2556])).
% 8.55/2.97  tff(c_2522, plain, (![A_247]: (r1_tarski('#skF_4', k2_zfmisc_1(A_247, '#skF_3')) | ~r1_tarski('#skF_1', A_247))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_677, c_2516])).
% 8.55/2.97  tff(c_871, plain, (![B_137, C_138, A_139]: (k1_xboole_0=B_137 | v1_funct_2(C_138, A_139, B_137) | k1_relset_1(A_139, B_137, C_138)!=A_139 | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_139, B_137))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.55/2.97  tff(c_2576, plain, (![B_252, A_253, A_254]: (k1_xboole_0=B_252 | v1_funct_2(A_253, A_254, B_252) | k1_relset_1(A_254, B_252, A_253)!=A_254 | ~r1_tarski(A_253, k2_zfmisc_1(A_254, B_252)))), inference(resolution, [status(thm)], [c_18, c_871])).
% 8.55/2.97  tff(c_2601, plain, (![A_247]: (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', A_247, '#skF_3') | k1_relset_1(A_247, '#skF_3', '#skF_4')!=A_247 | ~r1_tarski('#skF_1', A_247))), inference(resolution, [status(thm)], [c_2522, c_2576])).
% 8.55/2.97  tff(c_3099, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2601])).
% 8.55/2.97  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.55/2.97  tff(c_3174, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3099, c_8])).
% 8.55/2.97  tff(c_101, plain, (![B_36, A_37]: (B_36=A_37 | ~r1_tarski(B_36, A_37) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.55/2.97  tff(c_111, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_101])).
% 8.55/2.97  tff(c_222, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_111])).
% 8.55/2.97  tff(c_361, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_222])).
% 8.55/2.97  tff(c_3209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3174, c_361])).
% 8.55/2.97  tff(c_3212, plain, (![A_281]: (v1_funct_2('#skF_4', A_281, '#skF_3') | k1_relset_1(A_281, '#skF_3', '#skF_4')!=A_281 | ~r1_tarski('#skF_1', A_281))), inference(splitRight, [status(thm)], [c_2601])).
% 8.55/2.97  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.55/2.97  tff(c_48, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.55/2.97  tff(c_60, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_48])).
% 8.55/2.97  tff(c_161, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_60])).
% 8.55/2.97  tff(c_3218, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3212, c_161])).
% 8.55/2.97  tff(c_3223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2561, c_3218])).
% 8.55/2.97  tff(c_3224, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_111])).
% 8.55/2.97  tff(c_3436, plain, (![A_316, B_317, C_318]: (k2_relset_1(A_316, B_317, C_318)=k2_relat_1(C_318) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(A_316, B_317))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.55/2.97  tff(c_3443, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_3436])).
% 8.55/2.97  tff(c_3452, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3224, c_3443])).
% 8.55/2.97  tff(c_3542, plain, (![C_330, A_331, B_332]: (m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(A_331, B_332))) | ~r1_tarski(k2_relat_1(C_330), B_332) | ~r1_tarski(k1_relat_1(C_330), A_331) | ~v1_relat_1(C_330))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.55/2.97  tff(c_5433, plain, (![C_475, A_476, B_477]: (r1_tarski(C_475, k2_zfmisc_1(A_476, B_477)) | ~r1_tarski(k2_relat_1(C_475), B_477) | ~r1_tarski(k1_relat_1(C_475), A_476) | ~v1_relat_1(C_475))), inference(resolution, [status(thm)], [c_3542, c_16])).
% 8.55/2.97  tff(c_5435, plain, (![A_476, B_477]: (r1_tarski('#skF_4', k2_zfmisc_1(A_476, B_477)) | ~r1_tarski('#skF_3', B_477) | ~r1_tarski(k1_relat_1('#skF_4'), A_476) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3452, c_5433])).
% 8.55/2.97  tff(c_5442, plain, (![A_478, B_479]: (r1_tarski('#skF_4', k2_zfmisc_1(A_478, B_479)) | ~r1_tarski('#skF_3', B_479) | ~r1_tarski('#skF_1', A_478))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_3851, c_5435])).
% 8.55/2.97  tff(c_3384, plain, (![A_303, B_304, A_6]: (k1_relset_1(A_303, B_304, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_303, B_304)))), inference(resolution, [status(thm)], [c_18, c_3370])).
% 8.55/2.97  tff(c_5445, plain, (![A_478, B_479]: (k1_relset_1(A_478, B_479, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_3', B_479) | ~r1_tarski('#skF_1', A_478))), inference(resolution, [status(thm)], [c_5442, c_3384])).
% 8.55/2.97  tff(c_5477, plain, (![A_480, B_481]: (k1_relset_1(A_480, B_481, '#skF_4')='#skF_1' | ~r1_tarski('#skF_3', B_481) | ~r1_tarski('#skF_1', A_480))), inference(demodulation, [status(thm), theory('equality')], [c_3851, c_5445])).
% 8.55/2.97  tff(c_5482, plain, (![A_482]: (k1_relset_1(A_482, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_482))), inference(resolution, [status(thm)], [c_6, c_5477])).
% 8.55/2.97  tff(c_5487, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_5482])).
% 8.55/2.97  tff(c_5516, plain, (![C_489, A_490]: (r1_tarski(C_489, k2_zfmisc_1(A_490, k2_relat_1(C_489))) | ~r1_tarski(k1_relat_1(C_489), A_490) | ~v1_relat_1(C_489))), inference(resolution, [status(thm)], [c_6, c_5433])).
% 8.55/2.97  tff(c_5563, plain, (![A_490]: (r1_tarski('#skF_4', k2_zfmisc_1(A_490, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_490) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3452, c_5516])).
% 8.55/2.97  tff(c_5583, plain, (![A_490]: (r1_tarski('#skF_4', k2_zfmisc_1(A_490, '#skF_3')) | ~r1_tarski('#skF_1', A_490))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_3851, c_5563])).
% 8.55/2.97  tff(c_3674, plain, (![B_348, C_349, A_350]: (k1_xboole_0=B_348 | v1_funct_2(C_349, A_350, B_348) | k1_relset_1(A_350, B_348, C_349)!=A_350 | ~m1_subset_1(C_349, k1_zfmisc_1(k2_zfmisc_1(A_350, B_348))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.55/2.97  tff(c_5777, plain, (![B_499, A_500, A_501]: (k1_xboole_0=B_499 | v1_funct_2(A_500, A_501, B_499) | k1_relset_1(A_501, B_499, A_500)!=A_501 | ~r1_tarski(A_500, k2_zfmisc_1(A_501, B_499)))), inference(resolution, [status(thm)], [c_18, c_3674])).
% 8.55/2.97  tff(c_5808, plain, (![A_490]: (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', A_490, '#skF_3') | k1_relset_1(A_490, '#skF_3', '#skF_4')!=A_490 | ~r1_tarski('#skF_1', A_490))), inference(resolution, [status(thm)], [c_5583, c_5777])).
% 8.55/2.97  tff(c_5881, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_5808])).
% 8.55/2.97  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.55/2.97  tff(c_5009, plain, (![C_451, A_452]: (m1_subset_1(C_451, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_451), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_451), A_452) | ~v1_relat_1(C_451))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3542])).
% 8.55/2.97  tff(c_5011, plain, (![A_452]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), A_452) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3452, c_5009])).
% 8.55/2.97  tff(c_5013, plain, (![A_452]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_1', A_452))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_3851, c_5011])).
% 8.55/2.97  tff(c_5014, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_5013])).
% 8.55/2.97  tff(c_5895, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5881, c_5014])).
% 8.55/2.97  tff(c_5958, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5895])).
% 8.55/2.97  tff(c_5961, plain, (![A_507]: (v1_funct_2('#skF_4', A_507, '#skF_3') | k1_relset_1(A_507, '#skF_3', '#skF_4')!=A_507 | ~r1_tarski('#skF_1', A_507))), inference(splitRight, [status(thm)], [c_5808])).
% 8.55/2.97  tff(c_5967, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_5961, c_161])).
% 8.55/2.97  tff(c_5972, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5487, c_5967])).
% 8.55/2.97  tff(c_5974, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_5013])).
% 8.55/2.97  tff(c_116, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_101])).
% 8.55/2.97  tff(c_6000, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_5974, c_116])).
% 8.55/2.97  tff(c_3261, plain, (![C_289, A_290]: (v4_relat_1(C_289, A_290) | ~m1_subset_1(C_289, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3245])).
% 8.55/2.97  tff(c_3265, plain, (![A_6, A_290]: (v4_relat_1(A_6, A_290) | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_3261])).
% 8.55/2.97  tff(c_202, plain, (![B_51, A_52]: (r1_tarski(k1_relat_1(B_51), A_52) | ~v4_relat_1(B_51, A_52) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.55/2.97  tff(c_142, plain, (![A_6, A_40, B_41]: (v1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_40, B_41)))), inference(resolution, [status(thm)], [c_18, c_130])).
% 8.55/2.97  tff(c_3712, plain, (![B_353, A_354, B_355]: (v1_relat_1(k1_relat_1(B_353)) | ~v4_relat_1(B_353, k2_zfmisc_1(A_354, B_355)) | ~v1_relat_1(B_353))), inference(resolution, [status(thm)], [c_202, c_142])).
% 8.55/2.97  tff(c_3735, plain, (![A_6]: (v1_relat_1(k1_relat_1(A_6)) | ~v1_relat_1(A_6) | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_3265, c_3712])).
% 8.55/2.97  tff(c_3857, plain, (v1_relat_1('#skF_1') | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3851, c_3735])).
% 8.55/2.97  tff(c_3873, plain, (v1_relat_1('#skF_1') | ~r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_143, c_3857])).
% 8.55/2.97  tff(c_3887, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3873])).
% 8.55/2.97  tff(c_6027, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6000, c_3887])).
% 8.55/2.97  tff(c_5973, plain, (![A_452]: (~r1_tarski('#skF_1', A_452) | m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_5013])).
% 8.55/2.97  tff(c_6072, plain, (![A_452]: (~r1_tarski('#skF_1', A_452) | m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_6000, c_5973])).
% 8.55/2.97  tff(c_6075, plain, (![A_508]: (~r1_tarski('#skF_1', A_508))), inference(splitLeft, [status(thm)], [c_6072])).
% 8.55/2.97  tff(c_6080, plain, $false, inference(resolution, [status(thm)], [c_6, c_6075])).
% 8.55/2.97  tff(c_6081, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_6072])).
% 8.55/2.97  tff(c_6335, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_6081, c_16])).
% 8.55/2.97  tff(c_6339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6027, c_6335])).
% 8.55/2.97  tff(c_6341, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_3873])).
% 8.55/2.97  tff(c_3266, plain, (![A_291, A_292]: (v4_relat_1(A_291, A_292) | ~r1_tarski(A_291, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_3261])).
% 8.55/2.97  tff(c_219, plain, (![B_51]: (k1_relat_1(B_51)=k1_xboole_0 | ~v4_relat_1(B_51, k1_xboole_0) | ~v1_relat_1(B_51))), inference(resolution, [status(thm)], [c_202, c_116])).
% 8.55/2.97  tff(c_3271, plain, (![A_291]: (k1_relat_1(A_291)=k1_xboole_0 | ~v1_relat_1(A_291) | ~r1_tarski(A_291, k1_xboole_0))), inference(resolution, [status(thm)], [c_3266, c_219])).
% 8.55/2.97  tff(c_6357, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6341, c_3271])).
% 8.55/2.97  tff(c_6376, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_3851, c_6357])).
% 8.55/2.97  tff(c_144, plain, (![C_42]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_130])).
% 8.55/2.97  tff(c_149, plain, (![A_6]: (v1_relat_1(A_6) | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_144])).
% 8.55/2.97  tff(c_218, plain, (![B_51]: (v1_relat_1(k1_relat_1(B_51)) | ~v4_relat_1(B_51, k1_xboole_0) | ~v1_relat_1(B_51))), inference(resolution, [status(thm)], [c_202, c_149])).
% 8.55/2.97  tff(c_3866, plain, (v1_relat_1('#skF_1') | ~v4_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3851, c_218])).
% 8.55/2.97  tff(c_3879, plain, (v1_relat_1('#skF_1') | ~v4_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_143, c_3866])).
% 8.55/2.97  tff(c_6342, plain, (~v4_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3879])).
% 8.55/2.97  tff(c_6384, plain, (~v4_relat_1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6376, c_6342])).
% 8.55/2.97  tff(c_6426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3260, c_6384])).
% 8.55/2.97  tff(c_6428, plain, (v4_relat_1('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_3879])).
% 8.55/2.97  tff(c_6460, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6428, c_219])).
% 8.55/2.97  tff(c_6463, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_3851, c_6460])).
% 8.55/2.97  tff(c_6503, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_6463, c_8])).
% 8.55/2.97  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.55/2.97  tff(c_6501, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6463, c_6463, c_14])).
% 8.55/2.97  tff(c_91, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.55/2.97  tff(c_95, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_91])).
% 8.55/2.97  tff(c_110, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_95, c_101])).
% 8.55/2.97  tff(c_3272, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_110])).
% 8.55/2.97  tff(c_6671, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6501, c_3272])).
% 8.55/2.97  tff(c_6676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6503, c_6671])).
% 8.55/2.97  tff(c_6677, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_4'), inference(splitRight, [status(thm)], [c_110])).
% 8.55/2.97  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.55/2.97  tff(c_6690, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6677, c_10])).
% 8.55/2.97  tff(c_6698, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_68, c_6690])).
% 8.55/2.97  tff(c_6705, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_6698])).
% 8.55/2.97  tff(c_6680, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6677, c_54])).
% 8.55/2.97  tff(c_6839, plain, (![A_547, B_548, C_549]: (k1_relset_1(A_547, B_548, C_549)=k1_relat_1(C_549) | ~m1_subset_1(C_549, k1_zfmisc_1(k2_zfmisc_1(A_547, B_548))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.55/2.97  tff(c_6894, plain, (![C_556]: (k1_relset_1('#skF_1', '#skF_2', C_556)=k1_relat_1(C_556) | ~m1_subset_1(C_556, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_6677, c_6839])).
% 8.55/2.97  tff(c_6902, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6680, c_6894])).
% 8.55/2.97  tff(c_7828, plain, (![B_676, A_677, C_678]: (k1_xboole_0=B_676 | k1_relset_1(A_677, B_676, C_678)=A_677 | ~v1_funct_2(C_678, A_677, B_676) | ~m1_subset_1(C_678, k1_zfmisc_1(k2_zfmisc_1(A_677, B_676))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.55/2.97  tff(c_7834, plain, (![C_678]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_678)='#skF_1' | ~v1_funct_2(C_678, '#skF_1', '#skF_2') | ~m1_subset_1(C_678, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_6677, c_7828])).
% 8.55/2.97  tff(c_8109, plain, (![C_682]: (k1_relset_1('#skF_1', '#skF_2', C_682)='#skF_1' | ~v1_funct_2(C_682, '#skF_1', '#skF_2') | ~m1_subset_1(C_682, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_68, c_7834])).
% 8.55/2.97  tff(c_8112, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_6680, c_8109])).
% 8.55/2.97  tff(c_8119, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_6902, c_8112])).
% 8.55/2.97  tff(c_6980, plain, (![A_564, B_565, C_566]: (k2_relset_1(A_564, B_565, C_566)=k2_relat_1(C_566) | ~m1_subset_1(C_566, k1_zfmisc_1(k2_zfmisc_1(A_564, B_565))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.55/2.97  tff(c_7025, plain, (![C_570]: (k2_relset_1('#skF_1', '#skF_2', C_570)=k2_relat_1(C_570) | ~m1_subset_1(C_570, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_6677, c_6980])).
% 8.55/2.97  tff(c_7028, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6680, c_7025])).
% 8.55/2.97  tff(c_7034, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3224, c_7028])).
% 8.55/2.97  tff(c_7514, plain, (![C_631, A_632, B_633]: (m1_subset_1(C_631, k1_zfmisc_1(k2_zfmisc_1(A_632, B_633))) | ~r1_tarski(k2_relat_1(C_631), B_633) | ~r1_tarski(k1_relat_1(C_631), A_632) | ~v1_relat_1(C_631))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.55/2.97  tff(c_8600, plain, (![C_712, A_713, B_714]: (r1_tarski(C_712, k2_zfmisc_1(A_713, B_714)) | ~r1_tarski(k2_relat_1(C_712), B_714) | ~r1_tarski(k1_relat_1(C_712), A_713) | ~v1_relat_1(C_712))), inference(resolution, [status(thm)], [c_7514, c_16])).
% 8.55/2.97  tff(c_8970, plain, (![C_740, A_741]: (r1_tarski(C_740, k2_zfmisc_1(A_741, k2_relat_1(C_740))) | ~r1_tarski(k1_relat_1(C_740), A_741) | ~v1_relat_1(C_740))), inference(resolution, [status(thm)], [c_6, c_8600])).
% 8.55/2.97  tff(c_9020, plain, (![A_741]: (r1_tarski('#skF_4', k2_zfmisc_1(A_741, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_741) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7034, c_8970])).
% 8.55/2.97  tff(c_9041, plain, (![A_741]: (r1_tarski('#skF_4', k2_zfmisc_1(A_741, '#skF_3')) | ~r1_tarski('#skF_1', A_741))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_8119, c_9020])).
% 8.55/2.97  tff(c_9557, plain, (![B_750, A_751, A_752]: (k1_xboole_0=B_750 | k1_relset_1(A_751, B_750, A_752)=A_751 | ~v1_funct_2(A_752, A_751, B_750) | ~r1_tarski(A_752, k2_zfmisc_1(A_751, B_750)))), inference(resolution, [status(thm)], [c_18, c_7828])).
% 8.55/2.97  tff(c_9588, plain, (![A_741]: (k1_xboole_0='#skF_3' | k1_relset_1(A_741, '#skF_3', '#skF_4')=A_741 | ~v1_funct_2('#skF_4', A_741, '#skF_3') | ~r1_tarski('#skF_1', A_741))), inference(resolution, [status(thm)], [c_9041, c_9557])).
% 8.55/2.97  tff(c_9897, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_9588])).
% 8.55/2.97  tff(c_8469, plain, (![C_704, A_705]: (m1_subset_1(C_704, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_704), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_704), A_705) | ~v1_relat_1(C_704))), inference(superposition, [status(thm), theory('equality')], [c_12, c_7514])).
% 8.55/2.97  tff(c_8471, plain, (![A_705]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), A_705) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7034, c_8469])).
% 8.55/2.97  tff(c_8473, plain, (![A_705]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_1', A_705))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_8119, c_8471])).
% 8.55/2.97  tff(c_8556, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_8473])).
% 8.55/2.97  tff(c_9921, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9897, c_8556])).
% 8.55/2.97  tff(c_9979, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_9921])).
% 8.55/2.97  tff(c_9981, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_9588])).
% 8.55/2.97  tff(c_8602, plain, (![A_713, B_714]: (r1_tarski('#skF_4', k2_zfmisc_1(A_713, B_714)) | ~r1_tarski('#skF_3', B_714) | ~r1_tarski(k1_relat_1('#skF_4'), A_713) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7034, c_8600])).
% 8.55/2.97  tff(c_8738, plain, (![A_721, B_722]: (r1_tarski('#skF_4', k2_zfmisc_1(A_721, B_722)) | ~r1_tarski('#skF_3', B_722) | ~r1_tarski('#skF_1', A_721))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_8119, c_8602])).
% 8.55/2.97  tff(c_6853, plain, (![A_547, B_548, A_6]: (k1_relset_1(A_547, B_548, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_547, B_548)))), inference(resolution, [status(thm)], [c_18, c_6839])).
% 8.55/2.97  tff(c_8741, plain, (![A_721, B_722]: (k1_relset_1(A_721, B_722, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_3', B_722) | ~r1_tarski('#skF_1', A_721))), inference(resolution, [status(thm)], [c_8738, c_6853])).
% 8.55/2.97  tff(c_8848, plain, (![A_725, B_726]: (k1_relset_1(A_725, B_726, '#skF_4')='#skF_1' | ~r1_tarski('#skF_3', B_726) | ~r1_tarski('#skF_1', A_725))), inference(demodulation, [status(thm), theory('equality')], [c_8119, c_8741])).
% 8.55/2.97  tff(c_8853, plain, (![A_727]: (k1_relset_1(A_727, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_727))), inference(resolution, [status(thm)], [c_6, c_8848])).
% 8.55/2.97  tff(c_8858, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_8853])).
% 8.55/2.97  tff(c_34, plain, (![C_24, A_22, B_23]: (m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~r1_tarski(k2_relat_1(C_24), B_23) | ~r1_tarski(k1_relat_1(C_24), A_22) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.55/2.97  tff(c_7670, plain, (![B_653, C_654, A_655]: (k1_xboole_0=B_653 | v1_funct_2(C_654, A_655, B_653) | k1_relset_1(A_655, B_653, C_654)!=A_655 | ~m1_subset_1(C_654, k1_zfmisc_1(k2_zfmisc_1(A_655, B_653))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.55/2.97  tff(c_10029, plain, (![B_771, C_772, A_773]: (k1_xboole_0=B_771 | v1_funct_2(C_772, A_773, B_771) | k1_relset_1(A_773, B_771, C_772)!=A_773 | ~r1_tarski(k2_relat_1(C_772), B_771) | ~r1_tarski(k1_relat_1(C_772), A_773) | ~v1_relat_1(C_772))), inference(resolution, [status(thm)], [c_34, c_7670])).
% 8.55/2.97  tff(c_10034, plain, (![B_771, A_773]: (k1_xboole_0=B_771 | v1_funct_2('#skF_4', A_773, B_771) | k1_relset_1(A_773, B_771, '#skF_4')!=A_773 | ~r1_tarski('#skF_3', B_771) | ~r1_tarski(k1_relat_1('#skF_4'), A_773) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7034, c_10029])).
% 8.55/2.97  tff(c_10160, plain, (![B_776, A_777]: (k1_xboole_0=B_776 | v1_funct_2('#skF_4', A_777, B_776) | k1_relset_1(A_777, B_776, '#skF_4')!=A_777 | ~r1_tarski('#skF_3', B_776) | ~r1_tarski('#skF_1', A_777))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_8119, c_10034])).
% 8.55/2.97  tff(c_10173, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_10160, c_161])).
% 8.55/2.97  tff(c_10183, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_8858, c_10173])).
% 8.55/2.97  tff(c_10185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9981, c_10183])).
% 8.55/2.97  tff(c_10187, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_8473])).
% 8.55/2.97  tff(c_10213, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_10187, c_116])).
% 8.55/2.97  tff(c_7220, plain, (![B_595, A_596, B_597]: (v1_relat_1(k1_relat_1(B_595)) | ~v4_relat_1(B_595, k2_zfmisc_1(A_596, B_597)) | ~v1_relat_1(B_595))), inference(resolution, [status(thm)], [c_202, c_142])).
% 8.55/2.97  tff(c_7245, plain, (![A_6]: (v1_relat_1(k1_relat_1(A_6)) | ~v1_relat_1(A_6) | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_3265, c_7220])).
% 8.55/2.97  tff(c_8152, plain, (v1_relat_1('#skF_1') | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8119, c_7245])).
% 8.55/2.97  tff(c_8192, plain, (v1_relat_1('#skF_1') | ~r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_143, c_8152])).
% 8.55/2.97  tff(c_8210, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_8192])).
% 8.55/2.97  tff(c_10226, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10213, c_8210])).
% 8.55/2.97  tff(c_10559, plain, (![A_793]: (k2_zfmisc_1(A_793, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10213, c_10213, c_12])).
% 8.55/2.97  tff(c_10272, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_10213, c_8])).
% 8.55/2.97  tff(c_10280, plain, (![C_778, A_779, B_780]: (r1_tarski(C_778, k2_zfmisc_1(A_779, B_780)) | ~r1_tarski(k2_relat_1(C_778), B_780) | ~r1_tarski(k1_relat_1(C_778), A_779) | ~v1_relat_1(C_778))), inference(resolution, [status(thm)], [c_7514, c_16])).
% 8.55/2.97  tff(c_10282, plain, (![A_779, B_780]: (r1_tarski('#skF_4', k2_zfmisc_1(A_779, B_780)) | ~r1_tarski('#skF_3', B_780) | ~r1_tarski(k1_relat_1('#skF_4'), A_779) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7034, c_10280])).
% 8.55/2.97  tff(c_10287, plain, (![A_779, B_780]: (r1_tarski('#skF_4', k2_zfmisc_1(A_779, B_780)) | ~r1_tarski('#skF_3', B_780) | ~r1_tarski('#skF_1', A_779))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_8119, c_10282])).
% 8.55/2.97  tff(c_10344, plain, (![A_779, B_780]: (r1_tarski('#skF_4', k2_zfmisc_1(A_779, B_780)) | ~r1_tarski('#skF_1', A_779))), inference(demodulation, [status(thm), theory('equality')], [c_10272, c_10287])).
% 8.55/2.97  tff(c_10567, plain, (![A_793]: (r1_tarski('#skF_4', '#skF_3') | ~r1_tarski('#skF_1', A_793))), inference(superposition, [status(thm), theory('equality')], [c_10559, c_10344])).
% 8.55/2.97  tff(c_10729, plain, (![A_794]: (~r1_tarski('#skF_1', A_794))), inference(negUnitSimplification, [status(thm)], [c_10226, c_10567])).
% 8.55/2.97  tff(c_10734, plain, $false, inference(resolution, [status(thm)], [c_6, c_10729])).
% 8.55/2.97  tff(c_10736, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_8192])).
% 8.55/2.97  tff(c_10762, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_10736, c_116])).
% 8.55/2.97  tff(c_10781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6705, c_10762])).
% 8.55/2.97  tff(c_10783, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_6698])).
% 8.55/2.97  tff(c_10782, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_6698])).
% 8.55/2.97  tff(c_10801, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10783, c_10782])).
% 8.55/2.97  tff(c_10796, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_10782, c_8])).
% 8.55/2.97  tff(c_10818, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_10801, c_10796])).
% 8.55/2.97  tff(c_11119, plain, (![A_842]: (k1_relat_1(A_842)='#skF_4' | ~v1_relat_1(A_842) | ~r1_tarski(A_842, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10783, c_10783, c_3271])).
% 8.55/2.97  tff(c_11123, plain, (k1_relat_1('#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10818, c_11119])).
% 8.55/2.97  tff(c_11134, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_11123])).
% 8.55/2.97  tff(c_10794, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10782, c_10782, c_14])).
% 8.55/2.97  tff(c_10874, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10801, c_10801, c_10794])).
% 8.55/2.97  tff(c_11010, plain, (![A_819, B_820, C_821]: (k1_relset_1(A_819, B_820, C_821)=k1_relat_1(C_821) | ~m1_subset_1(C_821, k1_zfmisc_1(k2_zfmisc_1(A_819, B_820))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.55/2.97  tff(c_11288, plain, (![B_858, C_859]: (k1_relset_1('#skF_4', B_858, C_859)=k1_relat_1(C_859) | ~m1_subset_1(C_859, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_10874, c_11010])).
% 8.55/2.97  tff(c_11290, plain, (![B_858]: (k1_relset_1('#skF_4', B_858, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6680, c_11288])).
% 8.55/2.97  tff(c_11295, plain, (![B_858]: (k1_relset_1('#skF_4', B_858, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11134, c_11290])).
% 8.55/2.97  tff(c_40, plain, (![C_27, B_26]: (v1_funct_2(C_27, k1_xboole_0, B_26) | k1_relset_1(k1_xboole_0, B_26, C_27)!=k1_xboole_0 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_26))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.55/2.97  tff(c_62, plain, (![C_27, B_26]: (v1_funct_2(C_27, k1_xboole_0, B_26) | k1_relset_1(k1_xboole_0, B_26, C_27)!=k1_xboole_0 | ~m1_subset_1(C_27, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_40])).
% 8.55/2.97  tff(c_11298, plain, (![C_860, B_861]: (v1_funct_2(C_860, '#skF_4', B_861) | k1_relset_1('#skF_4', B_861, C_860)!='#skF_4' | ~m1_subset_1(C_860, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_10783, c_10783, c_10783, c_10783, c_62])).
% 8.55/2.97  tff(c_11304, plain, (![B_861]: (v1_funct_2('#skF_4', '#skF_4', B_861) | k1_relset_1('#skF_4', B_861, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_6680, c_11298])).
% 8.55/2.97  tff(c_11315, plain, (![B_861]: (v1_funct_2('#skF_4', '#skF_4', B_861))), inference(demodulation, [status(thm), theory('equality')], [c_11295, c_11304])).
% 8.55/2.97  tff(c_10811, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10801, c_161])).
% 8.55/2.97  tff(c_11319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11315, c_10811])).
% 8.55/2.97  tff(c_11320, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_60])).
% 8.55/2.97  tff(c_11795, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_11780, c_11320])).
% 8.55/2.97  tff(c_11814, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_11543, c_11795])).
% 8.55/2.97  tff(c_11819, plain, (~v4_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_11814])).
% 8.55/2.97  tff(c_11823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_11383, c_11819])).
% 8.55/2.97  tff(c_11824, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_50])).
% 8.55/2.97  tff(c_11826, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_11824, c_8])).
% 8.55/2.97  tff(c_11838, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11824, c_11824, c_12])).
% 8.55/2.97  tff(c_11825, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_50])).
% 8.55/2.97  tff(c_11831, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11824, c_11825])).
% 8.55/2.97  tff(c_11862, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11838, c_11831, c_54])).
% 8.55/2.97  tff(c_11867, plain, (![A_941, B_942]: (r1_tarski(A_941, B_942) | ~m1_subset_1(A_941, k1_zfmisc_1(B_942)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.55/2.97  tff(c_11875, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_11862, c_11867])).
% 8.55/2.97  tff(c_11876, plain, (![B_943, A_944]: (B_943=A_944 | ~r1_tarski(B_943, A_944) | ~r1_tarski(A_944, B_943))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.55/2.97  tff(c_11878, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_11875, c_11876])).
% 8.55/2.97  tff(c_11887, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11826, c_11878])).
% 8.55/2.97  tff(c_11897, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11887, c_11862])).
% 8.55/2.97  tff(c_11900, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11887, c_11887, c_11838])).
% 8.55/2.97  tff(c_11964, plain, (![C_951, A_952, B_953]: (v1_relat_1(C_951) | ~m1_subset_1(C_951, k1_zfmisc_1(k2_zfmisc_1(A_952, B_953))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.55/2.97  tff(c_11977, plain, (![C_954]: (v1_relat_1(C_954) | ~m1_subset_1(C_954, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_11900, c_11964])).
% 8.55/2.97  tff(c_11985, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_11897, c_11977])).
% 8.55/2.97  tff(c_11846, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11824, c_11824, c_14])).
% 8.55/2.97  tff(c_11899, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11887, c_11887, c_11846])).
% 8.55/2.97  tff(c_12074, plain, (![C_973, A_974, B_975]: (v4_relat_1(C_973, A_974) | ~m1_subset_1(C_973, k1_zfmisc_1(k2_zfmisc_1(A_974, B_975))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.55/2.97  tff(c_12099, plain, (![A_984, A_985, B_986]: (v4_relat_1(A_984, A_985) | ~r1_tarski(A_984, k2_zfmisc_1(A_985, B_986)))), inference(resolution, [status(thm)], [c_18, c_12074])).
% 8.55/2.97  tff(c_12116, plain, (![A_985, B_986]: (v4_relat_1(k2_zfmisc_1(A_985, B_986), A_985))), inference(resolution, [status(thm)], [c_6, c_12099])).
% 8.55/2.97  tff(c_12144, plain, (![B_992, A_993]: (r1_tarski(k1_relat_1(B_992), A_993) | ~v4_relat_1(B_992, A_993) | ~v1_relat_1(B_992))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.55/2.97  tff(c_11889, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(resolution, [status(thm)], [c_11826, c_11876])).
% 8.55/2.97  tff(c_11950, plain, (![A_3]: (A_3='#skF_4' | ~r1_tarski(A_3, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11887, c_11887, c_11889])).
% 8.55/2.97  tff(c_12186, plain, (![B_996]: (k1_relat_1(B_996)='#skF_4' | ~v4_relat_1(B_996, '#skF_4') | ~v1_relat_1(B_996))), inference(resolution, [status(thm)], [c_12144, c_11950])).
% 8.55/2.97  tff(c_12190, plain, (![B_986]: (k1_relat_1(k2_zfmisc_1('#skF_4', B_986))='#skF_4' | ~v1_relat_1(k2_zfmisc_1('#skF_4', B_986)))), inference(resolution, [status(thm)], [c_12116, c_12186])).
% 8.55/2.97  tff(c_12201, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11985, c_11899, c_11899, c_12190])).
% 8.55/2.97  tff(c_11901, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_11887, c_11826])).
% 8.55/2.97  tff(c_12426, plain, (![A_1027, B_1028, C_1029]: (k1_relset_1(A_1027, B_1028, C_1029)=k1_relat_1(C_1029) | ~m1_subset_1(C_1029, k1_zfmisc_1(k2_zfmisc_1(A_1027, B_1028))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.55/2.97  tff(c_12539, plain, (![A_1044, B_1045, A_1046]: (k1_relset_1(A_1044, B_1045, A_1046)=k1_relat_1(A_1046) | ~r1_tarski(A_1046, k2_zfmisc_1(A_1044, B_1045)))), inference(resolution, [status(thm)], [c_18, c_12426])).
% 8.55/2.97  tff(c_12553, plain, (![A_1044, B_1045]: (k1_relset_1(A_1044, B_1045, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_11901, c_12539])).
% 8.55/2.97  tff(c_12560, plain, (![A_1044, B_1045]: (k1_relset_1(A_1044, B_1045, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12201, c_12553])).
% 8.55/2.97  tff(c_11903, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11887, c_11824])).
% 8.55/2.97  tff(c_12694, plain, (![C_1062, B_1063]: (v1_funct_2(C_1062, '#skF_4', B_1063) | k1_relset_1('#skF_4', B_1063, C_1062)!='#skF_4' | ~m1_subset_1(C_1062, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11903, c_11903, c_11903, c_11903, c_62])).
% 8.55/2.97  tff(c_12696, plain, (![B_1063]: (v1_funct_2('#skF_4', '#skF_4', B_1063) | k1_relset_1('#skF_4', B_1063, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_11897, c_12694])).
% 8.55/2.97  tff(c_12702, plain, (![B_1063]: (v1_funct_2('#skF_4', '#skF_4', B_1063))), inference(demodulation, [status(thm), theory('equality')], [c_12560, c_12696])).
% 8.55/2.97  tff(c_11865, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11862, c_11846, c_60])).
% 8.55/2.97  tff(c_11895, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11887, c_11865])).
% 8.55/2.97  tff(c_12707, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12702, c_11895])).
% 8.55/2.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.55/2.97  
% 8.55/2.97  Inference rules
% 8.55/2.97  ----------------------
% 8.55/2.97  #Ref     : 0
% 8.55/2.97  #Sup     : 2620
% 8.55/2.97  #Fact    : 0
% 8.55/2.97  #Define  : 0
% 8.55/2.97  #Split   : 30
% 8.55/2.97  #Chain   : 0
% 8.55/2.97  #Close   : 0
% 8.55/2.97  
% 8.55/2.97  Ordering : KBO
% 8.55/2.97  
% 8.55/2.97  Simplification rules
% 8.55/2.97  ----------------------
% 8.55/2.97  #Subsume      : 461
% 8.55/2.97  #Demod        : 3799
% 8.55/2.97  #Tautology    : 1286
% 8.55/2.97  #SimpNegUnit  : 45
% 8.55/2.97  #BackRed      : 487
% 8.55/2.97  
% 8.55/2.97  #Partial instantiations: 0
% 8.55/2.97  #Strategies tried      : 1
% 8.55/2.97  
% 8.55/2.98  Timing (in seconds)
% 8.55/2.98  ----------------------
% 8.55/2.98  Preprocessing        : 0.33
% 8.55/2.98  Parsing              : 0.18
% 8.55/2.98  CNF conversion       : 0.02
% 8.55/2.98  Main loop            : 1.73
% 8.55/2.98  Inferencing          : 0.57
% 8.55/2.98  Reduction            : 0.64
% 8.55/2.98  Demodulation         : 0.45
% 8.55/2.98  BG Simplification    : 0.06
% 8.55/2.98  Subsumption          : 0.33
% 8.55/2.98  Abstraction          : 0.07
% 8.55/2.98  MUC search           : 0.00
% 8.55/2.98  Cooper               : 0.00
% 8.55/2.98  Total                : 2.15
% 8.55/2.98  Index Insertion      : 0.00
% 8.55/2.98  Index Deletion       : 0.00
% 8.55/2.98  Index Matching       : 0.00
% 8.55/2.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
