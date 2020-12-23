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
% DateTime   : Thu Dec  3 10:16:17 EST 2020

% Result     : Theorem 8.85s
% Output     : CNFRefutation 8.91s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 497 expanded)
%              Number of leaves         :   36 ( 181 expanded)
%              Depth                    :   11
%              Number of atoms          :  186 (1391 expanded)
%              Number of equality atoms :   60 ( 263 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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

tff(c_56,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2873,plain,(
    ! [C_275,B_276,A_277] :
      ( v1_xboole_0(C_275)
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(B_276,A_277)))
      | ~ v1_xboole_0(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2900,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_2873])).

tff(c_2902,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2900])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3020,plain,(
    ! [A_288,B_289,D_290] :
      ( r2_relset_1(A_288,B_289,D_290,D_290)
      | ~ m1_subset_1(D_290,k1_zfmisc_1(k2_zfmisc_1(A_288,B_289))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3044,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_3020])).

tff(c_160,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_177,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_160])).

tff(c_60,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_58,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3248,plain,(
    ! [A_302,B_303,C_304] :
      ( k1_relset_1(A_302,B_303,C_304) = k1_relat_1(C_304)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(k2_zfmisc_1(A_302,B_303))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3278,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_3248])).

tff(c_3501,plain,(
    ! [B_318,A_319,C_320] :
      ( k1_xboole_0 = B_318
      | k1_relset_1(A_319,B_318,C_320) = A_319
      | ~ v1_funct_2(C_320,A_319,B_318)
      | ~ m1_subset_1(C_320,k1_zfmisc_1(k2_zfmisc_1(A_319,B_318))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3523,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_3501])).

tff(c_3535,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_3278,c_3523])).

tff(c_3539,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3535])).

tff(c_178,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_160])).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_64,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3279,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_3248])).

tff(c_3526,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_3501])).

tff(c_3538,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3279,c_3526])).

tff(c_3545,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3538])).

tff(c_3744,plain,(
    ! [A_337,B_338] :
      ( r2_hidden('#skF_3'(A_337,B_338),k1_relat_1(A_337))
      | B_338 = A_337
      | k1_relat_1(B_338) != k1_relat_1(A_337)
      | ~ v1_funct_1(B_338)
      | ~ v1_relat_1(B_338)
      | ~ v1_funct_1(A_337)
      | ~ v1_relat_1(A_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6075,plain,(
    ! [A_472,B_473] :
      ( m1_subset_1('#skF_3'(A_472,B_473),k1_relat_1(A_472))
      | B_473 = A_472
      | k1_relat_1(B_473) != k1_relat_1(A_472)
      | ~ v1_funct_1(B_473)
      | ~ v1_relat_1(B_473)
      | ~ v1_funct_1(A_472)
      | ~ v1_relat_1(A_472) ) ),
    inference(resolution,[status(thm)],[c_3744,c_20])).

tff(c_6081,plain,(
    ! [B_473] :
      ( m1_subset_1('#skF_3'('#skF_6',B_473),'#skF_4')
      | B_473 = '#skF_6'
      | k1_relat_1(B_473) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_473)
      | ~ v1_relat_1(B_473)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3545,c_6075])).

tff(c_11849,plain,(
    ! [B_642] :
      ( m1_subset_1('#skF_3'('#skF_6',B_642),'#skF_4')
      | B_642 = '#skF_6'
      | k1_relat_1(B_642) != '#skF_4'
      | ~ v1_funct_1(B_642)
      | ~ v1_relat_1(B_642) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_66,c_3545,c_6081])).

tff(c_54,plain,(
    ! [E_43] :
      ( k1_funct_1('#skF_7',E_43) = k1_funct_1('#skF_6',E_43)
      | ~ m1_subset_1(E_43,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_11855,plain,(
    ! [B_643] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_643)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_643))
      | B_643 = '#skF_6'
      | k1_relat_1(B_643) != '#skF_4'
      | ~ v1_funct_1(B_643)
      | ~ v1_relat_1(B_643) ) ),
    inference(resolution,[status(thm)],[c_11849,c_54])).

tff(c_26,plain,(
    ! [B_20,A_16] :
      ( k1_funct_1(B_20,'#skF_3'(A_16,B_20)) != k1_funct_1(A_16,'#skF_3'(A_16,B_20))
      | B_20 = A_16
      | k1_relat_1(B_20) != k1_relat_1(A_16)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_11862,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_11855,c_26])).

tff(c_11869,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_60,c_3539,c_178,c_66,c_3539,c_3545,c_11862])).

tff(c_52,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_11893,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11869,c_52])).

tff(c_11904,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3044,c_11893])).

tff(c_11905,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3538])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_11925,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11905,c_12])).

tff(c_11927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2902,c_11925])).

tff(c_11928,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3535])).

tff(c_11948,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11928,c_12])).

tff(c_11950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2902,c_11948])).

tff(c_11952,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_2900])).

tff(c_2901,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_2873])).

tff(c_12027,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11952,c_2901])).

tff(c_100,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_2'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [A_55,B_56] :
      ( ~ v1_xboole_0(A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_100,c_2])).

tff(c_116,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_tarski(B_60,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_132,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(B_62,A_63)
      | ~ v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_108,c_116])).

tff(c_150,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ v1_xboole_0(B_64)
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_108,c_132])).

tff(c_153,plain,(
    ! [A_65] :
      ( k1_xboole_0 = A_65
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_12,c_150])).

tff(c_11974,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_11952,c_153])).

tff(c_11951,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_2900])).

tff(c_11963,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_11951,c_153])).

tff(c_12008,plain,(
    '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11974,c_11963])).

tff(c_145,plain,(
    ! [B_56,A_55] :
      ( B_56 = A_55
      | ~ v1_xboole_0(B_56)
      | ~ v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_108,c_132])).

tff(c_11964,plain,(
    ! [A_55] :
      ( A_55 = '#skF_7'
      | ~ v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_11951,c_145])).

tff(c_12037,plain,(
    ! [A_647] :
      ( A_647 = '#skF_5'
      | ~ v1_xboole_0(A_647) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12008,c_11964])).

tff(c_12044,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_12027,c_12037])).

tff(c_11976,plain,(
    ! [A_644,B_645,D_646] :
      ( r2_relset_1(A_644,B_645,D_646,D_646)
      | ~ m1_subset_1(D_646,k1_zfmisc_1(k2_zfmisc_1(A_644,B_645))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_11998,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_11976])).

tff(c_12088,plain,(
    r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12044,c_11998])).

tff(c_12017,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12008,c_52])).

tff(c_12112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12088,c_12044,c_12044,c_12017])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:05:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.85/3.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.85/3.11  
% 8.85/3.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.85/3.12  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 8.85/3.12  
% 8.85/3.12  %Foreground sorts:
% 8.85/3.12  
% 8.85/3.12  
% 8.85/3.12  %Background operators:
% 8.85/3.12  
% 8.85/3.12  
% 8.85/3.12  %Foreground operators:
% 8.85/3.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.85/3.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.85/3.12  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.85/3.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.85/3.12  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.85/3.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.85/3.12  tff('#skF_7', type, '#skF_7': $i).
% 8.85/3.12  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.85/3.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.85/3.12  tff('#skF_5', type, '#skF_5': $i).
% 8.85/3.12  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.85/3.12  tff('#skF_6', type, '#skF_6': $i).
% 8.85/3.12  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.85/3.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.85/3.12  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.85/3.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.85/3.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.85/3.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.85/3.12  tff('#skF_4', type, '#skF_4': $i).
% 8.85/3.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.85/3.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.85/3.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.85/3.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.85/3.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.85/3.12  
% 8.91/3.13  tff(f_133, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_funct_2)).
% 8.91/3.13  tff(f_82, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 8.91/3.13  tff(f_94, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.91/3.13  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.91/3.13  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.91/3.13  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.91/3.13  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 8.91/3.13  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 8.91/3.13  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.91/3.13  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.91/3.13  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.91/3.13  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.91/3.13  tff(c_56, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.91/3.13  tff(c_2873, plain, (![C_275, B_276, A_277]: (v1_xboole_0(C_275) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(B_276, A_277))) | ~v1_xboole_0(A_277))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.91/3.13  tff(c_2900, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_56, c_2873])).
% 8.91/3.13  tff(c_2902, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_2900])).
% 8.91/3.13  tff(c_62, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.91/3.13  tff(c_3020, plain, (![A_288, B_289, D_290]: (r2_relset_1(A_288, B_289, D_290, D_290) | ~m1_subset_1(D_290, k1_zfmisc_1(k2_zfmisc_1(A_288, B_289))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.91/3.13  tff(c_3044, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_3020])).
% 8.91/3.13  tff(c_160, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.91/3.13  tff(c_177, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_56, c_160])).
% 8.91/3.13  tff(c_60, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.91/3.13  tff(c_58, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.91/3.13  tff(c_3248, plain, (![A_302, B_303, C_304]: (k1_relset_1(A_302, B_303, C_304)=k1_relat_1(C_304) | ~m1_subset_1(C_304, k1_zfmisc_1(k2_zfmisc_1(A_302, B_303))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.91/3.13  tff(c_3278, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_56, c_3248])).
% 8.91/3.13  tff(c_3501, plain, (![B_318, A_319, C_320]: (k1_xboole_0=B_318 | k1_relset_1(A_319, B_318, C_320)=A_319 | ~v1_funct_2(C_320, A_319, B_318) | ~m1_subset_1(C_320, k1_zfmisc_1(k2_zfmisc_1(A_319, B_318))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.91/3.13  tff(c_3523, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_3501])).
% 8.91/3.13  tff(c_3535, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_3278, c_3523])).
% 8.91/3.13  tff(c_3539, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_3535])).
% 8.91/3.13  tff(c_178, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_160])).
% 8.91/3.13  tff(c_66, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.91/3.13  tff(c_64, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.91/3.13  tff(c_3279, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_3248])).
% 8.91/3.13  tff(c_3526, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_3501])).
% 8.91/3.13  tff(c_3538, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3279, c_3526])).
% 8.91/3.13  tff(c_3545, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_3538])).
% 8.91/3.13  tff(c_3744, plain, (![A_337, B_338]: (r2_hidden('#skF_3'(A_337, B_338), k1_relat_1(A_337)) | B_338=A_337 | k1_relat_1(B_338)!=k1_relat_1(A_337) | ~v1_funct_1(B_338) | ~v1_relat_1(B_338) | ~v1_funct_1(A_337) | ~v1_relat_1(A_337))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.91/3.13  tff(c_20, plain, (![A_12, B_13]: (m1_subset_1(A_12, B_13) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.91/3.13  tff(c_6075, plain, (![A_472, B_473]: (m1_subset_1('#skF_3'(A_472, B_473), k1_relat_1(A_472)) | B_473=A_472 | k1_relat_1(B_473)!=k1_relat_1(A_472) | ~v1_funct_1(B_473) | ~v1_relat_1(B_473) | ~v1_funct_1(A_472) | ~v1_relat_1(A_472))), inference(resolution, [status(thm)], [c_3744, c_20])).
% 8.91/3.13  tff(c_6081, plain, (![B_473]: (m1_subset_1('#skF_3'('#skF_6', B_473), '#skF_4') | B_473='#skF_6' | k1_relat_1(B_473)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_473) | ~v1_relat_1(B_473) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3545, c_6075])).
% 8.91/3.13  tff(c_11849, plain, (![B_642]: (m1_subset_1('#skF_3'('#skF_6', B_642), '#skF_4') | B_642='#skF_6' | k1_relat_1(B_642)!='#skF_4' | ~v1_funct_1(B_642) | ~v1_relat_1(B_642))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_66, c_3545, c_6081])).
% 8.91/3.13  tff(c_54, plain, (![E_43]: (k1_funct_1('#skF_7', E_43)=k1_funct_1('#skF_6', E_43) | ~m1_subset_1(E_43, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.91/3.13  tff(c_11855, plain, (![B_643]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_643))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_643)) | B_643='#skF_6' | k1_relat_1(B_643)!='#skF_4' | ~v1_funct_1(B_643) | ~v1_relat_1(B_643))), inference(resolution, [status(thm)], [c_11849, c_54])).
% 8.91/3.13  tff(c_26, plain, (![B_20, A_16]: (k1_funct_1(B_20, '#skF_3'(A_16, B_20))!=k1_funct_1(A_16, '#skF_3'(A_16, B_20)) | B_20=A_16 | k1_relat_1(B_20)!=k1_relat_1(A_16) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.91/3.13  tff(c_11862, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_11855, c_26])).
% 8.91/3.13  tff(c_11869, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_177, c_60, c_3539, c_178, c_66, c_3539, c_3545, c_11862])).
% 8.91/3.13  tff(c_52, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.91/3.13  tff(c_11893, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11869, c_52])).
% 8.91/3.13  tff(c_11904, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3044, c_11893])).
% 8.91/3.13  tff(c_11905, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_3538])).
% 8.91/3.13  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.91/3.13  tff(c_11925, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11905, c_12])).
% 8.91/3.13  tff(c_11927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2902, c_11925])).
% 8.91/3.13  tff(c_11928, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_3535])).
% 8.91/3.13  tff(c_11948, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11928, c_12])).
% 8.91/3.13  tff(c_11950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2902, c_11948])).
% 8.91/3.13  tff(c_11952, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_2900])).
% 8.91/3.13  tff(c_2901, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_62, c_2873])).
% 8.91/3.13  tff(c_12027, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11952, c_2901])).
% 8.91/3.13  tff(c_100, plain, (![A_55, B_56]: (r2_hidden('#skF_2'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.91/3.13  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.91/3.13  tff(c_108, plain, (![A_55, B_56]: (~v1_xboole_0(A_55) | r1_tarski(A_55, B_56))), inference(resolution, [status(thm)], [c_100, c_2])).
% 8.91/3.13  tff(c_116, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_tarski(B_60, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.91/3.13  tff(c_132, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_tarski(B_62, A_63) | ~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_108, c_116])).
% 8.91/3.13  tff(c_150, plain, (![B_64, A_65]: (B_64=A_65 | ~v1_xboole_0(B_64) | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_108, c_132])).
% 8.91/3.13  tff(c_153, plain, (![A_65]: (k1_xboole_0=A_65 | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_12, c_150])).
% 8.91/3.13  tff(c_11974, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_11952, c_153])).
% 8.91/3.13  tff(c_11951, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_2900])).
% 8.91/3.13  tff(c_11963, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_11951, c_153])).
% 8.91/3.13  tff(c_12008, plain, ('#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_11974, c_11963])).
% 8.91/3.13  tff(c_145, plain, (![B_56, A_55]: (B_56=A_55 | ~v1_xboole_0(B_56) | ~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_108, c_132])).
% 8.91/3.13  tff(c_11964, plain, (![A_55]: (A_55='#skF_7' | ~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_11951, c_145])).
% 8.91/3.13  tff(c_12037, plain, (![A_647]: (A_647='#skF_5' | ~v1_xboole_0(A_647))), inference(demodulation, [status(thm), theory('equality')], [c_12008, c_11964])).
% 8.91/3.13  tff(c_12044, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_12027, c_12037])).
% 8.91/3.13  tff(c_11976, plain, (![A_644, B_645, D_646]: (r2_relset_1(A_644, B_645, D_646, D_646) | ~m1_subset_1(D_646, k1_zfmisc_1(k2_zfmisc_1(A_644, B_645))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.91/3.13  tff(c_11998, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_11976])).
% 8.91/3.13  tff(c_12088, plain, (r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12044, c_11998])).
% 8.91/3.13  tff(c_12017, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12008, c_52])).
% 8.91/3.13  tff(c_12112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12088, c_12044, c_12044, c_12017])).
% 8.91/3.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.91/3.13  
% 8.91/3.13  Inference rules
% 8.91/3.13  ----------------------
% 8.91/3.13  #Ref     : 2
% 8.91/3.13  #Sup     : 2819
% 8.91/3.13  #Fact    : 0
% 8.91/3.13  #Define  : 0
% 8.91/3.13  #Split   : 23
% 8.91/3.13  #Chain   : 0
% 8.91/3.13  #Close   : 0
% 8.91/3.13  
% 8.91/3.13  Ordering : KBO
% 8.91/3.13  
% 8.91/3.13  Simplification rules
% 8.91/3.14  ----------------------
% 8.91/3.14  #Subsume      : 774
% 8.91/3.14  #Demod        : 1946
% 8.91/3.14  #Tautology    : 918
% 8.91/3.14  #SimpNegUnit  : 34
% 8.91/3.14  #BackRed      : 227
% 8.91/3.14  
% 8.91/3.14  #Partial instantiations: 0
% 8.91/3.14  #Strategies tried      : 1
% 8.91/3.14  
% 8.91/3.14  Timing (in seconds)
% 8.91/3.14  ----------------------
% 8.91/3.14  Preprocessing        : 0.34
% 8.91/3.14  Parsing              : 0.18
% 8.91/3.14  CNF conversion       : 0.02
% 8.91/3.14  Main loop            : 2.03
% 8.91/3.14  Inferencing          : 0.60
% 8.91/3.14  Reduction            : 0.60
% 8.91/3.14  Demodulation         : 0.42
% 8.91/3.14  BG Simplification    : 0.07
% 8.91/3.14  Subsumption          : 0.61
% 8.91/3.14  Abstraction          : 0.08
% 8.91/3.14  MUC search           : 0.00
% 8.91/3.14  Cooper               : 0.00
% 8.91/3.14  Total                : 2.41
% 8.91/3.14  Index Insertion      : 0.00
% 8.91/3.14  Index Deletion       : 0.00
% 8.91/3.14  Index Matching       : 0.00
% 8.91/3.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
