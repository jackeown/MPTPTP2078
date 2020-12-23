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
% DateTime   : Thu Dec  3 10:11:08 EST 2020

% Result     : Theorem 7.99s
% Output     : CNFRefutation 8.20s
% Verified   : 
% Statistics : Number of formulae       :  298 (3189 expanded)
%              Number of leaves         :   35 (1021 expanded)
%              Depth                    :   16
%              Number of atoms          :  555 (9332 expanded)
%              Number of equality atoms :  176 (3125 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_123,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_103,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_141,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_158,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_141])).

tff(c_11939,plain,(
    ! [C_936,A_937,B_938] :
      ( v4_relat_1(C_936,A_937)
      | ~ m1_subset_1(C_936,k1_zfmisc_1(k2_zfmisc_1(A_937,B_938))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_11958,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_11939])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(B_13),A_12)
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12192,plain,(
    ! [A_976,B_977,C_978] :
      ( k2_relset_1(A_976,B_977,C_978) = k2_relat_1(C_978)
      | ~ m1_subset_1(C_978,k1_zfmisc_1(k2_zfmisc_1(A_976,B_977))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12211,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_12192])).

tff(c_56,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_12222,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12211,c_56])).

tff(c_12270,plain,(
    ! [C_987,A_988,B_989] :
      ( m1_subset_1(C_987,k1_zfmisc_1(k2_zfmisc_1(A_988,B_989)))
      | ~ r1_tarski(k2_relat_1(C_987),B_989)
      | ~ r1_tarski(k1_relat_1(C_987),A_988)
      | ~ v1_relat_1(C_987) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_159,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_141])).

tff(c_2456,plain,(
    ! [C_261,A_262,B_263] :
      ( v4_relat_1(C_261,A_262)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_262,B_263))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2487,plain,(
    ! [A_266] : v4_relat_1(k1_xboole_0,A_266) ),
    inference(resolution,[status(thm)],[c_16,c_2456])).

tff(c_225,plain,(
    ! [B_57,A_58] :
      ( r1_tarski(k1_relat_1(B_57),A_58)
      | ~ v4_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_243,plain,(
    ! [B_57] :
      ( k1_relat_1(B_57) = k1_xboole_0
      | ~ v4_relat_1(B_57,k1_xboole_0)
      | ~ v1_relat_1(B_57) ) ),
    inference(resolution,[status(thm)],[c_225,c_8])).

tff(c_2491,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2487,c_243])).

tff(c_2494,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_2491])).

tff(c_6239,plain,(
    ! [A_587,B_588,C_589] :
      ( k1_relset_1(A_587,B_588,C_589) = k1_relat_1(C_589)
      | ~ m1_subset_1(C_589,k1_zfmisc_1(k2_zfmisc_1(A_587,B_588))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6250,plain,(
    ! [A_587,B_588] : k1_relset_1(A_587,B_588,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_6239])).

tff(c_6259,plain,(
    ! [A_587,B_588] : k1_relset_1(A_587,B_588,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2494,c_6250])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2612,plain,(
    ! [A_290,B_291,C_292] :
      ( k1_relset_1(A_290,B_291,C_292) = k1_relat_1(C_292)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2631,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_2612])).

tff(c_2925,plain,(
    ! [B_336,A_337,C_338] :
      ( k1_xboole_0 = B_336
      | k1_relset_1(A_337,B_336,C_338) = A_337
      | ~ v1_funct_2(C_338,A_337,B_336)
      | ~ m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(A_337,B_336))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2935,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_2925])).

tff(c_2950,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2631,c_2935])).

tff(c_2951,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2950])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_410,plain,(
    ! [A_91,B_92,C_93] :
      ( k1_relset_1(A_91,B_92,C_93) = k1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_429,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_410])).

tff(c_694,plain,(
    ! [B_133,A_134,C_135] :
      ( k1_xboole_0 = B_133
      | k1_relset_1(A_134,B_133,C_135) = A_134
      | ~ v1_funct_2(C_135,A_134,B_133)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_134,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_704,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_694])).

tff(c_719,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_429,c_704])).

tff(c_720,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_719])).

tff(c_471,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_relset_1(A_99,B_100,C_101) = k2_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_490,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_471])).

tff(c_509,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_56])).

tff(c_552,plain,(
    ! [C_112,A_113,B_114] :
      ( m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114)))
      | ~ r1_tarski(k2_relat_1(C_112),B_114)
      | ~ r1_tarski(k1_relat_1(C_112),A_113)
      | ~ v1_relat_1(C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2045,plain,(
    ! [C_238,A_239,B_240] :
      ( r1_tarski(C_238,k2_zfmisc_1(A_239,B_240))
      | ~ r1_tarski(k2_relat_1(C_238),B_240)
      | ~ r1_tarski(k1_relat_1(C_238),A_239)
      | ~ v1_relat_1(C_238) ) ),
    inference(resolution,[status(thm)],[c_552,c_18])).

tff(c_2047,plain,(
    ! [A_239] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_239,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_239)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_509,c_2045])).

tff(c_2055,plain,(
    ! [A_241] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_241,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_720,c_2047])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_428,plain,(
    ! [A_91,B_92,A_7] :
      ( k1_relset_1(A_91,B_92,A_7) = k1_relat_1(A_7)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_91,B_92)) ) ),
    inference(resolution,[status(thm)],[c_20,c_410])).

tff(c_2058,plain,(
    ! [A_241] :
      ( k1_relset_1(A_241,'#skF_3','#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',A_241) ) ),
    inference(resolution,[status(thm)],[c_2055,c_428])).

tff(c_2087,plain,(
    ! [A_242] :
      ( k1_relset_1(A_242,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_2058])).

tff(c_2092,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_2087])).

tff(c_2053,plain,(
    ! [A_239] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_239,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_239) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_720,c_2047])).

tff(c_908,plain,(
    ! [B_153,C_154,A_155] :
      ( k1_xboole_0 = B_153
      | v1_funct_2(C_154,A_155,B_153)
      | k1_relset_1(A_155,B_153,C_154) != A_155
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_155,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2192,plain,(
    ! [B_248,A_249,A_250] :
      ( k1_xboole_0 = B_248
      | v1_funct_2(A_249,A_250,B_248)
      | k1_relset_1(A_250,B_248,A_249) != A_250
      | ~ r1_tarski(A_249,k2_zfmisc_1(A_250,B_248)) ) ),
    inference(resolution,[status(thm)],[c_20,c_908])).

tff(c_2221,plain,(
    ! [A_239] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2('#skF_4',A_239,'#skF_3')
      | k1_relset_1(A_239,'#skF_3','#skF_4') != A_239
      | ~ r1_tarski('#skF_1',A_239) ) ),
    inference(resolution,[status(thm)],[c_2053,c_2192])).

tff(c_2316,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2221])).

tff(c_105,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_117,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_16,c_105])).

tff(c_2378,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2316,c_117])).

tff(c_125,plain,(
    ! [B_43,A_44] :
      ( B_43 = A_44
      | ~ r1_tarski(B_43,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_133,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_125])).

tff(c_244,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_508,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_244])).

tff(c_2430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2378,c_508])).

tff(c_2433,plain,(
    ! [A_258] :
      ( v1_funct_2('#skF_4',A_258,'#skF_3')
      | k1_relset_1(A_258,'#skF_3','#skF_4') != A_258
      | ~ r1_tarski('#skF_1',A_258) ) ),
    inference(splitRight,[status(thm)],[c_2221])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_64,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52])).

tff(c_160,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_2439,plain,
    ( k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2433,c_160])).

tff(c_2444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2092,c_2439])).

tff(c_2445,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_2673,plain,(
    ! [A_298,B_299,C_300] :
      ( k2_relset_1(A_298,B_299,C_300) = k2_relat_1(C_300)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(k2_zfmisc_1(A_298,B_299))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2680,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_2673])).

tff(c_2693,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2445,c_2680])).

tff(c_2787,plain,(
    ! [C_316,A_317,B_318] :
      ( m1_subset_1(C_316,k1_zfmisc_1(k2_zfmisc_1(A_317,B_318)))
      | ~ r1_tarski(k2_relat_1(C_316),B_318)
      | ~ r1_tarski(k1_relat_1(C_316),A_317)
      | ~ v1_relat_1(C_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4289,plain,(
    ! [C_442,A_443,B_444] :
      ( r1_tarski(C_442,k2_zfmisc_1(A_443,B_444))
      | ~ r1_tarski(k2_relat_1(C_442),B_444)
      | ~ r1_tarski(k1_relat_1(C_442),A_443)
      | ~ v1_relat_1(C_442) ) ),
    inference(resolution,[status(thm)],[c_2787,c_18])).

tff(c_4291,plain,(
    ! [A_443,B_444] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_443,B_444))
      | ~ r1_tarski('#skF_3',B_444)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_443)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2693,c_4289])).

tff(c_4298,plain,(
    ! [A_445,B_446] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_445,B_446))
      | ~ r1_tarski('#skF_3',B_446)
      | ~ r1_tarski('#skF_1',A_445) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_2951,c_4291])).

tff(c_2630,plain,(
    ! [A_290,B_291,A_7] :
      ( k1_relset_1(A_290,B_291,A_7) = k1_relat_1(A_7)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_290,B_291)) ) ),
    inference(resolution,[status(thm)],[c_20,c_2612])).

tff(c_4304,plain,(
    ! [A_445,B_446] :
      ( k1_relset_1(A_445,B_446,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_3',B_446)
      | ~ r1_tarski('#skF_1',A_445) ) ),
    inference(resolution,[status(thm)],[c_4298,c_2630])).

tff(c_4359,plain,(
    ! [A_452,B_453] :
      ( k1_relset_1(A_452,B_453,'#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_3',B_453)
      | ~ r1_tarski('#skF_1',A_452) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2951,c_4304])).

tff(c_4364,plain,(
    ! [A_454] :
      ( k1_relset_1(A_454,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_454) ) ),
    inference(resolution,[status(thm)],[c_6,c_4359])).

tff(c_4369,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_4364])).

tff(c_4374,plain,(
    ! [C_455,A_456] :
      ( r1_tarski(C_455,k2_zfmisc_1(A_456,k2_relat_1(C_455)))
      | ~ r1_tarski(k1_relat_1(C_455),A_456)
      | ~ v1_relat_1(C_455) ) ),
    inference(resolution,[status(thm)],[c_6,c_4289])).

tff(c_4418,plain,(
    ! [A_456] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_456,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_456)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2693,c_4374])).

tff(c_4437,plain,(
    ! [A_456] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_456,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_456) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_2951,c_4418])).

tff(c_4630,plain,(
    ! [B_465,A_466,A_467] :
      ( k1_xboole_0 = B_465
      | k1_relset_1(A_466,B_465,A_467) = A_466
      | ~ v1_funct_2(A_467,A_466,B_465)
      | ~ r1_tarski(A_467,k2_zfmisc_1(A_466,B_465)) ) ),
    inference(resolution,[status(thm)],[c_20,c_2925])).

tff(c_4661,plain,(
    ! [A_456] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1(A_456,'#skF_3','#skF_4') = A_456
      | ~ v1_funct_2('#skF_4',A_456,'#skF_3')
      | ~ r1_tarski('#skF_1',A_456) ) ),
    inference(resolution,[status(thm)],[c_4437,c_4630])).

tff(c_4766,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4661])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3972,plain,(
    ! [C_429,A_430] :
      ( m1_subset_1(C_429,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_429),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_429),A_430)
      | ~ v1_relat_1(C_429) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2787])).

tff(c_3974,plain,(
    ! [A_430] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_430)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2693,c_3972])).

tff(c_3976,plain,(
    ! [A_430] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski('#skF_1',A_430) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_2951,c_3974])).

tff(c_3977,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3976])).

tff(c_4779,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4766,c_3977])).

tff(c_4840,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4779])).

tff(c_4842,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4661])).

tff(c_3036,plain,(
    ! [B_343,C_344,A_345] :
      ( k1_xboole_0 = B_343
      | v1_funct_2(C_344,A_345,B_343)
      | k1_relset_1(A_345,B_343,C_344) != A_345
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(A_345,B_343))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5189,plain,(
    ! [B_494,A_495,A_496] :
      ( k1_xboole_0 = B_494
      | v1_funct_2(A_495,A_496,B_494)
      | k1_relset_1(A_496,B_494,A_495) != A_496
      | ~ r1_tarski(A_495,k2_zfmisc_1(A_496,B_494)) ) ),
    inference(resolution,[status(thm)],[c_20,c_3036])).

tff(c_5192,plain,(
    ! [A_456] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2('#skF_4',A_456,'#skF_3')
      | k1_relset_1(A_456,'#skF_3','#skF_4') != A_456
      | ~ r1_tarski('#skF_1',A_456) ) ),
    inference(resolution,[status(thm)],[c_4437,c_5189])).

tff(c_5235,plain,(
    ! [A_497] :
      ( v1_funct_2('#skF_4',A_497,'#skF_3')
      | k1_relset_1(A_497,'#skF_3','#skF_4') != A_497
      | ~ r1_tarski('#skF_1',A_497) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4842,c_5192])).

tff(c_5244,plain,
    ( k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_5235,c_160])).

tff(c_5250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4369,c_5244])).

tff(c_5252,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3976])).

tff(c_5281,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5252,c_8])).

tff(c_2538,plain,(
    ! [C_270,A_271] :
      ( v4_relat_1(C_270,A_271)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2456])).

tff(c_2545,plain,(
    ! [A_7,A_271] :
      ( v4_relat_1(A_7,A_271)
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_2538])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_161,plain,(
    ! [C_48] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_141])).

tff(c_170,plain,(
    ! [A_7] :
      ( v1_relat_1(A_7)
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_161])).

tff(c_241,plain,(
    ! [B_57] :
      ( v1_relat_1(k1_relat_1(B_57))
      | ~ v4_relat_1(B_57,k1_xboole_0)
      | ~ v1_relat_1(B_57) ) ),
    inference(resolution,[status(thm)],[c_225,c_170])).

tff(c_2965,plain,
    ( v1_relat_1('#skF_1')
    | ~ v4_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2951,c_241])).

tff(c_2976,plain,
    ( v1_relat_1('#skF_1')
    | ~ v4_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_2965])).

tff(c_2984,plain,(
    ~ v4_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2976])).

tff(c_2988,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2545,c_2984])).

tff(c_5379,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5281,c_2988])).

tff(c_5251,plain,(
    ! [A_430] :
      ( ~ r1_tarski('#skF_1',A_430)
      | m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_3976])).

tff(c_5350,plain,(
    ! [A_498] : ~ r1_tarski('#skF_1',A_498) ),
    inference(splitLeft,[status(thm)],[c_5251])).

tff(c_5355,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_5350])).

tff(c_5356,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_5251])).

tff(c_5554,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5281,c_5356])).

tff(c_5559,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_5554,c_18])).

tff(c_5564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5379,c_5559])).

tff(c_5566,plain,(
    v4_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2976])).

tff(c_5569,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5566,c_243])).

tff(c_5572,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_2951,c_5569])).

tff(c_5616,plain,(
    ! [A_6] : r1_tarski('#skF_1',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5572,c_117])).

tff(c_5621,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5572,c_5572,c_14])).

tff(c_116,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_105])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_140,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_116,c_2])).

tff(c_2520,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_5790,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5621,c_2520])).

tff(c_5795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5616,c_5790])).

tff(c_5796,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_6875,plain,(
    ! [B_668,C_669,A_670] :
      ( k1_xboole_0 = B_668
      | v1_funct_2(C_669,A_670,B_668)
      | k1_relset_1(A_670,B_668,C_669) != A_670
      | ~ m1_subset_1(C_669,k1_zfmisc_1(k2_zfmisc_1(A_670,B_668))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6881,plain,(
    ! [C_669] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_669,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_669) != '#skF_1'
      | ~ m1_subset_1(C_669,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5796,c_6875])).

tff(c_6967,plain,(
    ! [C_676] :
      ( v1_funct_2(C_676,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_676) != '#skF_1'
      | ~ m1_subset_1(C_676,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_6881])).

tff(c_6978,plain,
    ( v1_funct_2(k1_xboole_0,'#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2',k1_xboole_0) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_6967])).

tff(c_6983,plain,
    ( v1_funct_2(k1_xboole_0,'#skF_1','#skF_2')
    | k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6259,c_6978])).

tff(c_6984,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_6983])).

tff(c_5799,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5796,c_58])).

tff(c_6292,plain,(
    ! [C_596] :
      ( k1_relset_1('#skF_1','#skF_2',C_596) = k1_relat_1(C_596)
      | ~ m1_subset_1(C_596,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5796,c_6239])).

tff(c_6304,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5799,c_6292])).

tff(c_7207,plain,(
    ! [B_680,A_681,C_682] :
      ( k1_xboole_0 = B_680
      | k1_relset_1(A_681,B_680,C_682) = A_681
      | ~ v1_funct_2(C_682,A_681,B_680)
      | ~ m1_subset_1(C_682,k1_zfmisc_1(k2_zfmisc_1(A_681,B_680))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_7213,plain,(
    ! [C_682] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_682) = '#skF_1'
      | ~ v1_funct_2(C_682,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_682,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5796,c_7207])).

tff(c_7306,plain,(
    ! [C_688] :
      ( k1_relset_1('#skF_1','#skF_2',C_688) = '#skF_1'
      | ~ v1_funct_2(C_688,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_688,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_7213])).

tff(c_7309,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_5799,c_7306])).

tff(c_7320,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6304,c_7309])).

tff(c_6127,plain,(
    ! [A_572,B_573,C_574] :
      ( k2_relset_1(A_572,B_573,C_574) = k2_relat_1(C_574)
      | ~ m1_subset_1(C_574,k1_zfmisc_1(k2_zfmisc_1(A_572,B_573))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6165,plain,(
    ! [C_579] :
      ( k2_relset_1('#skF_1','#skF_2',C_579) = k2_relat_1(C_579)
      | ~ m1_subset_1(C_579,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5796,c_6127])).

tff(c_6168,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5799,c_6165])).

tff(c_6178,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2445,c_6168])).

tff(c_6714,plain,(
    ! [C_646,A_647,B_648] :
      ( m1_subset_1(C_646,k1_zfmisc_1(k2_zfmisc_1(A_647,B_648)))
      | ~ r1_tarski(k2_relat_1(C_646),B_648)
      | ~ r1_tarski(k1_relat_1(C_646),A_647)
      | ~ v1_relat_1(C_646) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7656,plain,(
    ! [C_708,A_709,B_710] :
      ( r1_tarski(C_708,k2_zfmisc_1(A_709,B_710))
      | ~ r1_tarski(k2_relat_1(C_708),B_710)
      | ~ r1_tarski(k1_relat_1(C_708),A_709)
      | ~ v1_relat_1(C_708) ) ),
    inference(resolution,[status(thm)],[c_6714,c_18])).

tff(c_7658,plain,(
    ! [A_709,B_710] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_709,B_710))
      | ~ r1_tarski('#skF_3',B_710)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_709)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6178,c_7656])).

tff(c_7939,plain,(
    ! [A_725,B_726] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_725,B_726))
      | ~ r1_tarski('#skF_3',B_726)
      | ~ r1_tarski('#skF_1',A_725) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_7320,c_7658])).

tff(c_6257,plain,(
    ! [A_587,B_588,A_7] :
      ( k1_relset_1(A_587,B_588,A_7) = k1_relat_1(A_7)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_587,B_588)) ) ),
    inference(resolution,[status(thm)],[c_20,c_6239])).

tff(c_7948,plain,(
    ! [A_725,B_726] :
      ( k1_relset_1(A_725,B_726,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_3',B_726)
      | ~ r1_tarski('#skF_1',A_725) ) ),
    inference(resolution,[status(thm)],[c_7939,c_6257])).

tff(c_8106,plain,(
    ! [A_739,B_740] :
      ( k1_relset_1(A_739,B_740,'#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_3',B_740)
      | ~ r1_tarski('#skF_1',A_739) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7320,c_7948])).

tff(c_8111,plain,(
    ! [A_741] :
      ( k1_relset_1(A_741,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_741) ) ),
    inference(resolution,[status(thm)],[c_6,c_8106])).

tff(c_8116,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_8111])).

tff(c_38,plain,(
    ! [C_28,A_26,B_27] :
      ( m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ r1_tarski(k2_relat_1(C_28),B_27)
      | ~ r1_tarski(k1_relat_1(C_28),A_26)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_9623,plain,(
    ! [B_800,C_801,A_802] :
      ( k1_xboole_0 = B_800
      | v1_funct_2(C_801,A_802,B_800)
      | k1_relset_1(A_802,B_800,C_801) != A_802
      | ~ r1_tarski(k2_relat_1(C_801),B_800)
      | ~ r1_tarski(k1_relat_1(C_801),A_802)
      | ~ v1_relat_1(C_801) ) ),
    inference(resolution,[status(thm)],[c_38,c_6875])).

tff(c_9628,plain,(
    ! [B_800,A_802] :
      ( k1_xboole_0 = B_800
      | v1_funct_2('#skF_4',A_802,B_800)
      | k1_relset_1(A_802,B_800,'#skF_4') != A_802
      | ~ r1_tarski('#skF_3',B_800)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_802)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6178,c_9623])).

tff(c_9756,plain,(
    ! [B_807,A_808] :
      ( k1_xboole_0 = B_807
      | v1_funct_2('#skF_4',A_808,B_807)
      | k1_relset_1(A_808,B_807,'#skF_4') != A_808
      | ~ r1_tarski('#skF_3',B_807)
      | ~ r1_tarski('#skF_1',A_808) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_7320,c_9628])).

tff(c_9771,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_9756,c_160])).

tff(c_9784,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_8116,c_9771])).

tff(c_7543,plain,(
    ! [C_698,A_699] :
      ( m1_subset_1(C_698,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_698),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_698),A_699)
      | ~ v1_relat_1(C_698) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_6714])).

tff(c_7545,plain,(
    ! [A_699] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_699)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6178,c_7543])).

tff(c_7547,plain,(
    ! [A_699] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski('#skF_1',A_699) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_7320,c_7545])).

tff(c_7811,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_7547])).

tff(c_9820,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9784,c_7811])).

tff(c_9886,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9820])).

tff(c_9888,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_7547])).

tff(c_9904,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_9888,c_2])).

tff(c_9916,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_9904])).

tff(c_5882,plain,(
    ! [C_529,A_530] :
      ( v4_relat_1(C_529,A_530)
      | ~ m1_subset_1(C_529,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2456])).

tff(c_5889,plain,(
    ! [A_7,A_530] :
      ( v4_relat_1(A_7,A_530)
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_5882])).

tff(c_157,plain,(
    ! [A_7,A_46,B_47] :
      ( v1_relat_1(A_7)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_46,B_47)) ) ),
    inference(resolution,[status(thm)],[c_20,c_141])).

tff(c_6088,plain,(
    ! [B_566,A_567,B_568] :
      ( v1_relat_1(k1_relat_1(B_566))
      | ~ v4_relat_1(B_566,k2_zfmisc_1(A_567,B_568))
      | ~ v1_relat_1(B_566) ) ),
    inference(resolution,[status(thm)],[c_225,c_157])).

tff(c_6110,plain,(
    ! [A_7] :
      ( v1_relat_1(k1_relat_1(A_7))
      | ~ v1_relat_1(A_7)
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_5889,c_6088])).

tff(c_7356,plain,
    ( v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7320,c_6110])).

tff(c_7393,plain,
    ( v1_relat_1('#skF_1')
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_7356])).

tff(c_7414,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_7393])).

tff(c_9927,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9916,c_7414])).

tff(c_9978,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9916,c_9916,c_12])).

tff(c_10749,plain,(
    ! [C_860,A_861] :
      ( r1_tarski(C_860,k2_zfmisc_1(A_861,k2_relat_1(C_860)))
      | ~ r1_tarski(k1_relat_1(C_860),A_861)
      | ~ v1_relat_1(C_860) ) ),
    inference(resolution,[status(thm)],[c_6,c_7656])).

tff(c_10801,plain,(
    ! [A_861] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_861,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_861)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6178,c_10749])).

tff(c_10818,plain,(
    ! [A_861] :
      ( r1_tarski('#skF_4','#skF_3')
      | ~ r1_tarski('#skF_1',A_861) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_7320,c_9978,c_10801])).

tff(c_10821,plain,(
    ! [A_862] : ~ r1_tarski('#skF_1',A_862) ),
    inference(negUnitSimplification,[status(thm)],[c_9927,c_10818])).

tff(c_10831,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_10821])).

tff(c_10833,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_7393])).

tff(c_5892,plain,(
    ! [A_531,A_532] :
      ( v4_relat_1(A_531,A_532)
      | ~ r1_tarski(A_531,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_5882])).

tff(c_5897,plain,(
    ! [A_531] :
      ( k1_relat_1(A_531) = k1_xboole_0
      | ~ v1_relat_1(A_531)
      | ~ r1_tarski(A_531,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_5892,c_243])).

tff(c_10844,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10833,c_5897])).

tff(c_10863,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_7320,c_10844])).

tff(c_10865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6984,c_10863])).

tff(c_10867,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6983])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5811,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5796,c_10])).

tff(c_5817,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_5811])).

tff(c_5824,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5817])).

tff(c_10899,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10867,c_5824])).

tff(c_11377,plain,(
    ! [B_877] : k2_zfmisc_1('#skF_1',B_877) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10867,c_10867,c_14])).

tff(c_11445,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_11377,c_5796])).

tff(c_11475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10899,c_11445])).

tff(c_11477,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5817])).

tff(c_11476,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5817])).

tff(c_11497,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11477,c_11476])).

tff(c_11478,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11476,c_11476,c_2494])).

tff(c_11519,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11497,c_11497,c_11478])).

tff(c_11489,plain,(
    ! [A_6] : m1_subset_1('#skF_1',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11476,c_16])).

tff(c_11554,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11497,c_11489])).

tff(c_11782,plain,(
    ! [A_907,B_908,C_909] :
      ( k1_relset_1(A_907,B_908,C_909) = k1_relat_1(C_909)
      | ~ m1_subset_1(C_909,k1_zfmisc_1(k2_zfmisc_1(A_907,B_908))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_11792,plain,(
    ! [A_907,B_908] : k1_relset_1(A_907,B_908,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11554,c_11782])).

tff(c_11798,plain,(
    ! [A_907,B_908] : k1_relset_1(A_907,B_908,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11519,c_11792])).

tff(c_44,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_68,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_44])).

tff(c_11845,plain,(
    ! [C_922,B_923] :
      ( v1_funct_2(C_922,'#skF_4',B_923)
      | k1_relset_1('#skF_4',B_923,C_922) != '#skF_4'
      | ~ m1_subset_1(C_922,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11477,c_11477,c_11477,c_11477,c_68])).

tff(c_11848,plain,(
    ! [B_923] :
      ( v1_funct_2('#skF_4','#skF_4',B_923)
      | k1_relset_1('#skF_4',B_923,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_11554,c_11845])).

tff(c_11854,plain,(
    ! [B_923] : v1_funct_2('#skF_4','#skF_4',B_923) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11798,c_11848])).

tff(c_11506,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11497,c_160])).

tff(c_11859,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11854,c_11506])).

tff(c_11860,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_12287,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12270,c_11860])).

tff(c_12307,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_12222,c_12287])).

tff(c_12312,plain,
    ( ~ v4_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_12307])).

tff(c_12316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_11958,c_12312])).

tff(c_12317,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_12329,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12317,c_12317,c_14])).

tff(c_12318,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_12323,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12317,c_12318])).

tff(c_12365,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12329,c_12323,c_58])).

tff(c_12368,plain,(
    ! [A_997,B_998] :
      ( r1_tarski(A_997,B_998)
      | ~ m1_subset_1(A_997,k1_zfmisc_1(B_998)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12379,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_12365,c_12368])).

tff(c_12355,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12317,c_12317,c_8])).

tff(c_12384,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12379,c_12355])).

tff(c_12353,plain,(
    ! [A_6] : m1_subset_1('#skF_1',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12317,c_16])).

tff(c_12390,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12384,c_12353])).

tff(c_12444,plain,(
    ! [C_1005,A_1006,B_1007] :
      ( v1_relat_1(C_1005)
      | ~ m1_subset_1(C_1005,k1_zfmisc_1(k2_zfmisc_1(A_1006,B_1007))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_12457,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12390,c_12444])).

tff(c_12652,plain,(
    ! [C_1043,A_1044,B_1045] :
      ( v4_relat_1(C_1043,A_1044)
      | ~ m1_subset_1(C_1043,k1_zfmisc_1(k2_zfmisc_1(A_1044,B_1045))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12669,plain,(
    ! [A_1046] : v4_relat_1('#skF_4',A_1046) ),
    inference(resolution,[status(thm)],[c_12390,c_12652])).

tff(c_12587,plain,(
    ! [B_1029,A_1030] :
      ( r1_tarski(k1_relat_1(B_1029),A_1030)
      | ~ v4_relat_1(B_1029,A_1030)
      | ~ v1_relat_1(B_1029) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12389,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ r1_tarski(A_3,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12384,c_12384,c_12355])).

tff(c_12605,plain,(
    ! [B_1029] :
      ( k1_relat_1(B_1029) = '#skF_4'
      | ~ v4_relat_1(B_1029,'#skF_4')
      | ~ v1_relat_1(B_1029) ) ),
    inference(resolution,[status(thm)],[c_12587,c_12389])).

tff(c_12673,plain,
    ( k1_relat_1('#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12669,c_12605])).

tff(c_12676,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12457,c_12673])).

tff(c_12807,plain,(
    ! [A_1068,B_1069,C_1070] :
      ( k1_relset_1(A_1068,B_1069,C_1070) = k1_relat_1(C_1070)
      | ~ m1_subset_1(C_1070,k1_zfmisc_1(k2_zfmisc_1(A_1068,B_1069))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12817,plain,(
    ! [A_1068,B_1069] : k1_relset_1(A_1068,B_1069,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12390,c_12807])).

tff(c_12823,plain,(
    ! [A_1068,B_1069] : k1_relset_1(A_1068,B_1069,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12676,c_12817])).

tff(c_12395,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12384,c_12317])).

tff(c_12889,plain,(
    ! [C_1083,B_1084] :
      ( v1_funct_2(C_1083,'#skF_4',B_1084)
      | k1_relset_1('#skF_4',B_1084,C_1083) != '#skF_4'
      | ~ m1_subset_1(C_1083,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12395,c_12395,c_12395,c_12395,c_68])).

tff(c_12892,plain,(
    ! [B_1084] :
      ( v1_funct_2('#skF_4','#skF_4',B_1084)
      | k1_relset_1('#skF_4',B_1084,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_12390,c_12889])).

tff(c_12898,plain,(
    ! [B_1084] : v1_funct_2('#skF_4','#skF_4',B_1084) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12823,c_12892])).

tff(c_12413,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12384,c_12384,c_64])).

tff(c_12414,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_12413])).

tff(c_12903,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12898,c_12414])).

tff(c_12904,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_12413])).

tff(c_12963,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12390,c_12904])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n012.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 19:34:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.99/3.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.20/3.22  
% 8.20/3.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.20/3.23  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.20/3.23  
% 8.20/3.23  %Foreground sorts:
% 8.20/3.23  
% 8.20/3.23  
% 8.20/3.23  %Background operators:
% 8.20/3.23  
% 8.20/3.23  
% 8.20/3.23  %Foreground operators:
% 8.20/3.23  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.20/3.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.20/3.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.20/3.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.20/3.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.20/3.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.20/3.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.20/3.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.20/3.23  tff('#skF_2', type, '#skF_2': $i).
% 8.20/3.23  tff('#skF_3', type, '#skF_3': $i).
% 8.20/3.23  tff('#skF_1', type, '#skF_1': $i).
% 8.20/3.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.20/3.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.20/3.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.20/3.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.20/3.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.20/3.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.20/3.23  tff('#skF_4', type, '#skF_4': $i).
% 8.20/3.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.20/3.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.20/3.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.20/3.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.20/3.23  
% 8.20/3.26  tff(f_123, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 8.20/3.26  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.20/3.26  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.20/3.26  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 8.20/3.26  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.20/3.26  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 8.20/3.26  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 8.20/3.26  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 8.20/3.26  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.20/3.26  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.20/3.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.20/3.26  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.20/3.26  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.20/3.26  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.20/3.26  tff(c_141, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.20/3.26  tff(c_158, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_141])).
% 8.20/3.26  tff(c_11939, plain, (![C_936, A_937, B_938]: (v4_relat_1(C_936, A_937) | ~m1_subset_1(C_936, k1_zfmisc_1(k2_zfmisc_1(A_937, B_938))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.20/3.26  tff(c_11958, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_11939])).
% 8.20/3.26  tff(c_26, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(B_13), A_12) | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.20/3.26  tff(c_12192, plain, (![A_976, B_977, C_978]: (k2_relset_1(A_976, B_977, C_978)=k2_relat_1(C_978) | ~m1_subset_1(C_978, k1_zfmisc_1(k2_zfmisc_1(A_976, B_977))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.20/3.26  tff(c_12211, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_12192])).
% 8.20/3.26  tff(c_56, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.20/3.26  tff(c_12222, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12211, c_56])).
% 8.20/3.26  tff(c_12270, plain, (![C_987, A_988, B_989]: (m1_subset_1(C_987, k1_zfmisc_1(k2_zfmisc_1(A_988, B_989))) | ~r1_tarski(k2_relat_1(C_987), B_989) | ~r1_tarski(k1_relat_1(C_987), A_988) | ~v1_relat_1(C_987))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.20/3.26  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.20/3.26  tff(c_159, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_141])).
% 8.20/3.26  tff(c_2456, plain, (![C_261, A_262, B_263]: (v4_relat_1(C_261, A_262) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_262, B_263))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.20/3.26  tff(c_2487, plain, (![A_266]: (v4_relat_1(k1_xboole_0, A_266))), inference(resolution, [status(thm)], [c_16, c_2456])).
% 8.20/3.26  tff(c_225, plain, (![B_57, A_58]: (r1_tarski(k1_relat_1(B_57), A_58) | ~v4_relat_1(B_57, A_58) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.20/3.26  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.20/3.26  tff(c_243, plain, (![B_57]: (k1_relat_1(B_57)=k1_xboole_0 | ~v4_relat_1(B_57, k1_xboole_0) | ~v1_relat_1(B_57))), inference(resolution, [status(thm)], [c_225, c_8])).
% 8.20/3.26  tff(c_2491, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2487, c_243])).
% 8.20/3.26  tff(c_2494, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_159, c_2491])).
% 8.20/3.26  tff(c_6239, plain, (![A_587, B_588, C_589]: (k1_relset_1(A_587, B_588, C_589)=k1_relat_1(C_589) | ~m1_subset_1(C_589, k1_zfmisc_1(k2_zfmisc_1(A_587, B_588))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.20/3.26  tff(c_6250, plain, (![A_587, B_588]: (k1_relset_1(A_587, B_588, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_6239])).
% 8.20/3.26  tff(c_6259, plain, (![A_587, B_588]: (k1_relset_1(A_587, B_588, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2494, c_6250])).
% 8.20/3.26  tff(c_54, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.20/3.26  tff(c_72, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_54])).
% 8.20/3.26  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.20/3.26  tff(c_2612, plain, (![A_290, B_291, C_292]: (k1_relset_1(A_290, B_291, C_292)=k1_relat_1(C_292) | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_290, B_291))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.20/3.26  tff(c_2631, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_2612])).
% 8.20/3.26  tff(c_2925, plain, (![B_336, A_337, C_338]: (k1_xboole_0=B_336 | k1_relset_1(A_337, B_336, C_338)=A_337 | ~v1_funct_2(C_338, A_337, B_336) | ~m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(A_337, B_336))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.20/3.26  tff(c_2935, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_2925])).
% 8.20/3.26  tff(c_2950, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2631, c_2935])).
% 8.20/3.26  tff(c_2951, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_72, c_2950])).
% 8.20/3.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.20/3.26  tff(c_410, plain, (![A_91, B_92, C_93]: (k1_relset_1(A_91, B_92, C_93)=k1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.20/3.26  tff(c_429, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_410])).
% 8.20/3.26  tff(c_694, plain, (![B_133, A_134, C_135]: (k1_xboole_0=B_133 | k1_relset_1(A_134, B_133, C_135)=A_134 | ~v1_funct_2(C_135, A_134, B_133) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_134, B_133))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.20/3.26  tff(c_704, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_694])).
% 8.20/3.26  tff(c_719, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_429, c_704])).
% 8.20/3.26  tff(c_720, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_72, c_719])).
% 8.20/3.26  tff(c_471, plain, (![A_99, B_100, C_101]: (k2_relset_1(A_99, B_100, C_101)=k2_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.20/3.26  tff(c_490, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_471])).
% 8.20/3.26  tff(c_509, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_490, c_56])).
% 8.20/3.26  tff(c_552, plain, (![C_112, A_113, B_114]: (m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))) | ~r1_tarski(k2_relat_1(C_112), B_114) | ~r1_tarski(k1_relat_1(C_112), A_113) | ~v1_relat_1(C_112))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.20/3.26  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.20/3.26  tff(c_2045, plain, (![C_238, A_239, B_240]: (r1_tarski(C_238, k2_zfmisc_1(A_239, B_240)) | ~r1_tarski(k2_relat_1(C_238), B_240) | ~r1_tarski(k1_relat_1(C_238), A_239) | ~v1_relat_1(C_238))), inference(resolution, [status(thm)], [c_552, c_18])).
% 8.20/3.26  tff(c_2047, plain, (![A_239]: (r1_tarski('#skF_4', k2_zfmisc_1(A_239, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_239) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_509, c_2045])).
% 8.20/3.26  tff(c_2055, plain, (![A_241]: (r1_tarski('#skF_4', k2_zfmisc_1(A_241, '#skF_3')) | ~r1_tarski('#skF_1', A_241))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_720, c_2047])).
% 8.20/3.26  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.20/3.26  tff(c_428, plain, (![A_91, B_92, A_7]: (k1_relset_1(A_91, B_92, A_7)=k1_relat_1(A_7) | ~r1_tarski(A_7, k2_zfmisc_1(A_91, B_92)))), inference(resolution, [status(thm)], [c_20, c_410])).
% 8.20/3.26  tff(c_2058, plain, (![A_241]: (k1_relset_1(A_241, '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', A_241))), inference(resolution, [status(thm)], [c_2055, c_428])).
% 8.20/3.26  tff(c_2087, plain, (![A_242]: (k1_relset_1(A_242, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_242))), inference(demodulation, [status(thm), theory('equality')], [c_720, c_2058])).
% 8.20/3.26  tff(c_2092, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_2087])).
% 8.20/3.26  tff(c_2053, plain, (![A_239]: (r1_tarski('#skF_4', k2_zfmisc_1(A_239, '#skF_3')) | ~r1_tarski('#skF_1', A_239))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_720, c_2047])).
% 8.20/3.26  tff(c_908, plain, (![B_153, C_154, A_155]: (k1_xboole_0=B_153 | v1_funct_2(C_154, A_155, B_153) | k1_relset_1(A_155, B_153, C_154)!=A_155 | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_155, B_153))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.20/3.26  tff(c_2192, plain, (![B_248, A_249, A_250]: (k1_xboole_0=B_248 | v1_funct_2(A_249, A_250, B_248) | k1_relset_1(A_250, B_248, A_249)!=A_250 | ~r1_tarski(A_249, k2_zfmisc_1(A_250, B_248)))), inference(resolution, [status(thm)], [c_20, c_908])).
% 8.20/3.26  tff(c_2221, plain, (![A_239]: (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', A_239, '#skF_3') | k1_relset_1(A_239, '#skF_3', '#skF_4')!=A_239 | ~r1_tarski('#skF_1', A_239))), inference(resolution, [status(thm)], [c_2053, c_2192])).
% 8.20/3.26  tff(c_2316, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2221])).
% 8.20/3.26  tff(c_105, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.20/3.26  tff(c_117, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_16, c_105])).
% 8.20/3.26  tff(c_2378, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_2316, c_117])).
% 8.20/3.26  tff(c_125, plain, (![B_43, A_44]: (B_43=A_44 | ~r1_tarski(B_43, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.20/3.26  tff(c_133, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_125])).
% 8.20/3.26  tff(c_244, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_133])).
% 8.20/3.26  tff(c_508, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_490, c_244])).
% 8.20/3.26  tff(c_2430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2378, c_508])).
% 8.20/3.26  tff(c_2433, plain, (![A_258]: (v1_funct_2('#skF_4', A_258, '#skF_3') | k1_relset_1(A_258, '#skF_3', '#skF_4')!=A_258 | ~r1_tarski('#skF_1', A_258))), inference(splitRight, [status(thm)], [c_2221])).
% 8.20/3.26  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.20/3.26  tff(c_52, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.20/3.26  tff(c_64, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52])).
% 8.20/3.26  tff(c_160, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_64])).
% 8.20/3.26  tff(c_2439, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2433, c_160])).
% 8.20/3.26  tff(c_2444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2092, c_2439])).
% 8.20/3.26  tff(c_2445, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_133])).
% 8.20/3.26  tff(c_2673, plain, (![A_298, B_299, C_300]: (k2_relset_1(A_298, B_299, C_300)=k2_relat_1(C_300) | ~m1_subset_1(C_300, k1_zfmisc_1(k2_zfmisc_1(A_298, B_299))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.20/3.26  tff(c_2680, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_2673])).
% 8.20/3.26  tff(c_2693, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2445, c_2680])).
% 8.20/3.26  tff(c_2787, plain, (![C_316, A_317, B_318]: (m1_subset_1(C_316, k1_zfmisc_1(k2_zfmisc_1(A_317, B_318))) | ~r1_tarski(k2_relat_1(C_316), B_318) | ~r1_tarski(k1_relat_1(C_316), A_317) | ~v1_relat_1(C_316))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.20/3.26  tff(c_4289, plain, (![C_442, A_443, B_444]: (r1_tarski(C_442, k2_zfmisc_1(A_443, B_444)) | ~r1_tarski(k2_relat_1(C_442), B_444) | ~r1_tarski(k1_relat_1(C_442), A_443) | ~v1_relat_1(C_442))), inference(resolution, [status(thm)], [c_2787, c_18])).
% 8.20/3.26  tff(c_4291, plain, (![A_443, B_444]: (r1_tarski('#skF_4', k2_zfmisc_1(A_443, B_444)) | ~r1_tarski('#skF_3', B_444) | ~r1_tarski(k1_relat_1('#skF_4'), A_443) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2693, c_4289])).
% 8.20/3.26  tff(c_4298, plain, (![A_445, B_446]: (r1_tarski('#skF_4', k2_zfmisc_1(A_445, B_446)) | ~r1_tarski('#skF_3', B_446) | ~r1_tarski('#skF_1', A_445))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_2951, c_4291])).
% 8.20/3.26  tff(c_2630, plain, (![A_290, B_291, A_7]: (k1_relset_1(A_290, B_291, A_7)=k1_relat_1(A_7) | ~r1_tarski(A_7, k2_zfmisc_1(A_290, B_291)))), inference(resolution, [status(thm)], [c_20, c_2612])).
% 8.20/3.26  tff(c_4304, plain, (![A_445, B_446]: (k1_relset_1(A_445, B_446, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_3', B_446) | ~r1_tarski('#skF_1', A_445))), inference(resolution, [status(thm)], [c_4298, c_2630])).
% 8.20/3.26  tff(c_4359, plain, (![A_452, B_453]: (k1_relset_1(A_452, B_453, '#skF_4')='#skF_1' | ~r1_tarski('#skF_3', B_453) | ~r1_tarski('#skF_1', A_452))), inference(demodulation, [status(thm), theory('equality')], [c_2951, c_4304])).
% 8.20/3.26  tff(c_4364, plain, (![A_454]: (k1_relset_1(A_454, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_454))), inference(resolution, [status(thm)], [c_6, c_4359])).
% 8.20/3.26  tff(c_4369, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_4364])).
% 8.20/3.26  tff(c_4374, plain, (![C_455, A_456]: (r1_tarski(C_455, k2_zfmisc_1(A_456, k2_relat_1(C_455))) | ~r1_tarski(k1_relat_1(C_455), A_456) | ~v1_relat_1(C_455))), inference(resolution, [status(thm)], [c_6, c_4289])).
% 8.20/3.26  tff(c_4418, plain, (![A_456]: (r1_tarski('#skF_4', k2_zfmisc_1(A_456, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_456) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2693, c_4374])).
% 8.20/3.26  tff(c_4437, plain, (![A_456]: (r1_tarski('#skF_4', k2_zfmisc_1(A_456, '#skF_3')) | ~r1_tarski('#skF_1', A_456))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_2951, c_4418])).
% 8.20/3.26  tff(c_4630, plain, (![B_465, A_466, A_467]: (k1_xboole_0=B_465 | k1_relset_1(A_466, B_465, A_467)=A_466 | ~v1_funct_2(A_467, A_466, B_465) | ~r1_tarski(A_467, k2_zfmisc_1(A_466, B_465)))), inference(resolution, [status(thm)], [c_20, c_2925])).
% 8.20/3.26  tff(c_4661, plain, (![A_456]: (k1_xboole_0='#skF_3' | k1_relset_1(A_456, '#skF_3', '#skF_4')=A_456 | ~v1_funct_2('#skF_4', A_456, '#skF_3') | ~r1_tarski('#skF_1', A_456))), inference(resolution, [status(thm)], [c_4437, c_4630])).
% 8.20/3.26  tff(c_4766, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_4661])).
% 8.20/3.26  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.20/3.26  tff(c_3972, plain, (![C_429, A_430]: (m1_subset_1(C_429, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_429), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_429), A_430) | ~v1_relat_1(C_429))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2787])).
% 8.20/3.26  tff(c_3974, plain, (![A_430]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), A_430) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2693, c_3972])).
% 8.20/3.26  tff(c_3976, plain, (![A_430]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_1', A_430))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_2951, c_3974])).
% 8.20/3.26  tff(c_3977, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3976])).
% 8.20/3.26  tff(c_4779, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4766, c_3977])).
% 8.20/3.26  tff(c_4840, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4779])).
% 8.20/3.26  tff(c_4842, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_4661])).
% 8.20/3.26  tff(c_3036, plain, (![B_343, C_344, A_345]: (k1_xboole_0=B_343 | v1_funct_2(C_344, A_345, B_343) | k1_relset_1(A_345, B_343, C_344)!=A_345 | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(A_345, B_343))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.20/3.26  tff(c_5189, plain, (![B_494, A_495, A_496]: (k1_xboole_0=B_494 | v1_funct_2(A_495, A_496, B_494) | k1_relset_1(A_496, B_494, A_495)!=A_496 | ~r1_tarski(A_495, k2_zfmisc_1(A_496, B_494)))), inference(resolution, [status(thm)], [c_20, c_3036])).
% 8.20/3.26  tff(c_5192, plain, (![A_456]: (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', A_456, '#skF_3') | k1_relset_1(A_456, '#skF_3', '#skF_4')!=A_456 | ~r1_tarski('#skF_1', A_456))), inference(resolution, [status(thm)], [c_4437, c_5189])).
% 8.20/3.26  tff(c_5235, plain, (![A_497]: (v1_funct_2('#skF_4', A_497, '#skF_3') | k1_relset_1(A_497, '#skF_3', '#skF_4')!=A_497 | ~r1_tarski('#skF_1', A_497))), inference(negUnitSimplification, [status(thm)], [c_4842, c_5192])).
% 8.20/3.26  tff(c_5244, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_5235, c_160])).
% 8.20/3.26  tff(c_5250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4369, c_5244])).
% 8.20/3.26  tff(c_5252, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_3976])).
% 8.20/3.26  tff(c_5281, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_5252, c_8])).
% 8.20/3.26  tff(c_2538, plain, (![C_270, A_271]: (v4_relat_1(C_270, A_271) | ~m1_subset_1(C_270, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2456])).
% 8.20/3.26  tff(c_2545, plain, (![A_7, A_271]: (v4_relat_1(A_7, A_271) | ~r1_tarski(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_2538])).
% 8.20/3.26  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.20/3.26  tff(c_161, plain, (![C_48]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_141])).
% 8.20/3.26  tff(c_170, plain, (![A_7]: (v1_relat_1(A_7) | ~r1_tarski(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_161])).
% 8.20/3.26  tff(c_241, plain, (![B_57]: (v1_relat_1(k1_relat_1(B_57)) | ~v4_relat_1(B_57, k1_xboole_0) | ~v1_relat_1(B_57))), inference(resolution, [status(thm)], [c_225, c_170])).
% 8.20/3.26  tff(c_2965, plain, (v1_relat_1('#skF_1') | ~v4_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2951, c_241])).
% 8.20/3.26  tff(c_2976, plain, (v1_relat_1('#skF_1') | ~v4_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_158, c_2965])).
% 8.20/3.26  tff(c_2984, plain, (~v4_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2976])).
% 8.20/3.26  tff(c_2988, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_2545, c_2984])).
% 8.20/3.26  tff(c_5379, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5281, c_2988])).
% 8.20/3.26  tff(c_5251, plain, (![A_430]: (~r1_tarski('#skF_1', A_430) | m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_3976])).
% 8.20/3.26  tff(c_5350, plain, (![A_498]: (~r1_tarski('#skF_1', A_498))), inference(splitLeft, [status(thm)], [c_5251])).
% 8.20/3.26  tff(c_5355, plain, $false, inference(resolution, [status(thm)], [c_6, c_5350])).
% 8.20/3.26  tff(c_5356, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_5251])).
% 8.20/3.26  tff(c_5554, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5281, c_5356])).
% 8.20/3.26  tff(c_5559, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_5554, c_18])).
% 8.20/3.26  tff(c_5564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5379, c_5559])).
% 8.20/3.26  tff(c_5566, plain, (v4_relat_1('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2976])).
% 8.20/3.26  tff(c_5569, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_5566, c_243])).
% 8.20/3.26  tff(c_5572, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_2951, c_5569])).
% 8.20/3.26  tff(c_5616, plain, (![A_6]: (r1_tarski('#skF_1', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_5572, c_117])).
% 8.20/3.26  tff(c_5621, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5572, c_5572, c_14])).
% 8.20/3.26  tff(c_116, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_105])).
% 8.20/3.26  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.20/3.26  tff(c_140, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_116, c_2])).
% 8.20/3.26  tff(c_2520, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_140])).
% 8.20/3.26  tff(c_5790, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5621, c_2520])).
% 8.20/3.26  tff(c_5795, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5616, c_5790])).
% 8.20/3.26  tff(c_5796, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_4'), inference(splitRight, [status(thm)], [c_140])).
% 8.20/3.26  tff(c_6875, plain, (![B_668, C_669, A_670]: (k1_xboole_0=B_668 | v1_funct_2(C_669, A_670, B_668) | k1_relset_1(A_670, B_668, C_669)!=A_670 | ~m1_subset_1(C_669, k1_zfmisc_1(k2_zfmisc_1(A_670, B_668))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.20/3.26  tff(c_6881, plain, (![C_669]: (k1_xboole_0='#skF_2' | v1_funct_2(C_669, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_669)!='#skF_1' | ~m1_subset_1(C_669, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5796, c_6875])).
% 8.20/3.26  tff(c_6967, plain, (![C_676]: (v1_funct_2(C_676, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_676)!='#skF_1' | ~m1_subset_1(C_676, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_72, c_6881])).
% 8.20/3.26  tff(c_6978, plain, (v1_funct_2(k1_xboole_0, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', k1_xboole_0)!='#skF_1'), inference(resolution, [status(thm)], [c_16, c_6967])).
% 8.20/3.26  tff(c_6983, plain, (v1_funct_2(k1_xboole_0, '#skF_1', '#skF_2') | k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6259, c_6978])).
% 8.20/3.26  tff(c_6984, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_6983])).
% 8.20/3.26  tff(c_5799, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5796, c_58])).
% 8.20/3.26  tff(c_6292, plain, (![C_596]: (k1_relset_1('#skF_1', '#skF_2', C_596)=k1_relat_1(C_596) | ~m1_subset_1(C_596, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5796, c_6239])).
% 8.20/3.26  tff(c_6304, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_5799, c_6292])).
% 8.20/3.26  tff(c_7207, plain, (![B_680, A_681, C_682]: (k1_xboole_0=B_680 | k1_relset_1(A_681, B_680, C_682)=A_681 | ~v1_funct_2(C_682, A_681, B_680) | ~m1_subset_1(C_682, k1_zfmisc_1(k2_zfmisc_1(A_681, B_680))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.20/3.26  tff(c_7213, plain, (![C_682]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_682)='#skF_1' | ~v1_funct_2(C_682, '#skF_1', '#skF_2') | ~m1_subset_1(C_682, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5796, c_7207])).
% 8.20/3.26  tff(c_7306, plain, (![C_688]: (k1_relset_1('#skF_1', '#skF_2', C_688)='#skF_1' | ~v1_funct_2(C_688, '#skF_1', '#skF_2') | ~m1_subset_1(C_688, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_72, c_7213])).
% 8.20/3.26  tff(c_7309, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_5799, c_7306])).
% 8.20/3.26  tff(c_7320, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6304, c_7309])).
% 8.20/3.26  tff(c_6127, plain, (![A_572, B_573, C_574]: (k2_relset_1(A_572, B_573, C_574)=k2_relat_1(C_574) | ~m1_subset_1(C_574, k1_zfmisc_1(k2_zfmisc_1(A_572, B_573))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.20/3.26  tff(c_6165, plain, (![C_579]: (k2_relset_1('#skF_1', '#skF_2', C_579)=k2_relat_1(C_579) | ~m1_subset_1(C_579, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5796, c_6127])).
% 8.20/3.26  tff(c_6168, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_5799, c_6165])).
% 8.20/3.26  tff(c_6178, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2445, c_6168])).
% 8.20/3.26  tff(c_6714, plain, (![C_646, A_647, B_648]: (m1_subset_1(C_646, k1_zfmisc_1(k2_zfmisc_1(A_647, B_648))) | ~r1_tarski(k2_relat_1(C_646), B_648) | ~r1_tarski(k1_relat_1(C_646), A_647) | ~v1_relat_1(C_646))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.20/3.26  tff(c_7656, plain, (![C_708, A_709, B_710]: (r1_tarski(C_708, k2_zfmisc_1(A_709, B_710)) | ~r1_tarski(k2_relat_1(C_708), B_710) | ~r1_tarski(k1_relat_1(C_708), A_709) | ~v1_relat_1(C_708))), inference(resolution, [status(thm)], [c_6714, c_18])).
% 8.20/3.26  tff(c_7658, plain, (![A_709, B_710]: (r1_tarski('#skF_4', k2_zfmisc_1(A_709, B_710)) | ~r1_tarski('#skF_3', B_710) | ~r1_tarski(k1_relat_1('#skF_4'), A_709) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6178, c_7656])).
% 8.20/3.26  tff(c_7939, plain, (![A_725, B_726]: (r1_tarski('#skF_4', k2_zfmisc_1(A_725, B_726)) | ~r1_tarski('#skF_3', B_726) | ~r1_tarski('#skF_1', A_725))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_7320, c_7658])).
% 8.20/3.26  tff(c_6257, plain, (![A_587, B_588, A_7]: (k1_relset_1(A_587, B_588, A_7)=k1_relat_1(A_7) | ~r1_tarski(A_7, k2_zfmisc_1(A_587, B_588)))), inference(resolution, [status(thm)], [c_20, c_6239])).
% 8.20/3.26  tff(c_7948, plain, (![A_725, B_726]: (k1_relset_1(A_725, B_726, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_3', B_726) | ~r1_tarski('#skF_1', A_725))), inference(resolution, [status(thm)], [c_7939, c_6257])).
% 8.20/3.26  tff(c_8106, plain, (![A_739, B_740]: (k1_relset_1(A_739, B_740, '#skF_4')='#skF_1' | ~r1_tarski('#skF_3', B_740) | ~r1_tarski('#skF_1', A_739))), inference(demodulation, [status(thm), theory('equality')], [c_7320, c_7948])).
% 8.20/3.26  tff(c_8111, plain, (![A_741]: (k1_relset_1(A_741, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_741))), inference(resolution, [status(thm)], [c_6, c_8106])).
% 8.20/3.26  tff(c_8116, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_8111])).
% 8.20/3.26  tff(c_38, plain, (![C_28, A_26, B_27]: (m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~r1_tarski(k2_relat_1(C_28), B_27) | ~r1_tarski(k1_relat_1(C_28), A_26) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.20/3.26  tff(c_9623, plain, (![B_800, C_801, A_802]: (k1_xboole_0=B_800 | v1_funct_2(C_801, A_802, B_800) | k1_relset_1(A_802, B_800, C_801)!=A_802 | ~r1_tarski(k2_relat_1(C_801), B_800) | ~r1_tarski(k1_relat_1(C_801), A_802) | ~v1_relat_1(C_801))), inference(resolution, [status(thm)], [c_38, c_6875])).
% 8.20/3.26  tff(c_9628, plain, (![B_800, A_802]: (k1_xboole_0=B_800 | v1_funct_2('#skF_4', A_802, B_800) | k1_relset_1(A_802, B_800, '#skF_4')!=A_802 | ~r1_tarski('#skF_3', B_800) | ~r1_tarski(k1_relat_1('#skF_4'), A_802) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6178, c_9623])).
% 8.20/3.26  tff(c_9756, plain, (![B_807, A_808]: (k1_xboole_0=B_807 | v1_funct_2('#skF_4', A_808, B_807) | k1_relset_1(A_808, B_807, '#skF_4')!=A_808 | ~r1_tarski('#skF_3', B_807) | ~r1_tarski('#skF_1', A_808))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_7320, c_9628])).
% 8.20/3.26  tff(c_9771, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_9756, c_160])).
% 8.20/3.26  tff(c_9784, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_8116, c_9771])).
% 8.20/3.26  tff(c_7543, plain, (![C_698, A_699]: (m1_subset_1(C_698, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_698), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_698), A_699) | ~v1_relat_1(C_698))), inference(superposition, [status(thm), theory('equality')], [c_12, c_6714])).
% 8.20/3.26  tff(c_7545, plain, (![A_699]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), A_699) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6178, c_7543])).
% 8.20/3.26  tff(c_7547, plain, (![A_699]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_1', A_699))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_7320, c_7545])).
% 8.20/3.26  tff(c_7811, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_7547])).
% 8.20/3.26  tff(c_9820, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9784, c_7811])).
% 8.20/3.26  tff(c_9886, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_9820])).
% 8.20/3.26  tff(c_9888, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_7547])).
% 8.20/3.26  tff(c_9904, plain, (k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_9888, c_2])).
% 8.20/3.26  tff(c_9916, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_9904])).
% 8.20/3.26  tff(c_5882, plain, (![C_529, A_530]: (v4_relat_1(C_529, A_530) | ~m1_subset_1(C_529, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2456])).
% 8.20/3.26  tff(c_5889, plain, (![A_7, A_530]: (v4_relat_1(A_7, A_530) | ~r1_tarski(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_5882])).
% 8.20/3.26  tff(c_157, plain, (![A_7, A_46, B_47]: (v1_relat_1(A_7) | ~r1_tarski(A_7, k2_zfmisc_1(A_46, B_47)))), inference(resolution, [status(thm)], [c_20, c_141])).
% 8.20/3.26  tff(c_6088, plain, (![B_566, A_567, B_568]: (v1_relat_1(k1_relat_1(B_566)) | ~v4_relat_1(B_566, k2_zfmisc_1(A_567, B_568)) | ~v1_relat_1(B_566))), inference(resolution, [status(thm)], [c_225, c_157])).
% 8.20/3.26  tff(c_6110, plain, (![A_7]: (v1_relat_1(k1_relat_1(A_7)) | ~v1_relat_1(A_7) | ~r1_tarski(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_5889, c_6088])).
% 8.20/3.26  tff(c_7356, plain, (v1_relat_1('#skF_1') | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7320, c_6110])).
% 8.20/3.26  tff(c_7393, plain, (v1_relat_1('#skF_1') | ~r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_158, c_7356])).
% 8.20/3.26  tff(c_7414, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_7393])).
% 8.20/3.26  tff(c_9927, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9916, c_7414])).
% 8.20/3.26  tff(c_9978, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9916, c_9916, c_12])).
% 8.20/3.26  tff(c_10749, plain, (![C_860, A_861]: (r1_tarski(C_860, k2_zfmisc_1(A_861, k2_relat_1(C_860))) | ~r1_tarski(k1_relat_1(C_860), A_861) | ~v1_relat_1(C_860))), inference(resolution, [status(thm)], [c_6, c_7656])).
% 8.20/3.26  tff(c_10801, plain, (![A_861]: (r1_tarski('#skF_4', k2_zfmisc_1(A_861, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_861) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6178, c_10749])).
% 8.20/3.26  tff(c_10818, plain, (![A_861]: (r1_tarski('#skF_4', '#skF_3') | ~r1_tarski('#skF_1', A_861))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_7320, c_9978, c_10801])).
% 8.20/3.26  tff(c_10821, plain, (![A_862]: (~r1_tarski('#skF_1', A_862))), inference(negUnitSimplification, [status(thm)], [c_9927, c_10818])).
% 8.20/3.26  tff(c_10831, plain, $false, inference(resolution, [status(thm)], [c_6, c_10821])).
% 8.20/3.26  tff(c_10833, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_7393])).
% 8.20/3.26  tff(c_5892, plain, (![A_531, A_532]: (v4_relat_1(A_531, A_532) | ~r1_tarski(A_531, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_5882])).
% 8.20/3.26  tff(c_5897, plain, (![A_531]: (k1_relat_1(A_531)=k1_xboole_0 | ~v1_relat_1(A_531) | ~r1_tarski(A_531, k1_xboole_0))), inference(resolution, [status(thm)], [c_5892, c_243])).
% 8.20/3.26  tff(c_10844, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10833, c_5897])).
% 8.20/3.26  tff(c_10863, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_7320, c_10844])).
% 8.20/3.26  tff(c_10865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6984, c_10863])).
% 8.20/3.26  tff(c_10867, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_6983])).
% 8.20/3.26  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.20/3.26  tff(c_5811, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5796, c_10])).
% 8.20/3.26  tff(c_5817, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_72, c_5811])).
% 8.20/3.26  tff(c_5824, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_5817])).
% 8.20/3.26  tff(c_10899, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10867, c_5824])).
% 8.20/3.26  tff(c_11377, plain, (![B_877]: (k2_zfmisc_1('#skF_1', B_877)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10867, c_10867, c_14])).
% 8.20/3.26  tff(c_11445, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_11377, c_5796])).
% 8.20/3.26  tff(c_11475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10899, c_11445])).
% 8.20/3.26  tff(c_11477, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_5817])).
% 8.20/3.26  tff(c_11476, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_5817])).
% 8.20/3.26  tff(c_11497, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11477, c_11476])).
% 8.20/3.26  tff(c_11478, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11476, c_11476, c_2494])).
% 8.20/3.26  tff(c_11519, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11497, c_11497, c_11478])).
% 8.20/3.26  tff(c_11489, plain, (![A_6]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_11476, c_16])).
% 8.20/3.26  tff(c_11554, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_11497, c_11489])).
% 8.20/3.26  tff(c_11782, plain, (![A_907, B_908, C_909]: (k1_relset_1(A_907, B_908, C_909)=k1_relat_1(C_909) | ~m1_subset_1(C_909, k1_zfmisc_1(k2_zfmisc_1(A_907, B_908))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.20/3.26  tff(c_11792, plain, (![A_907, B_908]: (k1_relset_1(A_907, B_908, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_11554, c_11782])).
% 8.20/3.26  tff(c_11798, plain, (![A_907, B_908]: (k1_relset_1(A_907, B_908, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11519, c_11792])).
% 8.20/3.26  tff(c_44, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_30))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.20/3.26  tff(c_68, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_44])).
% 8.20/3.26  tff(c_11845, plain, (![C_922, B_923]: (v1_funct_2(C_922, '#skF_4', B_923) | k1_relset_1('#skF_4', B_923, C_922)!='#skF_4' | ~m1_subset_1(C_922, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11477, c_11477, c_11477, c_11477, c_68])).
% 8.20/3.26  tff(c_11848, plain, (![B_923]: (v1_funct_2('#skF_4', '#skF_4', B_923) | k1_relset_1('#skF_4', B_923, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_11554, c_11845])).
% 8.20/3.26  tff(c_11854, plain, (![B_923]: (v1_funct_2('#skF_4', '#skF_4', B_923))), inference(demodulation, [status(thm), theory('equality')], [c_11798, c_11848])).
% 8.20/3.26  tff(c_11506, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11497, c_160])).
% 8.20/3.26  tff(c_11859, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11854, c_11506])).
% 8.20/3.26  tff(c_11860, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_64])).
% 8.20/3.26  tff(c_12287, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12270, c_11860])).
% 8.20/3.26  tff(c_12307, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_12222, c_12287])).
% 8.20/3.26  tff(c_12312, plain, (~v4_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_12307])).
% 8.20/3.26  tff(c_12316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_11958, c_12312])).
% 8.20/3.26  tff(c_12317, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_54])).
% 8.20/3.26  tff(c_12329, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12317, c_12317, c_14])).
% 8.20/3.26  tff(c_12318, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_54])).
% 8.20/3.26  tff(c_12323, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12317, c_12318])).
% 8.20/3.26  tff(c_12365, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12329, c_12323, c_58])).
% 8.20/3.26  tff(c_12368, plain, (![A_997, B_998]: (r1_tarski(A_997, B_998) | ~m1_subset_1(A_997, k1_zfmisc_1(B_998)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.20/3.26  tff(c_12379, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_12365, c_12368])).
% 8.20/3.26  tff(c_12355, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12317, c_12317, c_8])).
% 8.20/3.26  tff(c_12384, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_12379, c_12355])).
% 8.20/3.26  tff(c_12353, plain, (![A_6]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_12317, c_16])).
% 8.20/3.26  tff(c_12390, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_12384, c_12353])).
% 8.20/3.26  tff(c_12444, plain, (![C_1005, A_1006, B_1007]: (v1_relat_1(C_1005) | ~m1_subset_1(C_1005, k1_zfmisc_1(k2_zfmisc_1(A_1006, B_1007))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.20/3.26  tff(c_12457, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12390, c_12444])).
% 8.20/3.26  tff(c_12652, plain, (![C_1043, A_1044, B_1045]: (v4_relat_1(C_1043, A_1044) | ~m1_subset_1(C_1043, k1_zfmisc_1(k2_zfmisc_1(A_1044, B_1045))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.20/3.26  tff(c_12669, plain, (![A_1046]: (v4_relat_1('#skF_4', A_1046))), inference(resolution, [status(thm)], [c_12390, c_12652])).
% 8.20/3.26  tff(c_12587, plain, (![B_1029, A_1030]: (r1_tarski(k1_relat_1(B_1029), A_1030) | ~v4_relat_1(B_1029, A_1030) | ~v1_relat_1(B_1029))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.20/3.26  tff(c_12389, plain, (![A_3]: (A_3='#skF_4' | ~r1_tarski(A_3, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12384, c_12384, c_12355])).
% 8.20/3.26  tff(c_12605, plain, (![B_1029]: (k1_relat_1(B_1029)='#skF_4' | ~v4_relat_1(B_1029, '#skF_4') | ~v1_relat_1(B_1029))), inference(resolution, [status(thm)], [c_12587, c_12389])).
% 8.20/3.26  tff(c_12673, plain, (k1_relat_1('#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12669, c_12605])).
% 8.20/3.26  tff(c_12676, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12457, c_12673])).
% 8.20/3.26  tff(c_12807, plain, (![A_1068, B_1069, C_1070]: (k1_relset_1(A_1068, B_1069, C_1070)=k1_relat_1(C_1070) | ~m1_subset_1(C_1070, k1_zfmisc_1(k2_zfmisc_1(A_1068, B_1069))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.20/3.26  tff(c_12817, plain, (![A_1068, B_1069]: (k1_relset_1(A_1068, B_1069, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_12390, c_12807])).
% 8.20/3.26  tff(c_12823, plain, (![A_1068, B_1069]: (k1_relset_1(A_1068, B_1069, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12676, c_12817])).
% 8.20/3.26  tff(c_12395, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12384, c_12317])).
% 8.20/3.26  tff(c_12889, plain, (![C_1083, B_1084]: (v1_funct_2(C_1083, '#skF_4', B_1084) | k1_relset_1('#skF_4', B_1084, C_1083)!='#skF_4' | ~m1_subset_1(C_1083, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_12395, c_12395, c_12395, c_12395, c_68])).
% 8.20/3.26  tff(c_12892, plain, (![B_1084]: (v1_funct_2('#skF_4', '#skF_4', B_1084) | k1_relset_1('#skF_4', B_1084, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_12390, c_12889])).
% 8.20/3.26  tff(c_12898, plain, (![B_1084]: (v1_funct_2('#skF_4', '#skF_4', B_1084))), inference(demodulation, [status(thm), theory('equality')], [c_12823, c_12892])).
% 8.20/3.26  tff(c_12413, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12384, c_12384, c_64])).
% 8.20/3.26  tff(c_12414, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_12413])).
% 8.20/3.26  tff(c_12903, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12898, c_12414])).
% 8.20/3.26  tff(c_12904, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_12413])).
% 8.20/3.26  tff(c_12963, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12390, c_12904])).
% 8.20/3.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.20/3.26  
% 8.20/3.26  Inference rules
% 8.20/3.26  ----------------------
% 8.20/3.26  #Ref     : 0
% 8.20/3.26  #Sup     : 2621
% 8.20/3.26  #Fact    : 0
% 8.20/3.26  #Define  : 0
% 8.20/3.26  #Split   : 26
% 8.20/3.26  #Chain   : 0
% 8.20/3.26  #Close   : 0
% 8.20/3.26  
% 8.20/3.26  Ordering : KBO
% 8.20/3.26  
% 8.20/3.26  Simplification rules
% 8.20/3.26  ----------------------
% 8.20/3.26  #Subsume      : 447
% 8.20/3.26  #Demod        : 3882
% 8.20/3.26  #Tautology    : 1273
% 8.20/3.26  #SimpNegUnit  : 62
% 8.20/3.26  #BackRed      : 569
% 8.20/3.26  
% 8.20/3.26  #Partial instantiations: 0
% 8.20/3.26  #Strategies tried      : 1
% 8.20/3.26  
% 8.20/3.26  Timing (in seconds)
% 8.20/3.26  ----------------------
% 8.20/3.26  Preprocessing        : 0.54
% 8.20/3.26  Parsing              : 0.28
% 8.20/3.26  CNF conversion       : 0.03
% 8.20/3.27  Main loop            : 1.88
% 8.20/3.27  Inferencing          : 0.59
% 8.20/3.27  Reduction            : 0.70
% 8.20/3.27  Demodulation         : 0.51
% 8.20/3.27  BG Simplification    : 0.07
% 8.20/3.27  Subsumption          : 0.37
% 8.20/3.27  Abstraction          : 0.07
% 8.20/3.27  MUC search           : 0.00
% 8.20/3.27  Cooper               : 0.00
% 8.20/3.27  Total                : 2.51
% 8.20/3.27  Index Insertion      : 0.00
% 8.20/3.27  Index Deletion       : 0.00
% 8.20/3.27  Index Matching       : 0.00
% 8.20/3.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
