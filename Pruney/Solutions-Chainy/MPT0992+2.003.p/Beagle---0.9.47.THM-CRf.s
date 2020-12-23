%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:31 EST 2020

% Result     : Theorem 13.13s
% Output     : CNFRefutation 13.63s
% Verified   : 
% Statistics : Number of formulae       :  209 (2461 expanded)
%              Number of leaves         :   37 ( 811 expanded)
%              Depth                    :   17
%              Number of atoms          :  382 (7918 expanded)
%              Number of equality atoms :   98 (2118 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
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

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_58,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_247,plain,(
    ! [B_81,A_82] :
      ( v1_relat_1(B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_82))
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_250,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_247])).

tff(c_253,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_250])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_28005,plain,(
    ! [A_849,B_850,C_851] :
      ( k1_relset_1(A_849,B_850,C_851) = k1_relat_1(C_851)
      | ~ m1_subset_1(C_851,k1_zfmisc_1(k2_zfmisc_1(A_849,B_850))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28013,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_28005])).

tff(c_28254,plain,(
    ! [B_884,A_885,C_886] :
      ( k1_xboole_0 = B_884
      | k1_relset_1(A_885,B_884,C_886) = A_885
      | ~ v1_funct_2(C_886,A_885,B_884)
      | ~ m1_subset_1(C_886,k1_zfmisc_1(k2_zfmisc_1(A_885,B_884))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28263,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_28254])).

tff(c_28270,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_28013,c_28263])).

tff(c_28271,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_28270])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,A_13)) = A_13
      | ~ r1_tarski(A_13,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28291,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28271,c_20])).

tff(c_28324,plain,(
    ! [A_888] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_888)) = A_888
      | ~ r1_tarski(A_888,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_28291])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_28142,plain,(
    ! [A_874,B_875,C_876,D_877] :
      ( k2_partfun1(A_874,B_875,C_876,D_877) = k7_relat_1(C_876,D_877)
      | ~ m1_subset_1(C_876,k1_zfmisc_1(k2_zfmisc_1(A_874,B_875)))
      | ~ v1_funct_1(C_876) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_28148,plain,(
    ! [D_877] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_877) = k7_relat_1('#skF_4',D_877)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_28142])).

tff(c_28155,plain,(
    ! [D_877] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_877) = k7_relat_1('#skF_4',D_877) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_28148])).

tff(c_540,plain,(
    ! [A_137,B_138,C_139,D_140] :
      ( k2_partfun1(A_137,B_138,C_139,D_140) = k7_relat_1(C_139,D_140)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138)))
      | ~ v1_funct_1(C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_544,plain,(
    ! [D_140] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_140) = k7_relat_1('#skF_4',D_140)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_540])).

tff(c_548,plain,(
    ! [D_140] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_140) = k7_relat_1('#skF_4',D_140) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_544])).

tff(c_912,plain,(
    ! [A_165,B_166,C_167,D_168] :
      ( m1_subset_1(k2_partfun1(A_165,B_166,C_167,D_168),k1_zfmisc_1(k2_zfmisc_1(A_165,B_166)))
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166)))
      | ~ v1_funct_1(C_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_952,plain,(
    ! [D_140] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_140),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_912])).

tff(c_975,plain,(
    ! [D_169] : m1_subset_1(k7_relat_1('#skF_4',D_169),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_952])).

tff(c_22,plain,(
    ! [C_17,A_15,B_16] :
      ( v1_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1022,plain,(
    ! [D_169] : v1_relat_1(k7_relat_1('#skF_4',D_169)) ),
    inference(resolution,[status(thm)],[c_975,c_22])).

tff(c_24,plain,(
    ! [C_20,B_19,A_18] :
      ( v5_relat_1(C_20,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1021,plain,(
    ! [D_169] : v5_relat_1(k7_relat_1('#skF_4',D_169),'#skF_2') ),
    inference(resolution,[status(thm)],[c_975,c_24])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_413,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( v1_funct_1(k2_partfun1(A_115,B_116,C_117,D_118))
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_1(C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_415,plain,(
    ! [D_118] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_118))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_413])).

tff(c_418,plain,(
    ! [D_118] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_118)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_415])).

tff(c_549,plain,(
    ! [D_118] : v1_funct_1(k7_relat_1('#skF_4',D_118)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_418])).

tff(c_26,plain,(
    ! [C_20,A_18,B_19] :
      ( v4_relat_1(C_20,A_18)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1064,plain,(
    ! [D_173] : v4_relat_1(k7_relat_1('#skF_4',D_173),'#skF_1') ),
    inference(resolution,[status(thm)],[c_975,c_26])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1067,plain,(
    ! [D_173] :
      ( k7_relat_1(k7_relat_1('#skF_4',D_173),'#skF_1') = k7_relat_1('#skF_4',D_173)
      | ~ v1_relat_1(k7_relat_1('#skF_4',D_173)) ) ),
    inference(resolution,[status(thm)],[c_1064,c_18])).

tff(c_1076,plain,(
    ! [D_173] : k7_relat_1(k7_relat_1('#skF_4',D_173),'#skF_1') = k7_relat_1('#skF_4',D_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_1067])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_422,plain,(
    ! [B_122,A_123] :
      ( m1_subset_1(B_122,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_122),A_123)))
      | ~ r1_tarski(k2_relat_1(B_122),A_123)
      | ~ v1_funct_1(B_122)
      | ~ v1_relat_1(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_464,plain,(
    ! [B_124,A_125] :
      ( v4_relat_1(B_124,k1_relat_1(B_124))
      | ~ r1_tarski(k2_relat_1(B_124),A_125)
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124) ) ),
    inference(resolution,[status(thm)],[c_422,c_26])).

tff(c_471,plain,(
    ! [B_126] :
      ( v4_relat_1(B_126,k1_relat_1(B_126))
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126) ) ),
    inference(resolution,[status(thm)],[c_6,c_464])).

tff(c_481,plain,(
    ! [B_126] :
      ( k7_relat_1(B_126,k1_relat_1(B_126)) = B_126
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126) ) ),
    inference(resolution,[status(thm)],[c_471,c_18])).

tff(c_46,plain,(
    ! [A_31,B_32,C_33,D_34] :
      ( k2_partfun1(A_31,B_32,C_33,D_34) = k7_relat_1(C_33,D_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_983,plain,(
    ! [D_169,D_34] :
      ( k2_partfun1('#skF_1','#skF_2',k7_relat_1('#skF_4',D_169),D_34) = k7_relat_1(k7_relat_1('#skF_4',D_169),D_34)
      | ~ v1_funct_1(k7_relat_1('#skF_4',D_169)) ) ),
    inference(resolution,[status(thm)],[c_975,c_46])).

tff(c_1015,plain,(
    ! [D_169,D_34] : k2_partfun1('#skF_1','#skF_2',k7_relat_1('#skF_4',D_169),D_34) = k7_relat_1(k7_relat_1('#skF_4',D_169),D_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_983])).

tff(c_968,plain,(
    ! [D_140] : m1_subset_1(k7_relat_1('#skF_4',D_140),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_952])).

tff(c_10,plain,(
    ! [B_6,A_4] :
      ( v1_relat_1(B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_4))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_949,plain,(
    ! [A_165,B_166,C_167,D_168] :
      ( v1_relat_1(k2_partfun1(A_165,B_166,C_167,D_168))
      | ~ v1_relat_1(k2_zfmisc_1(A_165,B_166))
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166)))
      | ~ v1_funct_1(C_167) ) ),
    inference(resolution,[status(thm)],[c_912,c_10])).

tff(c_1090,plain,(
    ! [A_176,B_177,C_178,D_179] :
      ( v1_relat_1(k2_partfun1(A_176,B_177,C_178,D_179))
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ v1_funct_1(C_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_949])).

tff(c_1092,plain,(
    ! [D_140,D_179] :
      ( v1_relat_1(k2_partfun1('#skF_1','#skF_2',k7_relat_1('#skF_4',D_140),D_179))
      | ~ v1_funct_1(k7_relat_1('#skF_4',D_140)) ) ),
    inference(resolution,[status(thm)],[c_968,c_1090])).

tff(c_1103,plain,(
    ! [D_140,D_179] : v1_relat_1(k2_partfun1('#skF_1','#skF_2',k7_relat_1('#skF_4',D_140),D_179)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_1092])).

tff(c_1811,plain,(
    ! [D_140,D_179] : v1_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_140),D_179)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1015,c_1103])).

tff(c_1526,plain,(
    ! [A_195,B_196,C_197,D_198] :
      ( v4_relat_1(k2_partfun1(A_195,B_196,C_197,D_198),A_195)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196)))
      | ~ v1_funct_1(C_197) ) ),
    inference(resolution,[status(thm)],[c_912,c_26])).

tff(c_1528,plain,(
    ! [D_140,D_198] :
      ( v4_relat_1(k2_partfun1('#skF_1','#skF_2',k7_relat_1('#skF_4',D_140),D_198),'#skF_1')
      | ~ v1_funct_1(k7_relat_1('#skF_4',D_140)) ) ),
    inference(resolution,[status(thm)],[c_968,c_1526])).

tff(c_1539,plain,(
    ! [D_140,D_198] : v4_relat_1(k2_partfun1('#skF_1','#skF_2',k7_relat_1('#skF_4',D_140),D_198),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_1528])).

tff(c_1887,plain,(
    ! [D_212,D_213] : v4_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_212),D_213),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1015,c_1539])).

tff(c_1890,plain,(
    ! [D_212,D_213] :
      ( k7_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_212),D_213),'#skF_1') = k7_relat_1(k7_relat_1('#skF_4',D_212),D_213)
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_212),D_213)) ) ),
    inference(resolution,[status(thm)],[c_1887,c_18])).

tff(c_2317,plain,(
    ! [D_249,D_250] : k7_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_249),D_250),'#skF_1') = k7_relat_1(k7_relat_1('#skF_4',D_249),D_250) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1811,c_1890])).

tff(c_2340,plain,(
    ! [D_249] :
      ( k7_relat_1(k7_relat_1('#skF_4',D_249),k1_relat_1(k7_relat_1('#skF_4',D_249))) = k7_relat_1(k7_relat_1('#skF_4',D_249),'#skF_1')
      | ~ v1_funct_1(k7_relat_1('#skF_4',D_249))
      | ~ v1_relat_1(k7_relat_1('#skF_4',D_249)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_2317])).

tff(c_2352,plain,(
    ! [D_249] : k7_relat_1(k7_relat_1('#skF_4',D_249),k1_relat_1(k7_relat_1('#skF_4',D_249))) = k7_relat_1('#skF_4',D_249) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_549,c_1076,c_2340])).

tff(c_380,plain,(
    ! [A_108,B_109,C_110] :
      ( k1_relset_1(A_108,B_109,C_110) = k1_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_384,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_380])).

tff(c_596,plain,(
    ! [B_146,A_147,C_148] :
      ( k1_xboole_0 = B_146
      | k1_relset_1(A_147,B_146,C_148) = A_147
      | ~ v1_funct_2(C_148,A_147,B_146)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_147,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_602,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_596])).

tff(c_606,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_384,c_602])).

tff(c_607,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_606])).

tff(c_633,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_20])).

tff(c_651,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_633])).

tff(c_330,plain,(
    ! [B_103,A_104] :
      ( k1_relat_1(k7_relat_1(B_103,A_104)) = A_104
      | ~ r1_tarski(A_104,k1_relat_1(B_103))
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_344,plain,(
    ! [B_103] :
      ( k1_relat_1(k7_relat_1(B_103,k1_relat_1(B_103))) = k1_relat_1(B_103)
      | ~ v1_relat_1(B_103) ) ),
    inference(resolution,[status(thm)],[c_6,c_330])).

tff(c_18591,plain,(
    ! [B_659,A_660] :
      ( m1_subset_1(k7_relat_1(B_659,k1_relat_1(B_659)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_659),A_660)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1(B_659,k1_relat_1(B_659))),A_660)
      | ~ v1_funct_1(k7_relat_1(B_659,k1_relat_1(B_659)))
      | ~ v1_relat_1(k7_relat_1(B_659,k1_relat_1(B_659)))
      | ~ v1_relat_1(B_659) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_422])).

tff(c_18785,plain,(
    ! [A_13,A_660] :
      ( m1_subset_1(k7_relat_1(k7_relat_1('#skF_4',A_13),k1_relat_1(k7_relat_1('#skF_4',A_13))),k1_zfmisc_1(k2_zfmisc_1(A_13,A_660)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1('#skF_4',A_13),k1_relat_1(k7_relat_1('#skF_4',A_13)))),A_660)
      | ~ v1_funct_1(k7_relat_1(k7_relat_1('#skF_4',A_13),k1_relat_1(k7_relat_1('#skF_4',A_13))))
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_4',A_13),k1_relat_1(k7_relat_1('#skF_4',A_13))))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_13))
      | ~ r1_tarski(A_13,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_651,c_18591])).

tff(c_27756,plain,(
    ! [A_831,A_832] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_831),k1_zfmisc_1(k2_zfmisc_1(A_831,A_832)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_831)),A_832)
      | ~ r1_tarski(A_831,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_1022,c_2352,c_549,c_2352,c_2352,c_2352,c_18785])).

tff(c_236,plain,(
    ! [A_77,B_78,C_79,D_80] :
      ( v1_funct_1(k2_partfun1(A_77,B_78,C_79,D_80))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_funct_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_238,plain,(
    ! [D_80] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_80))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_236])).

tff(c_241,plain,(
    ! [D_80] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_80)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_238])).

tff(c_54,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_70,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_70])).

tff(c_245,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_297,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_550,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_297])).

tff(c_27784,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_27756,c_550])).

tff(c_27854,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_27784])).

tff(c_27885,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_27854])).

tff(c_27891,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_1021,c_27885])).

tff(c_27893,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_28012,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_27893,c_28005])).

tff(c_28156,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28155,c_28155,c_28012])).

tff(c_27892,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_28164,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28155,c_27892])).

tff(c_28163,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28155,c_27893])).

tff(c_36,plain,(
    ! [B_25,C_26,A_24] :
      ( k1_xboole_0 = B_25
      | v1_funct_2(C_26,A_24,B_25)
      | k1_relset_1(A_24,B_25,C_26) != A_24
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28203,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_28163,c_36])).

tff(c_28225,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_28164,c_68,c_28203])).

tff(c_28242,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28156,c_28225])).

tff(c_28330,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28324,c_28242])).

tff(c_28379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_28330])).

tff(c_28380,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_28381,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_28387,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28380,c_28381])).

tff(c_28395,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28387,c_60])).

tff(c_28396,plain,(
    ! [C_892,A_893,B_894] :
      ( v1_relat_1(C_892)
      | ~ m1_subset_1(C_892,k1_zfmisc_1(k2_zfmisc_1(A_893,B_894))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28400,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28395,c_28396])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28382,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28380,c_8])).

tff(c_28797,plain,(
    ! [C_943,B_944,A_945] :
      ( v5_relat_1(C_943,B_944)
      | ~ m1_subset_1(C_943,k1_zfmisc_1(k2_zfmisc_1(A_945,B_944))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28801,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_28395,c_28797])).

tff(c_28807,plain,(
    ! [B_949,A_950] :
      ( r1_tarski(k2_relat_1(B_949),A_950)
      | ~ v5_relat_1(B_949,A_950)
      | ~ v1_relat_1(B_949) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28753,plain,(
    ! [B_937,A_938] :
      ( B_937 = A_938
      | ~ r1_tarski(B_937,A_938)
      | ~ r1_tarski(A_938,B_937) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28760,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28382,c_28753])).

tff(c_28831,plain,(
    ! [B_953] :
      ( k2_relat_1(B_953) = '#skF_1'
      | ~ v5_relat_1(B_953,'#skF_1')
      | ~ v1_relat_1(B_953) ) ),
    inference(resolution,[status(thm)],[c_28807,c_28760])).

tff(c_28834,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28801,c_28831])).

tff(c_28837,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28400,c_28834])).

tff(c_28802,plain,(
    ! [C_946,A_947,B_948] :
      ( v4_relat_1(C_946,A_947)
      | ~ m1_subset_1(C_946,k1_zfmisc_1(k2_zfmisc_1(A_947,B_948))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28806,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_28395,c_28802])).

tff(c_28820,plain,(
    ! [B_951,A_952] :
      ( k7_relat_1(B_951,A_952) = B_951
      | ~ v4_relat_1(B_951,A_952)
      | ~ v1_relat_1(B_951) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28823,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28806,c_28820])).

tff(c_28826,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28400,c_28823])).

tff(c_28866,plain,(
    ! [B_955,A_956] :
      ( k1_relat_1(k7_relat_1(B_955,A_956)) = A_956
      | ~ r1_tarski(A_956,k1_relat_1(B_955))
      | ~ v1_relat_1(B_955) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28882,plain,(
    ! [B_957] :
      ( k1_relat_1(k7_relat_1(B_957,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_957) ) ),
    inference(resolution,[status(thm)],[c_28382,c_28866])).

tff(c_28894,plain,
    ( k1_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28826,c_28882])).

tff(c_28898,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28400,c_28894])).

tff(c_29091,plain,(
    ! [B_979,A_980] :
      ( m1_subset_1(B_979,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_979),A_980)))
      | ~ r1_tarski(k2_relat_1(B_979),A_980)
      | ~ v1_funct_1(B_979)
      | ~ v1_relat_1(B_979) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_29128,plain,(
    ! [A_980] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_980)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_980)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28898,c_29091])).

tff(c_29143,plain,(
    ! [A_980] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_980))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28400,c_64,c_28382,c_28837,c_29128])).

tff(c_29567,plain,(
    ! [A_1005,B_1006,C_1007,D_1008] :
      ( k2_partfun1(A_1005,B_1006,C_1007,D_1008) = k7_relat_1(C_1007,D_1008)
      | ~ m1_subset_1(C_1007,k1_zfmisc_1(k2_zfmisc_1(A_1005,B_1006)))
      | ~ v1_funct_1(C_1007) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_29569,plain,(
    ! [A_980,D_1008] :
      ( k2_partfun1('#skF_1',A_980,'#skF_4',D_1008) = k7_relat_1('#skF_4',D_1008)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_29143,c_29567])).

tff(c_29574,plain,(
    ! [A_980,D_1008] : k2_partfun1('#skF_1',A_980,'#skF_4',D_1008) = k7_relat_1('#skF_4',D_1008) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_29569])).

tff(c_28759,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_28753])).

tff(c_28767,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28382,c_28759])).

tff(c_28742,plain,(
    ! [A_933,B_934,C_935,D_936] :
      ( v1_funct_1(k2_partfun1(A_933,B_934,C_935,D_936))
      | ~ m1_subset_1(C_935,k1_zfmisc_1(k2_zfmisc_1(A_933,B_934)))
      | ~ v1_funct_1(C_935) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_28744,plain,(
    ! [D_936] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4',D_936))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28395,c_28742])).

tff(c_28747,plain,(
    ! [D_936] : v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4',D_936)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_28744])).

tff(c_28410,plain,(
    ! [B_897,A_898] :
      ( B_897 = A_898
      | ~ r1_tarski(B_897,A_898)
      | ~ r1_tarski(A_898,B_897) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28416,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_28410])).

tff(c_28424,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28382,c_28416])).

tff(c_28408,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28387,c_28387,c_28387,c_28387,c_28387,c_54])).

tff(c_28409,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_28408])).

tff(c_28425,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28424,c_28409])).

tff(c_28750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28747,c_28425])).

tff(c_28751,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_28408])).

tff(c_28795,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28767,c_28767,c_28767,c_28767,c_28751])).

tff(c_28796,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_28795])).

tff(c_29577,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29574,c_28796])).

tff(c_29580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_29143,c_28826,c_29577])).

tff(c_29582,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_28795])).

tff(c_29669,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_29582,c_22])).

tff(c_28752,plain,(
    v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_28408])).

tff(c_28768,plain,(
    v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28767,c_28752])).

tff(c_29665,plain,(
    v5_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_29582,c_24])).

tff(c_29589,plain,(
    ! [B_1014,A_1015] :
      ( r1_tarski(k2_relat_1(B_1014),A_1015)
      | ~ v5_relat_1(B_1014,A_1015)
      | ~ v1_relat_1(B_1014) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_29599,plain,(
    ! [B_1014] :
      ( k2_relat_1(B_1014) = '#skF_1'
      | ~ v5_relat_1(B_1014,'#skF_1')
      | ~ v1_relat_1(B_1014) ) ),
    inference(resolution,[status(thm)],[c_29589,c_28760])).

tff(c_29673,plain,
    ( k2_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_29665,c_29599])).

tff(c_29676,plain,(
    k2_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29669,c_29673])).

tff(c_29664,plain,(
    v4_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_29582,c_26])).

tff(c_29679,plain,
    ( k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1') = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_29664,c_18])).

tff(c_29682,plain,(
    k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1') = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29669,c_29679])).

tff(c_29711,plain,(
    ! [B_1022,A_1023] :
      ( k1_relat_1(k7_relat_1(B_1022,A_1023)) = A_1023
      | ~ r1_tarski(A_1023,k1_relat_1(B_1022))
      | ~ v1_relat_1(B_1022) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_29725,plain,(
    ! [B_1022] :
      ( k1_relat_1(k7_relat_1(B_1022,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_1022) ) ),
    inference(resolution,[status(thm)],[c_28382,c_29711])).

tff(c_29787,plain,
    ( k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_29682,c_29725])).

tff(c_29791,plain,(
    k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29669,c_29787])).

tff(c_29942,plain,(
    ! [B_1034,A_1035] :
      ( v1_funct_2(B_1034,k1_relat_1(B_1034),A_1035)
      | ~ r1_tarski(k2_relat_1(B_1034),A_1035)
      | ~ v1_funct_1(B_1034)
      | ~ v1_relat_1(B_1034) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_29951,plain,(
    ! [A_1035] :
      ( v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',A_1035)
      | ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')),A_1035)
      | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'))
      | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29791,c_29942])).

tff(c_29962,plain,(
    ! [A_1035] : v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',A_1035) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29669,c_28768,c_28382,c_29676,c_29951])).

tff(c_29581,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_28795])).

tff(c_29969,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_29962,c_29581])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n017.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 17:43:46 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.13/5.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.48/5.76  
% 13.48/5.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.48/5.76  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.48/5.76  
% 13.48/5.76  %Foreground sorts:
% 13.48/5.76  
% 13.48/5.76  
% 13.48/5.76  %Background operators:
% 13.48/5.76  
% 13.48/5.76  
% 13.48/5.76  %Foreground operators:
% 13.48/5.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.48/5.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.48/5.76  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 13.48/5.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.48/5.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.48/5.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.48/5.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.48/5.76  tff('#skF_2', type, '#skF_2': $i).
% 13.48/5.76  tff('#skF_3', type, '#skF_3': $i).
% 13.48/5.76  tff('#skF_1', type, '#skF_1': $i).
% 13.48/5.76  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.48/5.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.48/5.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.48/5.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.48/5.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.48/5.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.48/5.76  tff('#skF_4', type, '#skF_4': $i).
% 13.48/5.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.48/5.76  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 13.48/5.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.48/5.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.48/5.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.48/5.76  
% 13.63/5.79  tff(f_138, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 13.63/5.79  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 13.63/5.79  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 13.63/5.79  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.63/5.79  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 13.63/5.79  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 13.63/5.79  tff(f_106, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 13.63/5.79  tff(f_100, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 13.63/5.79  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.63/5.79  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.63/5.79  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 13.63/5.79  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 13.63/5.79  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.63/5.79  tff(f_118, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 13.63/5.79  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.63/5.79  tff(c_58, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 13.63/5.79  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.63/5.79  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 13.63/5.79  tff(c_247, plain, (![B_81, A_82]: (v1_relat_1(B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_82)) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_40])).
% 13.63/5.79  tff(c_250, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_247])).
% 13.63/5.79  tff(c_253, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_250])).
% 13.63/5.79  tff(c_56, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_138])).
% 13.63/5.79  tff(c_68, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_56])).
% 13.63/5.79  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 13.63/5.79  tff(c_28005, plain, (![A_849, B_850, C_851]: (k1_relset_1(A_849, B_850, C_851)=k1_relat_1(C_851) | ~m1_subset_1(C_851, k1_zfmisc_1(k2_zfmisc_1(A_849, B_850))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.63/5.79  tff(c_28013, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_28005])).
% 13.63/5.79  tff(c_28254, plain, (![B_884, A_885, C_886]: (k1_xboole_0=B_884 | k1_relset_1(A_885, B_884, C_886)=A_885 | ~v1_funct_2(C_886, A_885, B_884) | ~m1_subset_1(C_886, k1_zfmisc_1(k2_zfmisc_1(A_885, B_884))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.63/5.79  tff(c_28263, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_28254])).
% 13.63/5.79  tff(c_28270, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_28013, c_28263])).
% 13.63/5.79  tff(c_28271, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_68, c_28270])).
% 13.63/5.79  tff(c_20, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, A_13))=A_13 | ~r1_tarski(A_13, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.63/5.79  tff(c_28291, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_28271, c_20])).
% 13.63/5.79  tff(c_28324, plain, (![A_888]: (k1_relat_1(k7_relat_1('#skF_4', A_888))=A_888 | ~r1_tarski(A_888, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_28291])).
% 13.63/5.79  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 13.63/5.79  tff(c_28142, plain, (![A_874, B_875, C_876, D_877]: (k2_partfun1(A_874, B_875, C_876, D_877)=k7_relat_1(C_876, D_877) | ~m1_subset_1(C_876, k1_zfmisc_1(k2_zfmisc_1(A_874, B_875))) | ~v1_funct_1(C_876))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.63/5.79  tff(c_28148, plain, (![D_877]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_877)=k7_relat_1('#skF_4', D_877) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_28142])).
% 13.63/5.79  tff(c_28155, plain, (![D_877]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_877)=k7_relat_1('#skF_4', D_877))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_28148])).
% 13.63/5.79  tff(c_540, plain, (![A_137, B_138, C_139, D_140]: (k2_partfun1(A_137, B_138, C_139, D_140)=k7_relat_1(C_139, D_140) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))) | ~v1_funct_1(C_139))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.63/5.79  tff(c_544, plain, (![D_140]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_140)=k7_relat_1('#skF_4', D_140) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_540])).
% 13.63/5.79  tff(c_548, plain, (![D_140]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_140)=k7_relat_1('#skF_4', D_140))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_544])).
% 13.63/5.79  tff(c_912, plain, (![A_165, B_166, C_167, D_168]: (m1_subset_1(k2_partfun1(A_165, B_166, C_167, D_168), k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))) | ~v1_funct_1(C_167))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.63/5.79  tff(c_952, plain, (![D_140]: (m1_subset_1(k7_relat_1('#skF_4', D_140), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_548, c_912])).
% 13.63/5.79  tff(c_975, plain, (![D_169]: (m1_subset_1(k7_relat_1('#skF_4', D_169), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_952])).
% 13.63/5.79  tff(c_22, plain, (![C_17, A_15, B_16]: (v1_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.63/5.79  tff(c_1022, plain, (![D_169]: (v1_relat_1(k7_relat_1('#skF_4', D_169)))), inference(resolution, [status(thm)], [c_975, c_22])).
% 13.63/5.79  tff(c_24, plain, (![C_20, B_19, A_18]: (v5_relat_1(C_20, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.63/5.79  tff(c_1021, plain, (![D_169]: (v5_relat_1(k7_relat_1('#skF_4', D_169), '#skF_2'))), inference(resolution, [status(thm)], [c_975, c_24])).
% 13.63/5.79  tff(c_14, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.63/5.79  tff(c_413, plain, (![A_115, B_116, C_117, D_118]: (v1_funct_1(k2_partfun1(A_115, B_116, C_117, D_118)) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_1(C_117))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.63/5.79  tff(c_415, plain, (![D_118]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_118)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_413])).
% 13.63/5.79  tff(c_418, plain, (![D_118]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_118)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_415])).
% 13.63/5.79  tff(c_549, plain, (![D_118]: (v1_funct_1(k7_relat_1('#skF_4', D_118)))), inference(demodulation, [status(thm), theory('equality')], [c_548, c_418])).
% 13.63/5.79  tff(c_26, plain, (![C_20, A_18, B_19]: (v4_relat_1(C_20, A_18) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.63/5.79  tff(c_1064, plain, (![D_173]: (v4_relat_1(k7_relat_1('#skF_4', D_173), '#skF_1'))), inference(resolution, [status(thm)], [c_975, c_26])).
% 13.63/5.79  tff(c_18, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.63/5.79  tff(c_1067, plain, (![D_173]: (k7_relat_1(k7_relat_1('#skF_4', D_173), '#skF_1')=k7_relat_1('#skF_4', D_173) | ~v1_relat_1(k7_relat_1('#skF_4', D_173)))), inference(resolution, [status(thm)], [c_1064, c_18])).
% 13.63/5.79  tff(c_1076, plain, (![D_173]: (k7_relat_1(k7_relat_1('#skF_4', D_173), '#skF_1')=k7_relat_1('#skF_4', D_173))), inference(demodulation, [status(thm), theory('equality')], [c_1022, c_1067])).
% 13.63/5.79  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.63/5.79  tff(c_422, plain, (![B_122, A_123]: (m1_subset_1(B_122, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_122), A_123))) | ~r1_tarski(k2_relat_1(B_122), A_123) | ~v1_funct_1(B_122) | ~v1_relat_1(B_122))), inference(cnfTransformation, [status(thm)], [f_118])).
% 13.63/5.79  tff(c_464, plain, (![B_124, A_125]: (v4_relat_1(B_124, k1_relat_1(B_124)) | ~r1_tarski(k2_relat_1(B_124), A_125) | ~v1_funct_1(B_124) | ~v1_relat_1(B_124))), inference(resolution, [status(thm)], [c_422, c_26])).
% 13.63/5.79  tff(c_471, plain, (![B_126]: (v4_relat_1(B_126, k1_relat_1(B_126)) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126))), inference(resolution, [status(thm)], [c_6, c_464])).
% 13.63/5.79  tff(c_481, plain, (![B_126]: (k7_relat_1(B_126, k1_relat_1(B_126))=B_126 | ~v1_funct_1(B_126) | ~v1_relat_1(B_126))), inference(resolution, [status(thm)], [c_471, c_18])).
% 13.63/5.79  tff(c_46, plain, (![A_31, B_32, C_33, D_34]: (k2_partfun1(A_31, B_32, C_33, D_34)=k7_relat_1(C_33, D_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_1(C_33))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.63/5.79  tff(c_983, plain, (![D_169, D_34]: (k2_partfun1('#skF_1', '#skF_2', k7_relat_1('#skF_4', D_169), D_34)=k7_relat_1(k7_relat_1('#skF_4', D_169), D_34) | ~v1_funct_1(k7_relat_1('#skF_4', D_169)))), inference(resolution, [status(thm)], [c_975, c_46])).
% 13.63/5.79  tff(c_1015, plain, (![D_169, D_34]: (k2_partfun1('#skF_1', '#skF_2', k7_relat_1('#skF_4', D_169), D_34)=k7_relat_1(k7_relat_1('#skF_4', D_169), D_34))), inference(demodulation, [status(thm), theory('equality')], [c_549, c_983])).
% 13.63/5.79  tff(c_968, plain, (![D_140]: (m1_subset_1(k7_relat_1('#skF_4', D_140), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_952])).
% 13.63/5.79  tff(c_10, plain, (![B_6, A_4]: (v1_relat_1(B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_4)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 13.63/5.79  tff(c_949, plain, (![A_165, B_166, C_167, D_168]: (v1_relat_1(k2_partfun1(A_165, B_166, C_167, D_168)) | ~v1_relat_1(k2_zfmisc_1(A_165, B_166)) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))) | ~v1_funct_1(C_167))), inference(resolution, [status(thm)], [c_912, c_10])).
% 13.63/5.79  tff(c_1090, plain, (![A_176, B_177, C_178, D_179]: (v1_relat_1(k2_partfun1(A_176, B_177, C_178, D_179)) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~v1_funct_1(C_178))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_949])).
% 13.63/5.79  tff(c_1092, plain, (![D_140, D_179]: (v1_relat_1(k2_partfun1('#skF_1', '#skF_2', k7_relat_1('#skF_4', D_140), D_179)) | ~v1_funct_1(k7_relat_1('#skF_4', D_140)))), inference(resolution, [status(thm)], [c_968, c_1090])).
% 13.63/5.79  tff(c_1103, plain, (![D_140, D_179]: (v1_relat_1(k2_partfun1('#skF_1', '#skF_2', k7_relat_1('#skF_4', D_140), D_179)))), inference(demodulation, [status(thm), theory('equality')], [c_549, c_1092])).
% 13.63/5.79  tff(c_1811, plain, (![D_140, D_179]: (v1_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_140), D_179)))), inference(demodulation, [status(thm), theory('equality')], [c_1015, c_1103])).
% 13.63/5.79  tff(c_1526, plain, (![A_195, B_196, C_197, D_198]: (v4_relat_1(k2_partfun1(A_195, B_196, C_197, D_198), A_195) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))) | ~v1_funct_1(C_197))), inference(resolution, [status(thm)], [c_912, c_26])).
% 13.63/5.79  tff(c_1528, plain, (![D_140, D_198]: (v4_relat_1(k2_partfun1('#skF_1', '#skF_2', k7_relat_1('#skF_4', D_140), D_198), '#skF_1') | ~v1_funct_1(k7_relat_1('#skF_4', D_140)))), inference(resolution, [status(thm)], [c_968, c_1526])).
% 13.63/5.79  tff(c_1539, plain, (![D_140, D_198]: (v4_relat_1(k2_partfun1('#skF_1', '#skF_2', k7_relat_1('#skF_4', D_140), D_198), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_549, c_1528])).
% 13.63/5.79  tff(c_1887, plain, (![D_212, D_213]: (v4_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_212), D_213), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1015, c_1539])).
% 13.63/5.79  tff(c_1890, plain, (![D_212, D_213]: (k7_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_212), D_213), '#skF_1')=k7_relat_1(k7_relat_1('#skF_4', D_212), D_213) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_212), D_213)))), inference(resolution, [status(thm)], [c_1887, c_18])).
% 13.63/5.79  tff(c_2317, plain, (![D_249, D_250]: (k7_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_249), D_250), '#skF_1')=k7_relat_1(k7_relat_1('#skF_4', D_249), D_250))), inference(demodulation, [status(thm), theory('equality')], [c_1811, c_1890])).
% 13.63/5.79  tff(c_2340, plain, (![D_249]: (k7_relat_1(k7_relat_1('#skF_4', D_249), k1_relat_1(k7_relat_1('#skF_4', D_249)))=k7_relat_1(k7_relat_1('#skF_4', D_249), '#skF_1') | ~v1_funct_1(k7_relat_1('#skF_4', D_249)) | ~v1_relat_1(k7_relat_1('#skF_4', D_249)))), inference(superposition, [status(thm), theory('equality')], [c_481, c_2317])).
% 13.63/5.79  tff(c_2352, plain, (![D_249]: (k7_relat_1(k7_relat_1('#skF_4', D_249), k1_relat_1(k7_relat_1('#skF_4', D_249)))=k7_relat_1('#skF_4', D_249))), inference(demodulation, [status(thm), theory('equality')], [c_1022, c_549, c_1076, c_2340])).
% 13.63/5.79  tff(c_380, plain, (![A_108, B_109, C_110]: (k1_relset_1(A_108, B_109, C_110)=k1_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.63/5.79  tff(c_384, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_380])).
% 13.63/5.79  tff(c_596, plain, (![B_146, A_147, C_148]: (k1_xboole_0=B_146 | k1_relset_1(A_147, B_146, C_148)=A_147 | ~v1_funct_2(C_148, A_147, B_146) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_147, B_146))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.63/5.79  tff(c_602, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_596])).
% 13.63/5.79  tff(c_606, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_384, c_602])).
% 13.63/5.79  tff(c_607, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_68, c_606])).
% 13.63/5.79  tff(c_633, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_607, c_20])).
% 13.63/5.79  tff(c_651, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_633])).
% 13.63/5.79  tff(c_330, plain, (![B_103, A_104]: (k1_relat_1(k7_relat_1(B_103, A_104))=A_104 | ~r1_tarski(A_104, k1_relat_1(B_103)) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.63/5.79  tff(c_344, plain, (![B_103]: (k1_relat_1(k7_relat_1(B_103, k1_relat_1(B_103)))=k1_relat_1(B_103) | ~v1_relat_1(B_103))), inference(resolution, [status(thm)], [c_6, c_330])).
% 13.63/5.79  tff(c_18591, plain, (![B_659, A_660]: (m1_subset_1(k7_relat_1(B_659, k1_relat_1(B_659)), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_659), A_660))) | ~r1_tarski(k2_relat_1(k7_relat_1(B_659, k1_relat_1(B_659))), A_660) | ~v1_funct_1(k7_relat_1(B_659, k1_relat_1(B_659))) | ~v1_relat_1(k7_relat_1(B_659, k1_relat_1(B_659))) | ~v1_relat_1(B_659))), inference(superposition, [status(thm), theory('equality')], [c_344, c_422])).
% 13.63/5.79  tff(c_18785, plain, (![A_13, A_660]: (m1_subset_1(k7_relat_1(k7_relat_1('#skF_4', A_13), k1_relat_1(k7_relat_1('#skF_4', A_13))), k1_zfmisc_1(k2_zfmisc_1(A_13, A_660))) | ~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1('#skF_4', A_13), k1_relat_1(k7_relat_1('#skF_4', A_13)))), A_660) | ~v1_funct_1(k7_relat_1(k7_relat_1('#skF_4', A_13), k1_relat_1(k7_relat_1('#skF_4', A_13)))) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_4', A_13), k1_relat_1(k7_relat_1('#skF_4', A_13)))) | ~v1_relat_1(k7_relat_1('#skF_4', A_13)) | ~r1_tarski(A_13, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_651, c_18591])).
% 13.63/5.79  tff(c_27756, plain, (![A_831, A_832]: (m1_subset_1(k7_relat_1('#skF_4', A_831), k1_zfmisc_1(k2_zfmisc_1(A_831, A_832))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_831)), A_832) | ~r1_tarski(A_831, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1022, c_1022, c_2352, c_549, c_2352, c_2352, c_2352, c_18785])).
% 13.63/5.79  tff(c_236, plain, (![A_77, B_78, C_79, D_80]: (v1_funct_1(k2_partfun1(A_77, B_78, C_79, D_80)) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_funct_1(C_79))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.63/5.79  tff(c_238, plain, (![D_80]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_80)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_236])).
% 13.63/5.79  tff(c_241, plain, (![D_80]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_80)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_238])).
% 13.63/5.79  tff(c_54, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 13.63/5.79  tff(c_70, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_54])).
% 13.63/5.79  tff(c_244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_241, c_70])).
% 13.63/5.79  tff(c_245, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_54])).
% 13.63/5.79  tff(c_297, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_245])).
% 13.63/5.79  tff(c_550, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_548, c_297])).
% 13.63/5.79  tff(c_27784, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_27756, c_550])).
% 13.63/5.79  tff(c_27854, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_27784])).
% 13.63/5.79  tff(c_27885, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_14, c_27854])).
% 13.63/5.79  tff(c_27891, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1022, c_1021, c_27885])).
% 13.63/5.79  tff(c_27893, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_245])).
% 13.63/5.79  tff(c_28012, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_27893, c_28005])).
% 13.63/5.79  tff(c_28156, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28155, c_28155, c_28012])).
% 13.63/5.79  tff(c_27892, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_245])).
% 13.63/5.79  tff(c_28164, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28155, c_27892])).
% 13.63/5.79  tff(c_28163, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28155, c_27893])).
% 13.63/5.79  tff(c_36, plain, (![B_25, C_26, A_24]: (k1_xboole_0=B_25 | v1_funct_2(C_26, A_24, B_25) | k1_relset_1(A_24, B_25, C_26)!=A_24 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.63/5.79  tff(c_28203, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_28163, c_36])).
% 13.63/5.79  tff(c_28225, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_28164, c_68, c_28203])).
% 13.63/5.79  tff(c_28242, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28156, c_28225])).
% 13.63/5.79  tff(c_28330, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28324, c_28242])).
% 13.63/5.79  tff(c_28379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_28330])).
% 13.63/5.79  tff(c_28380, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_56])).
% 13.63/5.79  tff(c_28381, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_56])).
% 13.63/5.79  tff(c_28387, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28380, c_28381])).
% 13.63/5.79  tff(c_28395, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28387, c_60])).
% 13.63/5.79  tff(c_28396, plain, (![C_892, A_893, B_894]: (v1_relat_1(C_892) | ~m1_subset_1(C_892, k1_zfmisc_1(k2_zfmisc_1(A_893, B_894))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.63/5.79  tff(c_28400, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28395, c_28396])).
% 13.63/5.79  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.63/5.79  tff(c_28382, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_28380, c_8])).
% 13.63/5.79  tff(c_28797, plain, (![C_943, B_944, A_945]: (v5_relat_1(C_943, B_944) | ~m1_subset_1(C_943, k1_zfmisc_1(k2_zfmisc_1(A_945, B_944))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.63/5.79  tff(c_28801, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_28395, c_28797])).
% 13.63/5.79  tff(c_28807, plain, (![B_949, A_950]: (r1_tarski(k2_relat_1(B_949), A_950) | ~v5_relat_1(B_949, A_950) | ~v1_relat_1(B_949))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.63/5.79  tff(c_28753, plain, (![B_937, A_938]: (B_937=A_938 | ~r1_tarski(B_937, A_938) | ~r1_tarski(A_938, B_937))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.63/5.79  tff(c_28760, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(resolution, [status(thm)], [c_28382, c_28753])).
% 13.63/5.79  tff(c_28831, plain, (![B_953]: (k2_relat_1(B_953)='#skF_1' | ~v5_relat_1(B_953, '#skF_1') | ~v1_relat_1(B_953))), inference(resolution, [status(thm)], [c_28807, c_28760])).
% 13.63/5.79  tff(c_28834, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28801, c_28831])).
% 13.63/5.79  tff(c_28837, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28400, c_28834])).
% 13.63/5.79  tff(c_28802, plain, (![C_946, A_947, B_948]: (v4_relat_1(C_946, A_947) | ~m1_subset_1(C_946, k1_zfmisc_1(k2_zfmisc_1(A_947, B_948))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.63/5.79  tff(c_28806, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_28395, c_28802])).
% 13.63/5.79  tff(c_28820, plain, (![B_951, A_952]: (k7_relat_1(B_951, A_952)=B_951 | ~v4_relat_1(B_951, A_952) | ~v1_relat_1(B_951))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.63/5.79  tff(c_28823, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28806, c_28820])).
% 13.63/5.79  tff(c_28826, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28400, c_28823])).
% 13.63/5.79  tff(c_28866, plain, (![B_955, A_956]: (k1_relat_1(k7_relat_1(B_955, A_956))=A_956 | ~r1_tarski(A_956, k1_relat_1(B_955)) | ~v1_relat_1(B_955))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.63/5.79  tff(c_28882, plain, (![B_957]: (k1_relat_1(k7_relat_1(B_957, '#skF_1'))='#skF_1' | ~v1_relat_1(B_957))), inference(resolution, [status(thm)], [c_28382, c_28866])).
% 13.63/5.79  tff(c_28894, plain, (k1_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28826, c_28882])).
% 13.63/5.79  tff(c_28898, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28400, c_28894])).
% 13.63/5.79  tff(c_29091, plain, (![B_979, A_980]: (m1_subset_1(B_979, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_979), A_980))) | ~r1_tarski(k2_relat_1(B_979), A_980) | ~v1_funct_1(B_979) | ~v1_relat_1(B_979))), inference(cnfTransformation, [status(thm)], [f_118])).
% 13.63/5.79  tff(c_29128, plain, (![A_980]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_980))) | ~r1_tarski(k2_relat_1('#skF_4'), A_980) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_28898, c_29091])).
% 13.63/5.79  tff(c_29143, plain, (![A_980]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_980))))), inference(demodulation, [status(thm), theory('equality')], [c_28400, c_64, c_28382, c_28837, c_29128])).
% 13.63/5.79  tff(c_29567, plain, (![A_1005, B_1006, C_1007, D_1008]: (k2_partfun1(A_1005, B_1006, C_1007, D_1008)=k7_relat_1(C_1007, D_1008) | ~m1_subset_1(C_1007, k1_zfmisc_1(k2_zfmisc_1(A_1005, B_1006))) | ~v1_funct_1(C_1007))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.63/5.79  tff(c_29569, plain, (![A_980, D_1008]: (k2_partfun1('#skF_1', A_980, '#skF_4', D_1008)=k7_relat_1('#skF_4', D_1008) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_29143, c_29567])).
% 13.63/5.79  tff(c_29574, plain, (![A_980, D_1008]: (k2_partfun1('#skF_1', A_980, '#skF_4', D_1008)=k7_relat_1('#skF_4', D_1008))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_29569])).
% 13.63/5.79  tff(c_28759, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_28753])).
% 13.63/5.79  tff(c_28767, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28382, c_28759])).
% 13.63/5.79  tff(c_28742, plain, (![A_933, B_934, C_935, D_936]: (v1_funct_1(k2_partfun1(A_933, B_934, C_935, D_936)) | ~m1_subset_1(C_935, k1_zfmisc_1(k2_zfmisc_1(A_933, B_934))) | ~v1_funct_1(C_935))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.63/5.79  tff(c_28744, plain, (![D_936]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', D_936)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_28395, c_28742])).
% 13.63/5.79  tff(c_28747, plain, (![D_936]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', D_936)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_28744])).
% 13.63/5.79  tff(c_28410, plain, (![B_897, A_898]: (B_897=A_898 | ~r1_tarski(B_897, A_898) | ~r1_tarski(A_898, B_897))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.63/5.79  tff(c_28416, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_28410])).
% 13.63/5.79  tff(c_28424, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28382, c_28416])).
% 13.63/5.79  tff(c_28408, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28387, c_28387, c_28387, c_28387, c_28387, c_54])).
% 13.63/5.79  tff(c_28409, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_28408])).
% 13.63/5.79  tff(c_28425, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28424, c_28409])).
% 13.63/5.79  tff(c_28750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28747, c_28425])).
% 13.63/5.79  tff(c_28751, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(splitRight, [status(thm)], [c_28408])).
% 13.63/5.79  tff(c_28795, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28767, c_28767, c_28767, c_28767, c_28751])).
% 13.63/5.79  tff(c_28796, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_28795])).
% 13.63/5.79  tff(c_29577, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_29574, c_28796])).
% 13.63/5.79  tff(c_29580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_29143, c_28826, c_29577])).
% 13.63/5.79  tff(c_29582, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitRight, [status(thm)], [c_28795])).
% 13.63/5.79  tff(c_29669, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_29582, c_22])).
% 13.63/5.79  tff(c_28752, plain, (v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_28408])).
% 13.63/5.79  tff(c_28768, plain, (v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28767, c_28752])).
% 13.63/5.79  tff(c_29665, plain, (v5_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_29582, c_24])).
% 13.63/5.79  tff(c_29589, plain, (![B_1014, A_1015]: (r1_tarski(k2_relat_1(B_1014), A_1015) | ~v5_relat_1(B_1014, A_1015) | ~v1_relat_1(B_1014))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.63/5.79  tff(c_29599, plain, (![B_1014]: (k2_relat_1(B_1014)='#skF_1' | ~v5_relat_1(B_1014, '#skF_1') | ~v1_relat_1(B_1014))), inference(resolution, [status(thm)], [c_29589, c_28760])).
% 13.63/5.79  tff(c_29673, plain, (k2_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1' | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_29665, c_29599])).
% 13.63/5.79  tff(c_29676, plain, (k2_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_29669, c_29673])).
% 13.63/5.79  tff(c_29664, plain, (v4_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_29582, c_26])).
% 13.63/5.79  tff(c_29679, plain, (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1')=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_29664, c_18])).
% 13.63/5.79  tff(c_29682, plain, (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1')=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29669, c_29679])).
% 13.63/5.79  tff(c_29711, plain, (![B_1022, A_1023]: (k1_relat_1(k7_relat_1(B_1022, A_1023))=A_1023 | ~r1_tarski(A_1023, k1_relat_1(B_1022)) | ~v1_relat_1(B_1022))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.63/5.79  tff(c_29725, plain, (![B_1022]: (k1_relat_1(k7_relat_1(B_1022, '#skF_1'))='#skF_1' | ~v1_relat_1(B_1022))), inference(resolution, [status(thm)], [c_28382, c_29711])).
% 13.63/5.79  tff(c_29787, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1' | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_29682, c_29725])).
% 13.63/5.79  tff(c_29791, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_29669, c_29787])).
% 13.63/5.79  tff(c_29942, plain, (![B_1034, A_1035]: (v1_funct_2(B_1034, k1_relat_1(B_1034), A_1035) | ~r1_tarski(k2_relat_1(B_1034), A_1035) | ~v1_funct_1(B_1034) | ~v1_relat_1(B_1034))), inference(cnfTransformation, [status(thm)], [f_118])).
% 13.63/5.79  tff(c_29951, plain, (![A_1035]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', A_1035) | ~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')), A_1035) | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')) | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_29791, c_29942])).
% 13.63/5.79  tff(c_29962, plain, (![A_1035]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', A_1035))), inference(demodulation, [status(thm), theory('equality')], [c_29669, c_28768, c_28382, c_29676, c_29951])).
% 13.63/5.79  tff(c_29581, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_28795])).
% 13.63/5.79  tff(c_29969, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_29962, c_29581])).
% 13.63/5.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.63/5.79  
% 13.63/5.79  Inference rules
% 13.63/5.79  ----------------------
% 13.63/5.79  #Ref     : 0
% 13.63/5.79  #Sup     : 6268
% 13.63/5.79  #Fact    : 0
% 13.63/5.79  #Define  : 0
% 13.63/5.79  #Split   : 12
% 13.63/5.79  #Chain   : 0
% 13.63/5.79  #Close   : 0
% 13.63/5.79  
% 13.63/5.79  Ordering : KBO
% 13.63/5.79  
% 13.63/5.79  Simplification rules
% 13.63/5.79  ----------------------
% 13.63/5.79  #Subsume      : 1430
% 13.63/5.79  #Demod        : 12920
% 13.63/5.79  #Tautology    : 2694
% 13.63/5.79  #SimpNegUnit  : 146
% 13.63/5.79  #BackRed      : 88
% 13.63/5.79  
% 13.63/5.79  #Partial instantiations: 0
% 13.63/5.79  #Strategies tried      : 1
% 13.63/5.79  
% 13.63/5.79  Timing (in seconds)
% 13.63/5.79  ----------------------
% 13.63/5.79  Preprocessing        : 0.37
% 13.63/5.79  Parsing              : 0.20
% 13.63/5.79  CNF conversion       : 0.02
% 13.63/5.79  Main loop            : 4.57
% 13.63/5.79  Inferencing          : 1.06
% 13.63/5.79  Reduction            : 2.28
% 13.63/5.79  Demodulation         : 1.92
% 13.63/5.79  BG Simplification    : 0.10
% 13.63/5.79  Subsumption          : 0.91
% 13.63/5.79  Abstraction          : 0.18
% 13.63/5.79  MUC search           : 0.00
% 13.63/5.79  Cooper               : 0.00
% 13.63/5.79  Total                : 5.00
% 13.63/5.80  Index Insertion      : 0.00
% 13.63/5.80  Index Deletion       : 0.00
% 13.63/5.80  Index Matching       : 0.00
% 13.63/5.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
