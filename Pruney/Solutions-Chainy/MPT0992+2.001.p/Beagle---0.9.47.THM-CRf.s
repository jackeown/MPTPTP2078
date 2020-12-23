%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:31 EST 2020

% Result     : Theorem 12.34s
% Output     : CNFRefutation 12.71s
% Verified   : 
% Statistics : Number of formulae       :  210 (1456 expanded)
%              Number of leaves         :   46 ( 455 expanded)
%              Depth                    :   12
%              Number of atoms          :  335 (4335 expanded)
%              Number of equality atoms :   83 (1424 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_165,negated_conjecture,(
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

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_119,axiom,(
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

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_133,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_127,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_145,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_62,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_61,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_32,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(c_74,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_8709,plain,(
    ! [C_545,A_546,B_547] :
      ( v1_relat_1(C_545)
      | ~ m1_subset_1(C_545,k1_zfmisc_1(k2_zfmisc_1(A_546,B_547))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8717,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_8709])).

tff(c_72,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_108,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_8931,plain,(
    ! [A_579,B_580,C_581] :
      ( k1_relset_1(A_579,B_580,C_581) = k1_relat_1(C_581)
      | ~ m1_subset_1(C_581,k1_zfmisc_1(k2_zfmisc_1(A_579,B_580))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_8943,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_8931])).

tff(c_9329,plain,(
    ! [B_634,A_635,C_636] :
      ( k1_xboole_0 = B_634
      | k1_relset_1(A_635,B_634,C_636) = A_635
      | ~ v1_funct_2(C_636,A_635,B_634)
      | ~ m1_subset_1(C_636,k1_zfmisc_1(k2_zfmisc_1(A_635,B_634))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_9338,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_9329])).

tff(c_9349,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_8943,c_9338])).

tff(c_9350,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_9349])).

tff(c_26,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,A_13)) = A_13
      | ~ r1_tarski(A_13,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_9367,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9350,c_26])).

tff(c_9400,plain,(
    ! [A_637] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_637)) = A_637
      | ~ r1_tarski(A_637,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8717,c_9367])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_9188,plain,(
    ! [A_617,B_618,C_619,D_620] :
      ( k2_partfun1(A_617,B_618,C_619,D_620) = k7_relat_1(C_619,D_620)
      | ~ m1_subset_1(C_619,k1_zfmisc_1(k2_zfmisc_1(A_617,B_618)))
      | ~ v1_funct_1(C_619) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_9194,plain,(
    ! [D_620] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_620) = k7_relat_1('#skF_4',D_620)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_9188])).

tff(c_9204,plain,(
    ! [D_620] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_620) = k7_relat_1('#skF_4',D_620) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_9194])).

tff(c_790,plain,(
    ! [A_170,B_171,C_172,D_173] :
      ( k2_partfun1(A_170,B_171,C_172,D_173) = k7_relat_1(C_172,D_173)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171)))
      | ~ v1_funct_1(C_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_794,plain,(
    ! [D_173] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_173) = k7_relat_1('#skF_4',D_173)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_790])).

tff(c_801,plain,(
    ! [D_173] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_173) = k7_relat_1('#skF_4',D_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_794])).

tff(c_1100,plain,(
    ! [A_204,B_205,C_206,D_207] :
      ( m1_subset_1(k2_partfun1(A_204,B_205,C_206,D_207),k1_zfmisc_1(k2_zfmisc_1(A_204,B_205)))
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205)))
      | ~ v1_funct_1(C_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1145,plain,(
    ! [D_173] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_173),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_801,c_1100])).

tff(c_1240,plain,(
    ! [D_213] : m1_subset_1(k7_relat_1('#skF_4',D_213),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_1145])).

tff(c_36,plain,(
    ! [C_20,A_18,B_19] :
      ( v1_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1291,plain,(
    ! [D_213] : v1_relat_1(k7_relat_1('#skF_4',D_213)) ),
    inference(resolution,[status(thm)],[c_1240,c_36])).

tff(c_38,plain,(
    ! [C_23,B_22,A_21] :
      ( v5_relat_1(C_23,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1290,plain,(
    ! [D_213] : v5_relat_1(k7_relat_1('#skF_4',D_213),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1240,c_38])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_651,plain,(
    ! [A_148,B_149,C_150,D_151] :
      ( v1_funct_1(k2_partfun1(A_148,B_149,C_150,D_151))
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149)))
      | ~ v1_funct_1(C_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_653,plain,(
    ! [D_151] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_151))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_651])).

tff(c_659,plain,(
    ! [D_151] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_151)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_653])).

tff(c_805,plain,(
    ! [D_151] : v1_funct_1(k7_relat_1('#skF_4',D_151)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_801,c_659])).

tff(c_424,plain,(
    ! [C_105,A_106,B_107] :
      ( v1_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_432,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_424])).

tff(c_616,plain,(
    ! [A_140,B_141,C_142] :
      ( k1_relset_1(A_140,B_141,C_142) = k1_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_624,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_616])).

tff(c_995,plain,(
    ! [B_198,A_199,C_200] :
      ( k1_xboole_0 = B_198
      | k1_relset_1(A_199,B_198,C_200) = A_199
      | ~ v1_funct_2(C_200,A_199,B_198)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_199,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1001,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_995])).

tff(c_1009,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_624,c_1001])).

tff(c_1010,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_1009])).

tff(c_1033,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1010,c_26])).

tff(c_1577,plain,(
    ! [A_233] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_233)) = A_233
      | ~ r1_tarski(A_233,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_1033])).

tff(c_64,plain,(
    ! [B_43,A_42] :
      ( m1_subset_1(B_43,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_43),A_42)))
      | ~ r1_tarski(k2_relat_1(B_43),A_42)
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1595,plain,(
    ! [A_233,A_42] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_233),k1_zfmisc_1(k2_zfmisc_1(A_233,A_42)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_233)),A_42)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_233))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_233))
      | ~ r1_tarski(A_233,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1577,c_64])).

tff(c_8535,plain,(
    ! [A_539,A_540] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_539),k1_zfmisc_1(k2_zfmisc_1(A_539,A_540)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_539)),A_540)
      | ~ r1_tarski(A_539,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1291,c_805,c_1595])).

tff(c_372,plain,(
    ! [A_97,B_98,C_99,D_100] :
      ( v1_funct_1(k2_partfun1(A_97,B_98,C_99,D_100))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ v1_funct_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_374,plain,(
    ! [D_100] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_100))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_372])).

tff(c_380,plain,(
    ! [D_100] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_100)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_374])).

tff(c_70,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_117,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_117])).

tff(c_394,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_397,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_806,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_801,c_397])).

tff(c_8563,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_8535,c_806])).

tff(c_8641,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_8563])).

tff(c_8670,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_8641])).

tff(c_8674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1291,c_1290,c_8670])).

tff(c_8676,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_8942,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8676,c_8931])).

tff(c_9210,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9204,c_9204,c_8942])).

tff(c_8675,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_9217,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9204,c_8675])).

tff(c_9216,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9204,c_8676])).

tff(c_9295,plain,(
    ! [B_627,C_628,A_629] :
      ( k1_xboole_0 = B_627
      | v1_funct_2(C_628,A_629,B_627)
      | k1_relset_1(A_629,B_627,C_628) != A_629
      | ~ m1_subset_1(C_628,k1_zfmisc_1(k2_zfmisc_1(A_629,B_627))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_9298,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_9216,c_9295])).

tff(c_9311,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_9217,c_108,c_9298])).

tff(c_9324,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9210,c_9311])).

tff(c_9406,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9400,c_9324])).

tff(c_9454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_9406])).

tff(c_9455,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_9456,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_9468,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9455,c_9456])).

tff(c_9494,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9468,c_76])).

tff(c_9537,plain,(
    ! [C_645,A_646,B_647] :
      ( v1_relat_1(C_645)
      | ~ m1_subset_1(C_645,k1_zfmisc_1(k2_zfmisc_1(A_646,B_647))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_9547,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_9494,c_9537])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_9463,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9455,c_2])).

tff(c_10881,plain,(
    ! [C_813,A_814,B_815] :
      ( v1_xboole_0(C_813)
      | ~ m1_subset_1(C_813,k1_zfmisc_1(k2_zfmisc_1(A_814,B_815)))
      | ~ v1_xboole_0(A_814) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10891,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_9494,c_10881])).

tff(c_10899,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9463,c_10891])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_9499,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9455,c_4])).

tff(c_10906,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10899,c_9499])).

tff(c_24,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_96,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_32])).

tff(c_9458,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9455,c_96])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_9506,plain,(
    ! [A_5] : m1_subset_1('#skF_1',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9455,c_10])).

tff(c_10704,plain,(
    ! [C_789,B_790,A_791] :
      ( v5_relat_1(C_789,B_790)
      | ~ m1_subset_1(C_789,k1_zfmisc_1(k2_zfmisc_1(A_791,B_790))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10716,plain,(
    ! [B_790] : v5_relat_1('#skF_1',B_790) ),
    inference(resolution,[status(thm)],[c_9506,c_10704])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_9461,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9455,c_9455,c_20])).

tff(c_10725,plain,(
    ! [B_795,A_796] :
      ( r1_tarski(k2_relat_1(B_795),A_796)
      | ~ v5_relat_1(B_795,A_796)
      | ~ v1_relat_1(B_795) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10735,plain,(
    ! [A_796] :
      ( r1_tarski('#skF_1',A_796)
      | ~ v5_relat_1('#skF_1',A_796)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9461,c_10725])).

tff(c_10739,plain,(
    ! [A_796] : r1_tarski('#skF_1',A_796) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9458,c_10716,c_10735])).

tff(c_10920,plain,(
    ! [A_796] : r1_tarski('#skF_4',A_796) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10906,c_10739])).

tff(c_10933,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10906,c_10906,c_9461])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_9460,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9455,c_9455,c_22])).

tff(c_10938,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10906,c_10906,c_9460])).

tff(c_11103,plain,(
    ! [B_826,A_827] :
      ( v1_funct_2(B_826,k1_relat_1(B_826),A_827)
      | ~ r1_tarski(k2_relat_1(B_826),A_827)
      | ~ v1_funct_1(B_826)
      | ~ v1_relat_1(B_826) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_11106,plain,(
    ! [A_827] :
      ( v1_funct_2('#skF_4','#skF_4',A_827)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_827)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10938,c_11103])).

tff(c_11108,plain,(
    ! [A_827] : v1_funct_2('#skF_4','#skF_4',A_827) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9547,c_80,c_10920,c_10933,c_11106])).

tff(c_6,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9462,plain,(
    ! [A_2] : r1_xboole_0(A_2,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9455,c_6])).

tff(c_10666,plain,(
    ! [B_786,A_787] :
      ( ~ r1_xboole_0(B_786,A_787)
      | ~ r1_tarski(B_786,A_787)
      | v1_xboole_0(B_786) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10671,plain,(
    ! [A_788] :
      ( ~ r1_tarski(A_788,'#skF_1')
      | v1_xboole_0(A_788) ) ),
    inference(resolution,[status(thm)],[c_9462,c_10666])).

tff(c_10675,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_10671])).

tff(c_10682,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10675,c_9499])).

tff(c_10192,plain,(
    ! [C_730,A_731,B_732] :
      ( v1_xboole_0(C_730)
      | ~ m1_subset_1(C_730,k1_zfmisc_1(k2_zfmisc_1(A_731,B_732)))
      | ~ v1_xboole_0(A_731) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10199,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_9494,c_10192])).

tff(c_10204,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9463,c_10199])).

tff(c_10211,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10204,c_9499])).

tff(c_10230,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10211,c_9506])).

tff(c_9511,plain,(
    ! [A_644] :
      ( k7_relat_1(A_644,k1_relat_1(A_644)) = A_644
      | ~ v1_relat_1(A_644) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_9523,plain,
    ( k7_relat_1('#skF_1','#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9460,c_9511])).

tff(c_9527,plain,(
    k7_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9458,c_9523])).

tff(c_10228,plain,(
    k7_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10211,c_10211,c_10211,c_9527])).

tff(c_10649,plain,(
    ! [A_782,B_783,C_784,D_785] :
      ( k2_partfun1(A_782,B_783,C_784,D_785) = k7_relat_1(C_784,D_785)
      | ~ m1_subset_1(C_784,k1_zfmisc_1(k2_zfmisc_1(A_782,B_783)))
      | ~ v1_funct_1(C_784) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_10654,plain,(
    ! [A_782,B_783,D_785] :
      ( k2_partfun1(A_782,B_783,'#skF_4',D_785) = k7_relat_1('#skF_4',D_785)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10230,c_10649])).

tff(c_10658,plain,(
    ! [A_782,B_783,D_785] : k2_partfun1(A_782,B_783,'#skF_4',D_785) = k7_relat_1('#skF_4',D_785) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_10654])).

tff(c_10032,plain,(
    ! [B_704,A_705] :
      ( ~ r1_xboole_0(B_704,A_705)
      | ~ r1_tarski(B_704,A_705)
      | v1_xboole_0(B_704) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10037,plain,(
    ! [A_706] :
      ( ~ r1_tarski(A_706,'#skF_1')
      | v1_xboole_0(A_706) ) ),
    inference(resolution,[status(thm)],[c_9462,c_10032])).

tff(c_10041,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_10037])).

tff(c_10048,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10041,c_9499])).

tff(c_9716,plain,(
    ! [C_670,A_671,B_672] :
      ( v1_xboole_0(C_670)
      | ~ m1_subset_1(C_670,k1_zfmisc_1(k2_zfmisc_1(A_671,B_672)))
      | ~ v1_xboole_0(A_671) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_9723,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_9494,c_9716])).

tff(c_9728,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9463,c_9723])).

tff(c_9735,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9728,c_9499])).

tff(c_9751,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9735,c_9506])).

tff(c_10019,plain,(
    ! [A_700,B_701,C_702,D_703] :
      ( v1_funct_1(k2_partfun1(A_700,B_701,C_702,D_703))
      | ~ m1_subset_1(C_702,k1_zfmisc_1(k2_zfmisc_1(A_700,B_701)))
      | ~ v1_funct_1(C_702) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_10022,plain,(
    ! [A_700,B_701,D_703] :
      ( v1_funct_1(k2_partfun1(A_700,B_701,'#skF_4',D_703))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_9751,c_10019])).

tff(c_10025,plain,(
    ! [A_700,B_701,D_703] : v1_funct_1(k2_partfun1(A_700,B_701,'#skF_4',D_703)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_10022])).

tff(c_9550,plain,(
    ! [B_648,A_649] :
      ( ~ r1_xboole_0(B_648,A_649)
      | ~ r1_tarski(B_648,A_649)
      | v1_xboole_0(B_648) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_9555,plain,(
    ! [A_650] :
      ( ~ r1_tarski(A_650,'#skF_1')
      | v1_xboole_0(A_650) ) ),
    inference(resolution,[status(thm)],[c_9462,c_9550])).

tff(c_9559,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_9555])).

tff(c_9566,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_9559,c_9499])).

tff(c_9548,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9468,c_9468,c_9468,c_9468,c_9468,c_70])).

tff(c_9549,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_9548])).

tff(c_9580,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9566,c_9549])).

tff(c_9746,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9735,c_9735,c_9735,c_9580])).

tff(c_10028,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10025,c_9746])).

tff(c_10029,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_9548])).

tff(c_10031,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_10029])).

tff(c_10158,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10048,c_10048,c_10031])).

tff(c_10216,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10211,c_10211,c_10211,c_10211,c_10211,c_10158])).

tff(c_10660,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10658,c_10216])).

tff(c_10663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10230,c_10228,c_10660])).

tff(c_10665,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_10029])).

tff(c_10699,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10682,c_10682,c_10665])).

tff(c_10884,plain,
    ( v1_xboole_0(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10699,c_10881])).

tff(c_10894,plain,(
    v1_xboole_0(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9463,c_10884])).

tff(c_11143,plain,(
    v1_xboole_0(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10906,c_10906,c_10906,c_10894])).

tff(c_10931,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10906,c_9499])).

tff(c_11150,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_11143,c_10931])).

tff(c_10664,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_10029])).

tff(c_10692,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10682,c_10682,c_10664])).

tff(c_10925,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10906,c_10906,c_10906,c_10906,c_10906,c_10692])).

tff(c_11213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11108,c_11150,c_10925])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.34/4.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.34/4.38  
% 12.34/4.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.34/4.39  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.34/4.39  
% 12.34/4.39  %Foreground sorts:
% 12.34/4.39  
% 12.34/4.39  
% 12.34/4.39  %Background operators:
% 12.34/4.39  
% 12.34/4.39  
% 12.34/4.39  %Foreground operators:
% 12.34/4.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.34/4.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.34/4.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.34/4.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.34/4.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.34/4.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.34/4.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.34/4.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.34/4.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.34/4.39  tff('#skF_2', type, '#skF_2': $i).
% 12.34/4.39  tff('#skF_3', type, '#skF_3': $i).
% 12.34/4.39  tff('#skF_1', type, '#skF_1': $i).
% 12.34/4.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.34/4.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.34/4.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.34/4.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.34/4.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.34/4.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.34/4.39  tff('#skF_4', type, '#skF_4': $i).
% 12.34/4.39  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 12.34/4.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.34/4.39  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 12.34/4.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.34/4.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.34/4.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.34/4.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.34/4.39  
% 12.71/4.43  tff(f_165, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 12.71/4.43  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.71/4.43  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.71/4.43  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 12.71/4.43  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 12.71/4.43  tff(f_133, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 12.71/4.43  tff(f_127, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 12.71/4.43  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.71/4.43  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 12.71/4.43  tff(f_145, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 12.71/4.43  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 12.71/4.43  tff(f_97, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 12.71/4.43  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 12.71/4.43  tff(f_62, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 12.71/4.43  tff(f_80, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 12.71/4.43  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 12.71/4.43  tff(f_61, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 12.71/4.43  tff(f_32, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 12.71/4.43  tff(f_40, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 12.71/4.43  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 12.71/4.43  tff(c_74, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.71/4.43  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.71/4.43  tff(c_8709, plain, (![C_545, A_546, B_547]: (v1_relat_1(C_545) | ~m1_subset_1(C_545, k1_zfmisc_1(k2_zfmisc_1(A_546, B_547))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.71/4.43  tff(c_8717, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_8709])).
% 12.71/4.43  tff(c_72, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.71/4.43  tff(c_108, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_72])).
% 12.71/4.43  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.71/4.43  tff(c_8931, plain, (![A_579, B_580, C_581]: (k1_relset_1(A_579, B_580, C_581)=k1_relat_1(C_581) | ~m1_subset_1(C_581, k1_zfmisc_1(k2_zfmisc_1(A_579, B_580))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.71/4.43  tff(c_8943, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_8931])).
% 12.71/4.43  tff(c_9329, plain, (![B_634, A_635, C_636]: (k1_xboole_0=B_634 | k1_relset_1(A_635, B_634, C_636)=A_635 | ~v1_funct_2(C_636, A_635, B_634) | ~m1_subset_1(C_636, k1_zfmisc_1(k2_zfmisc_1(A_635, B_634))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 12.71/4.43  tff(c_9338, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_9329])).
% 12.71/4.43  tff(c_9349, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_8943, c_9338])).
% 12.71/4.43  tff(c_9350, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_108, c_9349])).
% 12.71/4.43  tff(c_26, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, A_13))=A_13 | ~r1_tarski(A_13, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.71/4.43  tff(c_9367, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9350, c_26])).
% 12.71/4.43  tff(c_9400, plain, (![A_637]: (k1_relat_1(k7_relat_1('#skF_4', A_637))=A_637 | ~r1_tarski(A_637, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8717, c_9367])).
% 12.71/4.43  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.71/4.43  tff(c_9188, plain, (![A_617, B_618, C_619, D_620]: (k2_partfun1(A_617, B_618, C_619, D_620)=k7_relat_1(C_619, D_620) | ~m1_subset_1(C_619, k1_zfmisc_1(k2_zfmisc_1(A_617, B_618))) | ~v1_funct_1(C_619))), inference(cnfTransformation, [status(thm)], [f_133])).
% 12.71/4.43  tff(c_9194, plain, (![D_620]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_620)=k7_relat_1('#skF_4', D_620) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_9188])).
% 12.71/4.43  tff(c_9204, plain, (![D_620]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_620)=k7_relat_1('#skF_4', D_620))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_9194])).
% 12.71/4.43  tff(c_790, plain, (![A_170, B_171, C_172, D_173]: (k2_partfun1(A_170, B_171, C_172, D_173)=k7_relat_1(C_172, D_173) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))) | ~v1_funct_1(C_172))), inference(cnfTransformation, [status(thm)], [f_133])).
% 12.71/4.43  tff(c_794, plain, (![D_173]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_173)=k7_relat_1('#skF_4', D_173) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_790])).
% 12.71/4.43  tff(c_801, plain, (![D_173]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_173)=k7_relat_1('#skF_4', D_173))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_794])).
% 12.71/4.43  tff(c_1100, plain, (![A_204, B_205, C_206, D_207]: (m1_subset_1(k2_partfun1(A_204, B_205, C_206, D_207), k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))) | ~v1_funct_1(C_206))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.71/4.43  tff(c_1145, plain, (![D_173]: (m1_subset_1(k7_relat_1('#skF_4', D_173), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_801, c_1100])).
% 12.71/4.43  tff(c_1240, plain, (![D_213]: (m1_subset_1(k7_relat_1('#skF_4', D_213), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_1145])).
% 12.71/4.43  tff(c_36, plain, (![C_20, A_18, B_19]: (v1_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.71/4.43  tff(c_1291, plain, (![D_213]: (v1_relat_1(k7_relat_1('#skF_4', D_213)))), inference(resolution, [status(thm)], [c_1240, c_36])).
% 12.71/4.43  tff(c_38, plain, (![C_23, B_22, A_21]: (v5_relat_1(C_23, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.71/4.43  tff(c_1290, plain, (![D_213]: (v5_relat_1(k7_relat_1('#skF_4', D_213), '#skF_2'))), inference(resolution, [status(thm)], [c_1240, c_38])).
% 12.71/4.43  tff(c_16, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.71/4.43  tff(c_651, plain, (![A_148, B_149, C_150, D_151]: (v1_funct_1(k2_partfun1(A_148, B_149, C_150, D_151)) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))) | ~v1_funct_1(C_150))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.71/4.43  tff(c_653, plain, (![D_151]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_151)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_651])).
% 12.71/4.43  tff(c_659, plain, (![D_151]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_151)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_653])).
% 12.71/4.43  tff(c_805, plain, (![D_151]: (v1_funct_1(k7_relat_1('#skF_4', D_151)))), inference(demodulation, [status(thm), theory('equality')], [c_801, c_659])).
% 12.71/4.43  tff(c_424, plain, (![C_105, A_106, B_107]: (v1_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.71/4.43  tff(c_432, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_424])).
% 12.71/4.43  tff(c_616, plain, (![A_140, B_141, C_142]: (k1_relset_1(A_140, B_141, C_142)=k1_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.71/4.43  tff(c_624, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_616])).
% 12.71/4.43  tff(c_995, plain, (![B_198, A_199, C_200]: (k1_xboole_0=B_198 | k1_relset_1(A_199, B_198, C_200)=A_199 | ~v1_funct_2(C_200, A_199, B_198) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_199, B_198))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 12.71/4.43  tff(c_1001, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_995])).
% 12.71/4.43  tff(c_1009, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_624, c_1001])).
% 12.71/4.43  tff(c_1010, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_108, c_1009])).
% 12.71/4.43  tff(c_1033, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1010, c_26])).
% 12.71/4.43  tff(c_1577, plain, (![A_233]: (k1_relat_1(k7_relat_1('#skF_4', A_233))=A_233 | ~r1_tarski(A_233, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_432, c_1033])).
% 12.71/4.43  tff(c_64, plain, (![B_43, A_42]: (m1_subset_1(B_43, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_43), A_42))) | ~r1_tarski(k2_relat_1(B_43), A_42) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_145])).
% 12.71/4.43  tff(c_1595, plain, (![A_233, A_42]: (m1_subset_1(k7_relat_1('#skF_4', A_233), k1_zfmisc_1(k2_zfmisc_1(A_233, A_42))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_233)), A_42) | ~v1_funct_1(k7_relat_1('#skF_4', A_233)) | ~v1_relat_1(k7_relat_1('#skF_4', A_233)) | ~r1_tarski(A_233, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1577, c_64])).
% 12.71/4.43  tff(c_8535, plain, (![A_539, A_540]: (m1_subset_1(k7_relat_1('#skF_4', A_539), k1_zfmisc_1(k2_zfmisc_1(A_539, A_540))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_539)), A_540) | ~r1_tarski(A_539, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1291, c_805, c_1595])).
% 12.71/4.43  tff(c_372, plain, (![A_97, B_98, C_99, D_100]: (v1_funct_1(k2_partfun1(A_97, B_98, C_99, D_100)) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~v1_funct_1(C_99))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.71/4.43  tff(c_374, plain, (![D_100]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_100)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_372])).
% 12.71/4.43  tff(c_380, plain, (![D_100]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_100)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_374])).
% 12.71/4.43  tff(c_70, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.71/4.43  tff(c_117, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_70])).
% 12.71/4.43  tff(c_393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_380, c_117])).
% 12.71/4.43  tff(c_394, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_70])).
% 12.71/4.43  tff(c_397, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_394])).
% 12.71/4.43  tff(c_806, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_801, c_397])).
% 12.71/4.43  tff(c_8563, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_8535, c_806])).
% 12.71/4.43  tff(c_8641, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_8563])).
% 12.71/4.43  tff(c_8670, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_8641])).
% 12.71/4.43  tff(c_8674, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1291, c_1290, c_8670])).
% 12.71/4.43  tff(c_8676, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_394])).
% 12.71/4.43  tff(c_8942, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_8676, c_8931])).
% 12.71/4.43  tff(c_9210, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9204, c_9204, c_8942])).
% 12.71/4.43  tff(c_8675, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_394])).
% 12.71/4.43  tff(c_9217, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9204, c_8675])).
% 12.71/4.43  tff(c_9216, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_9204, c_8676])).
% 12.71/4.43  tff(c_9295, plain, (![B_627, C_628, A_629]: (k1_xboole_0=B_627 | v1_funct_2(C_628, A_629, B_627) | k1_relset_1(A_629, B_627, C_628)!=A_629 | ~m1_subset_1(C_628, k1_zfmisc_1(k2_zfmisc_1(A_629, B_627))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 12.71/4.43  tff(c_9298, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_9216, c_9295])).
% 12.71/4.43  tff(c_9311, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_9217, c_108, c_9298])).
% 12.71/4.43  tff(c_9324, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9210, c_9311])).
% 12.71/4.43  tff(c_9406, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9400, c_9324])).
% 12.71/4.43  tff(c_9454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_9406])).
% 12.71/4.43  tff(c_9455, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_72])).
% 12.71/4.43  tff(c_9456, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_72])).
% 12.71/4.43  tff(c_9468, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9455, c_9456])).
% 12.71/4.43  tff(c_9494, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_9468, c_76])).
% 12.71/4.43  tff(c_9537, plain, (![C_645, A_646, B_647]: (v1_relat_1(C_645) | ~m1_subset_1(C_645, k1_zfmisc_1(k2_zfmisc_1(A_646, B_647))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.71/4.43  tff(c_9547, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_9494, c_9537])).
% 12.71/4.43  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 12.71/4.43  tff(c_9463, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9455, c_2])).
% 12.71/4.43  tff(c_10881, plain, (![C_813, A_814, B_815]: (v1_xboole_0(C_813) | ~m1_subset_1(C_813, k1_zfmisc_1(k2_zfmisc_1(A_814, B_815))) | ~v1_xboole_0(A_814))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.71/4.43  tff(c_10891, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_9494, c_10881])).
% 12.71/4.43  tff(c_10899, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9463, c_10891])).
% 12.71/4.43  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 12.71/4.43  tff(c_9499, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_9455, c_4])).
% 12.71/4.43  tff(c_10906, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_10899, c_9499])).
% 12.71/4.43  tff(c_24, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.71/4.43  tff(c_32, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.71/4.43  tff(c_96, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_32])).
% 12.71/4.43  tff(c_9458, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9455, c_96])).
% 12.71/4.43  tff(c_10, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.71/4.43  tff(c_9506, plain, (![A_5]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_9455, c_10])).
% 12.71/4.43  tff(c_10704, plain, (![C_789, B_790, A_791]: (v5_relat_1(C_789, B_790) | ~m1_subset_1(C_789, k1_zfmisc_1(k2_zfmisc_1(A_791, B_790))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.71/4.43  tff(c_10716, plain, (![B_790]: (v5_relat_1('#skF_1', B_790))), inference(resolution, [status(thm)], [c_9506, c_10704])).
% 12.71/4.43  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.71/4.43  tff(c_9461, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9455, c_9455, c_20])).
% 12.71/4.43  tff(c_10725, plain, (![B_795, A_796]: (r1_tarski(k2_relat_1(B_795), A_796) | ~v5_relat_1(B_795, A_796) | ~v1_relat_1(B_795))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.71/4.43  tff(c_10735, plain, (![A_796]: (r1_tarski('#skF_1', A_796) | ~v5_relat_1('#skF_1', A_796) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_9461, c_10725])).
% 12.71/4.43  tff(c_10739, plain, (![A_796]: (r1_tarski('#skF_1', A_796))), inference(demodulation, [status(thm), theory('equality')], [c_9458, c_10716, c_10735])).
% 12.71/4.43  tff(c_10920, plain, (![A_796]: (r1_tarski('#skF_4', A_796))), inference(demodulation, [status(thm), theory('equality')], [c_10906, c_10739])).
% 12.71/4.43  tff(c_10933, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10906, c_10906, c_9461])).
% 12.71/4.43  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.71/4.43  tff(c_9460, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9455, c_9455, c_22])).
% 12.71/4.43  tff(c_10938, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10906, c_10906, c_9460])).
% 12.71/4.43  tff(c_11103, plain, (![B_826, A_827]: (v1_funct_2(B_826, k1_relat_1(B_826), A_827) | ~r1_tarski(k2_relat_1(B_826), A_827) | ~v1_funct_1(B_826) | ~v1_relat_1(B_826))), inference(cnfTransformation, [status(thm)], [f_145])).
% 12.71/4.43  tff(c_11106, plain, (![A_827]: (v1_funct_2('#skF_4', '#skF_4', A_827) | ~r1_tarski(k2_relat_1('#skF_4'), A_827) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10938, c_11103])).
% 12.71/4.43  tff(c_11108, plain, (![A_827]: (v1_funct_2('#skF_4', '#skF_4', A_827))), inference(demodulation, [status(thm), theory('equality')], [c_9547, c_80, c_10920, c_10933, c_11106])).
% 12.71/4.43  tff(c_6, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.71/4.43  tff(c_9462, plain, (![A_2]: (r1_xboole_0(A_2, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9455, c_6])).
% 12.71/4.43  tff(c_10666, plain, (![B_786, A_787]: (~r1_xboole_0(B_786, A_787) | ~r1_tarski(B_786, A_787) | v1_xboole_0(B_786))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.71/4.43  tff(c_10671, plain, (![A_788]: (~r1_tarski(A_788, '#skF_1') | v1_xboole_0(A_788))), inference(resolution, [status(thm)], [c_9462, c_10666])).
% 12.71/4.43  tff(c_10675, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_10671])).
% 12.71/4.43  tff(c_10682, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_10675, c_9499])).
% 12.71/4.43  tff(c_10192, plain, (![C_730, A_731, B_732]: (v1_xboole_0(C_730) | ~m1_subset_1(C_730, k1_zfmisc_1(k2_zfmisc_1(A_731, B_732))) | ~v1_xboole_0(A_731))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.71/4.43  tff(c_10199, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_9494, c_10192])).
% 12.71/4.43  tff(c_10204, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9463, c_10199])).
% 12.71/4.43  tff(c_10211, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_10204, c_9499])).
% 12.71/4.43  tff(c_10230, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_10211, c_9506])).
% 12.71/4.43  tff(c_9511, plain, (![A_644]: (k7_relat_1(A_644, k1_relat_1(A_644))=A_644 | ~v1_relat_1(A_644))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.71/4.43  tff(c_9523, plain, (k7_relat_1('#skF_1', '#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9460, c_9511])).
% 12.71/4.43  tff(c_9527, plain, (k7_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9458, c_9523])).
% 12.71/4.43  tff(c_10228, plain, (k7_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10211, c_10211, c_10211, c_9527])).
% 12.71/4.43  tff(c_10649, plain, (![A_782, B_783, C_784, D_785]: (k2_partfun1(A_782, B_783, C_784, D_785)=k7_relat_1(C_784, D_785) | ~m1_subset_1(C_784, k1_zfmisc_1(k2_zfmisc_1(A_782, B_783))) | ~v1_funct_1(C_784))), inference(cnfTransformation, [status(thm)], [f_133])).
% 12.71/4.43  tff(c_10654, plain, (![A_782, B_783, D_785]: (k2_partfun1(A_782, B_783, '#skF_4', D_785)=k7_relat_1('#skF_4', D_785) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_10230, c_10649])).
% 12.71/4.43  tff(c_10658, plain, (![A_782, B_783, D_785]: (k2_partfun1(A_782, B_783, '#skF_4', D_785)=k7_relat_1('#skF_4', D_785))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_10654])).
% 12.71/4.43  tff(c_10032, plain, (![B_704, A_705]: (~r1_xboole_0(B_704, A_705) | ~r1_tarski(B_704, A_705) | v1_xboole_0(B_704))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.71/4.43  tff(c_10037, plain, (![A_706]: (~r1_tarski(A_706, '#skF_1') | v1_xboole_0(A_706))), inference(resolution, [status(thm)], [c_9462, c_10032])).
% 12.71/4.43  tff(c_10041, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_10037])).
% 12.71/4.43  tff(c_10048, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_10041, c_9499])).
% 12.71/4.43  tff(c_9716, plain, (![C_670, A_671, B_672]: (v1_xboole_0(C_670) | ~m1_subset_1(C_670, k1_zfmisc_1(k2_zfmisc_1(A_671, B_672))) | ~v1_xboole_0(A_671))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.71/4.43  tff(c_9723, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_9494, c_9716])).
% 12.71/4.43  tff(c_9728, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9463, c_9723])).
% 12.71/4.43  tff(c_9735, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_9728, c_9499])).
% 12.71/4.43  tff(c_9751, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_9735, c_9506])).
% 12.71/4.43  tff(c_10019, plain, (![A_700, B_701, C_702, D_703]: (v1_funct_1(k2_partfun1(A_700, B_701, C_702, D_703)) | ~m1_subset_1(C_702, k1_zfmisc_1(k2_zfmisc_1(A_700, B_701))) | ~v1_funct_1(C_702))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.71/4.43  tff(c_10022, plain, (![A_700, B_701, D_703]: (v1_funct_1(k2_partfun1(A_700, B_701, '#skF_4', D_703)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_9751, c_10019])).
% 12.71/4.43  tff(c_10025, plain, (![A_700, B_701, D_703]: (v1_funct_1(k2_partfun1(A_700, B_701, '#skF_4', D_703)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_10022])).
% 12.71/4.43  tff(c_9550, plain, (![B_648, A_649]: (~r1_xboole_0(B_648, A_649) | ~r1_tarski(B_648, A_649) | v1_xboole_0(B_648))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.71/4.43  tff(c_9555, plain, (![A_650]: (~r1_tarski(A_650, '#skF_1') | v1_xboole_0(A_650))), inference(resolution, [status(thm)], [c_9462, c_9550])).
% 12.71/4.43  tff(c_9559, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_9555])).
% 12.71/4.43  tff(c_9566, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_9559, c_9499])).
% 12.71/4.43  tff(c_9548, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9468, c_9468, c_9468, c_9468, c_9468, c_70])).
% 12.71/4.43  tff(c_9549, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_9548])).
% 12.71/4.43  tff(c_9580, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9566, c_9549])).
% 12.71/4.43  tff(c_9746, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9735, c_9735, c_9735, c_9580])).
% 12.71/4.43  tff(c_10028, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10025, c_9746])).
% 12.71/4.43  tff(c_10029, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(splitRight, [status(thm)], [c_9548])).
% 12.71/4.43  tff(c_10031, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(splitLeft, [status(thm)], [c_10029])).
% 12.71/4.43  tff(c_10158, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_10048, c_10048, c_10031])).
% 12.71/4.43  tff(c_10216, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_10211, c_10211, c_10211, c_10211, c_10211, c_10158])).
% 12.71/4.43  tff(c_10660, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_10658, c_10216])).
% 12.71/4.43  tff(c_10663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10230, c_10228, c_10660])).
% 12.71/4.43  tff(c_10665, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(splitRight, [status(thm)], [c_10029])).
% 12.71/4.43  tff(c_10699, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_10682, c_10682, c_10665])).
% 12.71/4.43  tff(c_10884, plain, (v1_xboole_0(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_10699, c_10881])).
% 12.71/4.43  tff(c_10894, plain, (v1_xboole_0(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9463, c_10884])).
% 12.71/4.43  tff(c_11143, plain, (v1_xboole_0(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10906, c_10906, c_10906, c_10894])).
% 12.71/4.43  tff(c_10931, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_10906, c_9499])).
% 12.71/4.43  tff(c_11150, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_11143, c_10931])).
% 12.71/4.43  tff(c_10664, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_10029])).
% 12.71/4.43  tff(c_10692, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10682, c_10682, c_10664])).
% 12.71/4.43  tff(c_10925, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10906, c_10906, c_10906, c_10906, c_10906, c_10692])).
% 12.71/4.43  tff(c_11213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11108, c_11150, c_10925])).
% 12.71/4.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.71/4.43  
% 12.71/4.43  Inference rules
% 12.71/4.43  ----------------------
% 12.71/4.43  #Ref     : 0
% 12.71/4.43  #Sup     : 2310
% 12.71/4.43  #Fact    : 0
% 12.71/4.43  #Define  : 0
% 12.71/4.43  #Split   : 16
% 12.71/4.43  #Chain   : 0
% 12.71/4.43  #Close   : 0
% 12.71/4.43  
% 12.71/4.43  Ordering : KBO
% 12.71/4.43  
% 12.71/4.43  Simplification rules
% 12.71/4.43  ----------------------
% 12.71/4.43  #Subsume      : 353
% 12.71/4.43  #Demod        : 4321
% 12.71/4.43  #Tautology    : 1316
% 12.71/4.43  #SimpNegUnit  : 94
% 12.71/4.43  #BackRed      : 173
% 12.71/4.43  
% 12.71/4.43  #Partial instantiations: 0
% 12.71/4.43  #Strategies tried      : 1
% 12.71/4.43  
% 12.71/4.43  Timing (in seconds)
% 12.71/4.43  ----------------------
% 12.71/4.43  Preprocessing        : 0.59
% 12.71/4.43  Parsing              : 0.31
% 12.71/4.43  CNF conversion       : 0.04
% 12.71/4.43  Main loop            : 2.95
% 12.71/4.43  Inferencing          : 0.96
% 12.71/4.43  Reduction            : 1.21
% 12.71/4.43  Demodulation         : 0.93
% 12.71/4.43  BG Simplification    : 0.09
% 12.71/4.43  Subsumption          : 0.48
% 12.71/4.43  Abstraction          : 0.11
% 12.71/4.44  MUC search           : 0.00
% 12.71/4.44  Cooper               : 0.00
% 12.71/4.44  Total                : 3.64
% 12.71/4.44  Index Insertion      : 0.00
% 12.71/4.44  Index Deletion       : 0.00
% 12.71/4.44  Index Matching       : 0.00
% 12.71/4.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
