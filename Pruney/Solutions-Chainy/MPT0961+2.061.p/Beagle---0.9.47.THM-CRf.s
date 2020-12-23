%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:49 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 4.31s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 621 expanded)
%              Number of leaves         :   28 ( 215 expanded)
%              Depth                    :   17
%              Number of atoms          :  219 (1512 expanded)
%              Number of equality atoms :   66 ( 488 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2

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

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_81,axiom,(
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

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2837,plain,(
    ! [A_303] :
      ( r1_tarski(A_303,k2_zfmisc_1(k1_relat_1(A_303),k2_relat_1(A_303)))
      | ~ v1_relat_1(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    ! [A_10] :
      ( r1_tarski(A_10,k2_zfmisc_1(k1_relat_1(A_10),k2_relat_1(A_10)))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_727,plain,(
    ! [A_141,B_142,C_143] :
      ( k1_relset_1(A_141,B_142,C_143) = k1_relat_1(C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1051,plain,(
    ! [A_180,B_181,A_182] :
      ( k1_relset_1(A_180,B_181,A_182) = k1_relat_1(A_182)
      | ~ r1_tarski(A_182,k2_zfmisc_1(A_180,B_181)) ) ),
    inference(resolution,[status(thm)],[c_14,c_727])).

tff(c_1067,plain,(
    ! [A_10] :
      ( k1_relset_1(k1_relat_1(A_10),k2_relat_1(A_10),A_10) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_18,c_1051])).

tff(c_989,plain,(
    ! [B_172,C_173,A_174] :
      ( k1_xboole_0 = B_172
      | v1_funct_2(C_173,A_174,B_172)
      | k1_relset_1(A_174,B_172,C_173) != A_174
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_174,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1697,plain,(
    ! [B_241,A_242,A_243] :
      ( k1_xboole_0 = B_241
      | v1_funct_2(A_242,A_243,B_241)
      | k1_relset_1(A_243,B_241,A_242) != A_243
      | ~ r1_tarski(A_242,k2_zfmisc_1(A_243,B_241)) ) ),
    inference(resolution,[status(thm)],[c_14,c_989])).

tff(c_2504,plain,(
    ! [A_286] :
      ( k2_relat_1(A_286) = k1_xboole_0
      | v1_funct_2(A_286,k1_relat_1(A_286),k2_relat_1(A_286))
      | k1_relset_1(k1_relat_1(A_286),k2_relat_1(A_286),A_286) != k1_relat_1(A_286)
      | ~ v1_relat_1(A_286) ) ),
    inference(resolution,[status(thm)],[c_18,c_1697])).

tff(c_38,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_36,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36])).

tff(c_87,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_2511,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2504,c_87])).

tff(c_2523,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2511])).

tff(c_2526,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2523])).

tff(c_2532,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1067,c_2526])).

tff(c_2538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2532])).

tff(c_2539,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2523])).

tff(c_97,plain,(
    ! [A_37] :
      ( r1_tarski(A_37,k2_zfmisc_1(k1_relat_1(A_37),k2_relat_1(A_37)))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_88,plain,(
    ! [C_29,B_30,A_31] :
      ( ~ v1_xboole_0(C_29)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(C_29))
      | ~ r2_hidden(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_92,plain,(
    ! [B_32,A_33,A_34] :
      ( ~ v1_xboole_0(B_32)
      | ~ r2_hidden(A_33,A_34)
      | ~ r1_tarski(A_34,B_32) ) ),
    inference(resolution,[status(thm)],[c_14,c_88])).

tff(c_95,plain,(
    ! [B_32,A_1] :
      ( ~ v1_xboole_0(B_32)
      | ~ r1_tarski(A_1,B_32)
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_4,c_92])).

tff(c_101,plain,(
    ! [A_37] :
      ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(A_37),k2_relat_1(A_37)))
      | k1_xboole_0 = A_37
      | ~ v1_relat_1(A_37) ) ),
    inference(resolution,[status(thm)],[c_97,c_95])).

tff(c_2551,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_2'),k1_xboole_0))
    | k1_xboole_0 = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2539,c_101])).

tff(c_2565,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2,c_8,c_2551])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_153,plain,(
    ! [A_56,B_57,C_58] :
      ( m1_subset_1(k1_relset_1(A_56,B_57,C_58),k1_zfmisc_1(A_56))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_179,plain,(
    ! [A_59,B_60,C_61] :
      ( r1_tarski(k1_relset_1(A_59,B_60,C_61),A_59)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(resolution,[status(thm)],[c_153,c_12])).

tff(c_189,plain,(
    ! [B_4,C_61] :
      ( r1_tarski(k1_relset_1(k1_xboole_0,B_4,C_61),k1_xboole_0)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_179])).

tff(c_20,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_subset_1(k1_relset_1(A_11,B_12,C_13),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_187,plain,(
    ! [A_3,C_61] :
      ( r1_tarski(k1_relset_1(A_3,k1_xboole_0,C_61),A_3)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_179])).

tff(c_24,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_17,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_45,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_24])).

tff(c_102,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_106,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_102])).

tff(c_259,plain,(
    ! [A_73,B_74,A_75] :
      ( r1_tarski(k1_relset_1(A_73,B_74,A_75),A_73)
      | ~ r1_tarski(A_75,k2_zfmisc_1(A_73,B_74)) ) ),
    inference(resolution,[status(thm)],[c_14,c_179])).

tff(c_228,plain,(
    ! [B_67,C_68] :
      ( r1_tarski(k1_relset_1(k1_xboole_0,B_67,C_68),k1_xboole_0)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_179])).

tff(c_235,plain,(
    ! [B_67,C_68] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | k1_relset_1(k1_xboole_0,B_67,C_68) = k1_xboole_0
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_228,c_95])).

tff(c_241,plain,(
    ! [B_69,C_70] :
      ( k1_relset_1(k1_xboole_0,B_69,C_70) = k1_xboole_0
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_235])).

tff(c_250,plain,(
    ! [B_69,A_5] :
      ( k1_relset_1(k1_xboole_0,B_69,A_5) = k1_xboole_0
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_241])).

tff(c_262,plain,(
    ! [B_69,B_74,A_75] :
      ( k1_relset_1(k1_xboole_0,B_69,k1_relset_1(k1_xboole_0,B_74,A_75)) = k1_xboole_0
      | ~ r1_tarski(A_75,k2_zfmisc_1(k1_xboole_0,B_74)) ) ),
    inference(resolution,[status(thm)],[c_259,c_250])).

tff(c_291,plain,(
    ! [B_78,B_79,A_80] :
      ( k1_relset_1(k1_xboole_0,B_78,k1_relset_1(k1_xboole_0,B_79,A_80)) = k1_xboole_0
      | ~ r1_tarski(A_80,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_262])).

tff(c_191,plain,(
    ! [A_59,B_60,A_5] :
      ( r1_tarski(k1_relset_1(A_59,B_60,A_5),A_59)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_59,B_60)) ) ),
    inference(resolution,[status(thm)],[c_14,c_179])).

tff(c_300,plain,(
    ! [B_79,A_80,B_78] :
      ( r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_relset_1(k1_xboole_0,B_79,A_80),k2_zfmisc_1(k1_xboole_0,B_78))
      | ~ r1_tarski(A_80,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_191])).

tff(c_318,plain,(
    ! [B_79,A_80] :
      ( r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_relset_1(k1_xboole_0,B_79,A_80),k1_xboole_0)
      | ~ r1_tarski(A_80,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_300])).

tff(c_325,plain,(
    ! [B_81,A_82] :
      ( ~ r1_tarski(k1_relset_1(k1_xboole_0,B_81,A_82),k1_xboole_0)
      | ~ r1_tarski(A_82,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_318])).

tff(c_375,plain,(
    ! [C_87] :
      ( ~ r1_tarski(C_87,k1_xboole_0)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_187,c_325])).

tff(c_379,plain,(
    ! [B_12,C_13] :
      ( ~ r1_tarski(k1_relset_1(k1_xboole_0,B_12,C_13),k1_xboole_0)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_12))) ) ),
    inference(resolution,[status(thm)],[c_20,c_375])).

tff(c_411,plain,(
    ! [B_92,C_93] :
      ( ~ r1_tarski(k1_relset_1(k1_xboole_0,B_92,C_93),k1_xboole_0)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_379])).

tff(c_430,plain,(
    ! [C_94] : ~ m1_subset_1(C_94,k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_189,c_411])).

tff(c_441,plain,(
    ! [A_5] : ~ r1_tarski(A_5,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_430])).

tff(c_108,plain,(
    ! [A_39,B_40,C_41] :
      ( k1_relset_1(A_39,B_40,C_41) = k1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_132,plain,(
    ! [A_50,B_51,A_52] :
      ( k1_relset_1(A_50,B_51,A_52) = k1_relat_1(A_52)
      | ~ r1_tarski(A_52,k2_zfmisc_1(A_50,B_51)) ) ),
    inference(resolution,[status(thm)],[c_14,c_108])).

tff(c_142,plain,(
    ! [A_10] :
      ( k1_relset_1(k1_relat_1(A_10),k2_relat_1(A_10),A_10) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_18,c_132])).

tff(c_192,plain,(
    ! [B_62,C_63,A_64] :
      ( k1_xboole_0 = B_62
      | v1_funct_2(C_63,A_64,B_62)
      | k1_relset_1(A_64,B_62,C_63) != A_64
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_528,plain,(
    ! [B_111,A_112,A_113] :
      ( k1_xboole_0 = B_111
      | v1_funct_2(A_112,A_113,B_111)
      | k1_relset_1(A_113,B_111,A_112) != A_113
      | ~ r1_tarski(A_112,k2_zfmisc_1(A_113,B_111)) ) ),
    inference(resolution,[status(thm)],[c_14,c_192])).

tff(c_675,plain,(
    ! [A_136] :
      ( k2_relat_1(A_136) = k1_xboole_0
      | v1_funct_2(A_136,k1_relat_1(A_136),k2_relat_1(A_136))
      | k1_relset_1(k1_relat_1(A_136),k2_relat_1(A_136),A_136) != k1_relat_1(A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(resolution,[status(thm)],[c_18,c_528])).

tff(c_678,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_675,c_87])).

tff(c_681,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_678])).

tff(c_689,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_681])).

tff(c_692,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_689])).

tff(c_696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_692])).

tff(c_697,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_681])).

tff(c_712,plain,
    ( r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),k1_xboole_0))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_697,c_18])).

tff(c_722,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8,c_712])).

tff(c_724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_441,c_722])).

tff(c_726,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_763,plain,(
    ! [A_146,C_147] :
      ( k1_relset_1(A_146,k1_xboole_0,C_147) = k1_relat_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_727])).

tff(c_769,plain,(
    ! [A_146] : k1_relset_1(A_146,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_726,c_763])).

tff(c_798,plain,(
    ! [A_155,B_156,C_157] :
      ( m1_subset_1(k1_relset_1(A_155,B_156,C_157),k1_zfmisc_1(A_155))
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_816,plain,(
    ! [A_146] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_146))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_146,k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_798])).

tff(c_826,plain,(
    ! [A_158] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_158)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_726,c_8,c_816])).

tff(c_847,plain,(
    ! [A_159] : r1_tarski(k1_relat_1(k1_xboole_0),A_159) ),
    inference(resolution,[status(thm)],[c_826,c_12])).

tff(c_855,plain,(
    ! [A_159] :
      ( ~ v1_xboole_0(A_159)
      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_847,c_95])).

tff(c_856,plain,(
    ! [A_159] : ~ v1_xboole_0(A_159) ),
    inference(splitLeft,[status(thm)],[c_855])).

tff(c_858,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_856,c_2])).

tff(c_859,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_855])).

tff(c_825,plain,(
    ! [A_146] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_146)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_726,c_8,c_816])).

tff(c_897,plain,(
    ! [A_163] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_163)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_859,c_825])).

tff(c_22,plain,(
    ! [A_14,B_15,C_16] :
      ( k1_relset_1(A_14,B_15,C_16) = k1_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_910,plain,(
    ! [A_14,B_15] : k1_relset_1(A_14,B_15,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_897,c_22])).

tff(c_922,plain,(
    ! [A_14,B_15] : k1_relset_1(A_14,B_15,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_859,c_910])).

tff(c_28,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_871,plain,(
    ! [C_160,B_161] :
      ( v1_funct_2(C_160,k1_xboole_0,B_161)
      | k1_relset_1(k1_xboole_0,B_161,C_160) != k1_xboole_0
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_28])).

tff(c_882,plain,(
    ! [B_161] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_161)
      | k1_relset_1(k1_xboole_0,B_161,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_726,c_871])).

tff(c_1031,plain,(
    ! [B_161] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_161) ),
    inference(demodulation,[status(thm),theory(equality)],[c_922,c_882])).

tff(c_2603,plain,(
    ! [B_161] : v1_funct_2('#skF_2','#skF_2',B_161) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2565,c_2565,c_1031])).

tff(c_2611,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2565,c_2565,c_859])).

tff(c_2541,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2539,c_87])).

tff(c_2654,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2565,c_2541])).

tff(c_2662,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2611,c_2654])).

tff(c_2826,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2603,c_2662])).

tff(c_2827,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2832,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_14,c_2827])).

tff(c_2840,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2837,c_2832])).

tff(c_2844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2840])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:52:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.96/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.75  
% 3.96/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.75  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2
% 3.96/1.75  
% 3.96/1.75  %Foreground sorts:
% 3.96/1.75  
% 3.96/1.75  
% 3.96/1.75  %Background operators:
% 3.96/1.75  
% 3.96/1.75  
% 3.96/1.75  %Foreground operators:
% 3.96/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.96/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.96/1.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.96/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.96/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.96/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.96/1.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.96/1.75  tff('#skF_2', type, '#skF_2': $i).
% 3.96/1.75  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.96/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.96/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.96/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.96/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.96/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.96/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.96/1.75  
% 4.31/1.77  tff(f_92, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 4.31/1.77  tff(f_55, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 4.31/1.77  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.31/1.77  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.31/1.77  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.31/1.77  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.31/1.77  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.31/1.77  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.31/1.77  tff(f_51, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.31/1.77  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.31/1.77  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.31/1.77  tff(c_2837, plain, (![A_303]: (r1_tarski(A_303, k2_zfmisc_1(k1_relat_1(A_303), k2_relat_1(A_303))) | ~v1_relat_1(A_303))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.31/1.77  tff(c_14, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.31/1.77  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.31/1.77  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.31/1.77  tff(c_18, plain, (![A_10]: (r1_tarski(A_10, k2_zfmisc_1(k1_relat_1(A_10), k2_relat_1(A_10))) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.31/1.77  tff(c_727, plain, (![A_141, B_142, C_143]: (k1_relset_1(A_141, B_142, C_143)=k1_relat_1(C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.31/1.77  tff(c_1051, plain, (![A_180, B_181, A_182]: (k1_relset_1(A_180, B_181, A_182)=k1_relat_1(A_182) | ~r1_tarski(A_182, k2_zfmisc_1(A_180, B_181)))), inference(resolution, [status(thm)], [c_14, c_727])).
% 4.31/1.77  tff(c_1067, plain, (![A_10]: (k1_relset_1(k1_relat_1(A_10), k2_relat_1(A_10), A_10)=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_18, c_1051])).
% 4.31/1.77  tff(c_989, plain, (![B_172, C_173, A_174]: (k1_xboole_0=B_172 | v1_funct_2(C_173, A_174, B_172) | k1_relset_1(A_174, B_172, C_173)!=A_174 | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_174, B_172))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.31/1.77  tff(c_1697, plain, (![B_241, A_242, A_243]: (k1_xboole_0=B_241 | v1_funct_2(A_242, A_243, B_241) | k1_relset_1(A_243, B_241, A_242)!=A_243 | ~r1_tarski(A_242, k2_zfmisc_1(A_243, B_241)))), inference(resolution, [status(thm)], [c_14, c_989])).
% 4.31/1.77  tff(c_2504, plain, (![A_286]: (k2_relat_1(A_286)=k1_xboole_0 | v1_funct_2(A_286, k1_relat_1(A_286), k2_relat_1(A_286)) | k1_relset_1(k1_relat_1(A_286), k2_relat_1(A_286), A_286)!=k1_relat_1(A_286) | ~v1_relat_1(A_286))), inference(resolution, [status(thm)], [c_18, c_1697])).
% 4.31/1.77  tff(c_38, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.31/1.77  tff(c_36, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.31/1.77  tff(c_42, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36])).
% 4.31/1.77  tff(c_87, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_42])).
% 4.31/1.77  tff(c_2511, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2504, c_87])).
% 4.31/1.77  tff(c_2523, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2511])).
% 4.31/1.77  tff(c_2526, plain, (k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_2523])).
% 4.31/1.77  tff(c_2532, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1067, c_2526])).
% 4.31/1.77  tff(c_2538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_2532])).
% 4.31/1.77  tff(c_2539, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2523])).
% 4.31/1.77  tff(c_97, plain, (![A_37]: (r1_tarski(A_37, k2_zfmisc_1(k1_relat_1(A_37), k2_relat_1(A_37))) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.31/1.77  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.31/1.77  tff(c_88, plain, (![C_29, B_30, A_31]: (~v1_xboole_0(C_29) | ~m1_subset_1(B_30, k1_zfmisc_1(C_29)) | ~r2_hidden(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.31/1.77  tff(c_92, plain, (![B_32, A_33, A_34]: (~v1_xboole_0(B_32) | ~r2_hidden(A_33, A_34) | ~r1_tarski(A_34, B_32))), inference(resolution, [status(thm)], [c_14, c_88])).
% 4.31/1.77  tff(c_95, plain, (![B_32, A_1]: (~v1_xboole_0(B_32) | ~r1_tarski(A_1, B_32) | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_4, c_92])).
% 4.31/1.77  tff(c_101, plain, (![A_37]: (~v1_xboole_0(k2_zfmisc_1(k1_relat_1(A_37), k2_relat_1(A_37))) | k1_xboole_0=A_37 | ~v1_relat_1(A_37))), inference(resolution, [status(thm)], [c_97, c_95])).
% 4.31/1.77  tff(c_2551, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_2'), k1_xboole_0)) | k1_xboole_0='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2539, c_101])).
% 4.31/1.77  tff(c_2565, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2, c_8, c_2551])).
% 4.31/1.77  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.31/1.77  tff(c_153, plain, (![A_56, B_57, C_58]: (m1_subset_1(k1_relset_1(A_56, B_57, C_58), k1_zfmisc_1(A_56)) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.31/1.77  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.31/1.77  tff(c_179, plain, (![A_59, B_60, C_61]: (r1_tarski(k1_relset_1(A_59, B_60, C_61), A_59) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(resolution, [status(thm)], [c_153, c_12])).
% 4.31/1.77  tff(c_189, plain, (![B_4, C_61]: (r1_tarski(k1_relset_1(k1_xboole_0, B_4, C_61), k1_xboole_0) | ~m1_subset_1(C_61, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_179])).
% 4.31/1.77  tff(c_20, plain, (![A_11, B_12, C_13]: (m1_subset_1(k1_relset_1(A_11, B_12, C_13), k1_zfmisc_1(A_11)) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.31/1.77  tff(c_187, plain, (![A_3, C_61]: (r1_tarski(k1_relset_1(A_3, k1_xboole_0, C_61), A_3) | ~m1_subset_1(C_61, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_179])).
% 4.31/1.77  tff(c_24, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_17, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.31/1.77  tff(c_45, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_24])).
% 4.31/1.77  tff(c_102, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_45])).
% 4.31/1.77  tff(c_106, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_102])).
% 4.31/1.77  tff(c_259, plain, (![A_73, B_74, A_75]: (r1_tarski(k1_relset_1(A_73, B_74, A_75), A_73) | ~r1_tarski(A_75, k2_zfmisc_1(A_73, B_74)))), inference(resolution, [status(thm)], [c_14, c_179])).
% 4.31/1.77  tff(c_228, plain, (![B_67, C_68]: (r1_tarski(k1_relset_1(k1_xboole_0, B_67, C_68), k1_xboole_0) | ~m1_subset_1(C_68, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_179])).
% 4.31/1.77  tff(c_235, plain, (![B_67, C_68]: (~v1_xboole_0(k1_xboole_0) | k1_relset_1(k1_xboole_0, B_67, C_68)=k1_xboole_0 | ~m1_subset_1(C_68, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_228, c_95])).
% 4.31/1.77  tff(c_241, plain, (![B_69, C_70]: (k1_relset_1(k1_xboole_0, B_69, C_70)=k1_xboole_0 | ~m1_subset_1(C_70, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_235])).
% 4.31/1.77  tff(c_250, plain, (![B_69, A_5]: (k1_relset_1(k1_xboole_0, B_69, A_5)=k1_xboole_0 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_241])).
% 4.31/1.77  tff(c_262, plain, (![B_69, B_74, A_75]: (k1_relset_1(k1_xboole_0, B_69, k1_relset_1(k1_xboole_0, B_74, A_75))=k1_xboole_0 | ~r1_tarski(A_75, k2_zfmisc_1(k1_xboole_0, B_74)))), inference(resolution, [status(thm)], [c_259, c_250])).
% 4.31/1.77  tff(c_291, plain, (![B_78, B_79, A_80]: (k1_relset_1(k1_xboole_0, B_78, k1_relset_1(k1_xboole_0, B_79, A_80))=k1_xboole_0 | ~r1_tarski(A_80, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_262])).
% 4.31/1.77  tff(c_191, plain, (![A_59, B_60, A_5]: (r1_tarski(k1_relset_1(A_59, B_60, A_5), A_59) | ~r1_tarski(A_5, k2_zfmisc_1(A_59, B_60)))), inference(resolution, [status(thm)], [c_14, c_179])).
% 4.31/1.77  tff(c_300, plain, (![B_79, A_80, B_78]: (r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_relset_1(k1_xboole_0, B_79, A_80), k2_zfmisc_1(k1_xboole_0, B_78)) | ~r1_tarski(A_80, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_291, c_191])).
% 4.31/1.77  tff(c_318, plain, (![B_79, A_80]: (r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_relset_1(k1_xboole_0, B_79, A_80), k1_xboole_0) | ~r1_tarski(A_80, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_300])).
% 4.31/1.77  tff(c_325, plain, (![B_81, A_82]: (~r1_tarski(k1_relset_1(k1_xboole_0, B_81, A_82), k1_xboole_0) | ~r1_tarski(A_82, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_106, c_318])).
% 4.31/1.77  tff(c_375, plain, (![C_87]: (~r1_tarski(C_87, k1_xboole_0) | ~m1_subset_1(C_87, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_187, c_325])).
% 4.31/1.77  tff(c_379, plain, (![B_12, C_13]: (~r1_tarski(k1_relset_1(k1_xboole_0, B_12, C_13), k1_xboole_0) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_12))))), inference(resolution, [status(thm)], [c_20, c_375])).
% 4.31/1.77  tff(c_411, plain, (![B_92, C_93]: (~r1_tarski(k1_relset_1(k1_xboole_0, B_92, C_93), k1_xboole_0) | ~m1_subset_1(C_93, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_379])).
% 4.31/1.77  tff(c_430, plain, (![C_94]: (~m1_subset_1(C_94, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_189, c_411])).
% 4.31/1.77  tff(c_441, plain, (![A_5]: (~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_430])).
% 4.31/1.77  tff(c_108, plain, (![A_39, B_40, C_41]: (k1_relset_1(A_39, B_40, C_41)=k1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.31/1.77  tff(c_132, plain, (![A_50, B_51, A_52]: (k1_relset_1(A_50, B_51, A_52)=k1_relat_1(A_52) | ~r1_tarski(A_52, k2_zfmisc_1(A_50, B_51)))), inference(resolution, [status(thm)], [c_14, c_108])).
% 4.31/1.77  tff(c_142, plain, (![A_10]: (k1_relset_1(k1_relat_1(A_10), k2_relat_1(A_10), A_10)=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_18, c_132])).
% 4.31/1.77  tff(c_192, plain, (![B_62, C_63, A_64]: (k1_xboole_0=B_62 | v1_funct_2(C_63, A_64, B_62) | k1_relset_1(A_64, B_62, C_63)!=A_64 | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_62))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.31/1.77  tff(c_528, plain, (![B_111, A_112, A_113]: (k1_xboole_0=B_111 | v1_funct_2(A_112, A_113, B_111) | k1_relset_1(A_113, B_111, A_112)!=A_113 | ~r1_tarski(A_112, k2_zfmisc_1(A_113, B_111)))), inference(resolution, [status(thm)], [c_14, c_192])).
% 4.31/1.77  tff(c_675, plain, (![A_136]: (k2_relat_1(A_136)=k1_xboole_0 | v1_funct_2(A_136, k1_relat_1(A_136), k2_relat_1(A_136)) | k1_relset_1(k1_relat_1(A_136), k2_relat_1(A_136), A_136)!=k1_relat_1(A_136) | ~v1_relat_1(A_136))), inference(resolution, [status(thm)], [c_18, c_528])).
% 4.31/1.77  tff(c_678, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_675, c_87])).
% 4.31/1.77  tff(c_681, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_678])).
% 4.31/1.77  tff(c_689, plain, (k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_681])).
% 4.31/1.77  tff(c_692, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_142, c_689])).
% 4.31/1.77  tff(c_696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_692])).
% 4.31/1.77  tff(c_697, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_681])).
% 4.31/1.77  tff(c_712, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), k1_xboole_0)) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_697, c_18])).
% 4.31/1.77  tff(c_722, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8, c_712])).
% 4.31/1.77  tff(c_724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_441, c_722])).
% 4.31/1.77  tff(c_726, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_45])).
% 4.31/1.77  tff(c_763, plain, (![A_146, C_147]: (k1_relset_1(A_146, k1_xboole_0, C_147)=k1_relat_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_727])).
% 4.31/1.77  tff(c_769, plain, (![A_146]: (k1_relset_1(A_146, k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_726, c_763])).
% 4.31/1.77  tff(c_798, plain, (![A_155, B_156, C_157]: (m1_subset_1(k1_relset_1(A_155, B_156, C_157), k1_zfmisc_1(A_155)) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.31/1.77  tff(c_816, plain, (![A_146]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_146)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_146, k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_769, c_798])).
% 4.31/1.77  tff(c_826, plain, (![A_158]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_158)))), inference(demodulation, [status(thm), theory('equality')], [c_726, c_8, c_816])).
% 4.31/1.77  tff(c_847, plain, (![A_159]: (r1_tarski(k1_relat_1(k1_xboole_0), A_159))), inference(resolution, [status(thm)], [c_826, c_12])).
% 4.31/1.77  tff(c_855, plain, (![A_159]: (~v1_xboole_0(A_159) | k1_relat_1(k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_847, c_95])).
% 4.31/1.77  tff(c_856, plain, (![A_159]: (~v1_xboole_0(A_159))), inference(splitLeft, [status(thm)], [c_855])).
% 4.31/1.77  tff(c_858, plain, $false, inference(negUnitSimplification, [status(thm)], [c_856, c_2])).
% 4.31/1.77  tff(c_859, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_855])).
% 4.31/1.77  tff(c_825, plain, (![A_146]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_146)))), inference(demodulation, [status(thm), theory('equality')], [c_726, c_8, c_816])).
% 4.31/1.77  tff(c_897, plain, (![A_163]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_163)))), inference(demodulation, [status(thm), theory('equality')], [c_859, c_825])).
% 4.31/1.77  tff(c_22, plain, (![A_14, B_15, C_16]: (k1_relset_1(A_14, B_15, C_16)=k1_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.31/1.77  tff(c_910, plain, (![A_14, B_15]: (k1_relset_1(A_14, B_15, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_897, c_22])).
% 4.31/1.77  tff(c_922, plain, (![A_14, B_15]: (k1_relset_1(A_14, B_15, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_859, c_910])).
% 4.31/1.77  tff(c_28, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.31/1.77  tff(c_871, plain, (![C_160, B_161]: (v1_funct_2(C_160, k1_xboole_0, B_161) | k1_relset_1(k1_xboole_0, B_161, C_160)!=k1_xboole_0 | ~m1_subset_1(C_160, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_28])).
% 4.31/1.77  tff(c_882, plain, (![B_161]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_161) | k1_relset_1(k1_xboole_0, B_161, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_726, c_871])).
% 4.31/1.77  tff(c_1031, plain, (![B_161]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_161))), inference(demodulation, [status(thm), theory('equality')], [c_922, c_882])).
% 4.31/1.77  tff(c_2603, plain, (![B_161]: (v1_funct_2('#skF_2', '#skF_2', B_161))), inference(demodulation, [status(thm), theory('equality')], [c_2565, c_2565, c_1031])).
% 4.31/1.77  tff(c_2611, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2565, c_2565, c_859])).
% 4.31/1.77  tff(c_2541, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2539, c_87])).
% 4.31/1.77  tff(c_2654, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2565, c_2541])).
% 4.31/1.77  tff(c_2662, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2611, c_2654])).
% 4.31/1.77  tff(c_2826, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2603, c_2662])).
% 4.31/1.77  tff(c_2827, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_42])).
% 4.31/1.77  tff(c_2832, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_14, c_2827])).
% 4.31/1.77  tff(c_2840, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2837, c_2832])).
% 4.31/1.77  tff(c_2844, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_2840])).
% 4.31/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.31/1.77  
% 4.31/1.77  Inference rules
% 4.31/1.77  ----------------------
% 4.31/1.77  #Ref     : 0
% 4.31/1.77  #Sup     : 604
% 4.31/1.77  #Fact    : 0
% 4.31/1.77  #Define  : 0
% 4.31/1.77  #Split   : 6
% 4.31/1.77  #Chain   : 0
% 4.31/1.77  #Close   : 0
% 4.31/1.77  
% 4.31/1.77  Ordering : KBO
% 4.31/1.77  
% 4.31/1.77  Simplification rules
% 4.31/1.77  ----------------------
% 4.31/1.77  #Subsume      : 160
% 4.31/1.77  #Demod        : 630
% 4.31/1.77  #Tautology    : 226
% 4.31/1.77  #SimpNegUnit  : 7
% 4.31/1.77  #BackRed      : 61
% 4.31/1.77  
% 4.31/1.77  #Partial instantiations: 0
% 4.31/1.77  #Strategies tried      : 1
% 4.31/1.77  
% 4.31/1.77  Timing (in seconds)
% 4.31/1.77  ----------------------
% 4.31/1.78  Preprocessing        : 0.30
% 4.31/1.78  Parsing              : 0.16
% 4.31/1.78  CNF conversion       : 0.02
% 4.31/1.78  Main loop            : 0.65
% 4.31/1.78  Inferencing          : 0.24
% 4.31/1.78  Reduction            : 0.20
% 4.31/1.78  Demodulation         : 0.14
% 4.31/1.78  BG Simplification    : 0.03
% 4.31/1.78  Subsumption          : 0.13
% 4.31/1.78  Abstraction          : 0.04
% 4.31/1.78  MUC search           : 0.00
% 4.31/1.78  Cooper               : 0.00
% 4.31/1.78  Total                : 1.00
% 4.31/1.78  Index Insertion      : 0.00
% 4.31/1.78  Index Deletion       : 0.00
% 4.31/1.78  Index Matching       : 0.00
% 4.31/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
