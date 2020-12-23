%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:52 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 170 expanded)
%              Number of leaves         :   40 (  77 expanded)
%              Depth                    :    8
%              Number of atoms          :  149 ( 475 expanded)
%              Number of equality atoms :   35 (  90 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
             => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_104,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_54,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_237,plain,(
    ! [A_83,B_84,C_85] :
      ( k2_relset_1(A_83,B_84,C_85) = k2_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_249,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_237])).

tff(c_44,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_260,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_44])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_93,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_105,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_93])).

tff(c_104,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_93])).

tff(c_136,plain,(
    ! [C_60,B_61,A_62] :
      ( v5_relat_1(C_60,B_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_147,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_136])).

tff(c_42,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_18,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_59,plain,(
    ! [A_10] : k2_relat_1(k6_partfun1(A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_18])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_410,plain,(
    ! [E_119,B_118,C_122,A_120,F_121,D_117] :
      ( k1_partfun1(A_120,B_118,C_122,D_117,E_119,F_121) = k5_relat_1(E_119,F_121)
      | ~ m1_subset_1(F_121,k1_zfmisc_1(k2_zfmisc_1(C_122,D_117)))
      | ~ v1_funct_1(F_121)
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_120,B_118)))
      | ~ v1_funct_1(E_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_414,plain,(
    ! [A_120,B_118,E_119] :
      ( k1_partfun1(A_120,B_118,'#skF_1','#skF_2',E_119,'#skF_3') = k5_relat_1(E_119,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_120,B_118)))
      | ~ v1_funct_1(E_119) ) ),
    inference(resolution,[status(thm)],[c_54,c_410])).

tff(c_492,plain,(
    ! [A_129,B_130,E_131] :
      ( k1_partfun1(A_129,B_130,'#skF_1','#skF_2',E_131,'#skF_3') = k5_relat_1(E_131,'#skF_3')
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ v1_funct_1(E_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_414])).

tff(c_501,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_492])).

tff(c_508,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_501])).

tff(c_38,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_46,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_265,plain,(
    ! [D_87,C_88,A_89,B_90] :
      ( D_87 = C_88
      | ~ r2_relset_1(A_89,B_90,C_88,D_87)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_273,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_46,c_265])).

tff(c_288,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_273])).

tff(c_319,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_515,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_319])).

tff(c_526,plain,(
    ! [B_133,C_132,F_135,D_137,E_134,A_136] :
      ( m1_subset_1(k1_partfun1(A_136,B_133,C_132,D_137,E_134,F_135),k1_zfmisc_1(k2_zfmisc_1(A_136,D_137)))
      | ~ m1_subset_1(F_135,k1_zfmisc_1(k2_zfmisc_1(C_132,D_137)))
      | ~ v1_funct_1(F_135)
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_136,B_133)))
      | ~ v1_funct_1(E_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_556,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_526])).

tff(c_571,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_58,c_54,c_556])).

tff(c_574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_515,c_571])).

tff(c_575,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_733,plain,(
    ! [B_166,C_170,D_165,E_167,A_168,F_169] :
      ( k1_partfun1(A_168,B_166,C_170,D_165,E_167,F_169) = k5_relat_1(E_167,F_169)
      | ~ m1_subset_1(F_169,k1_zfmisc_1(k2_zfmisc_1(C_170,D_165)))
      | ~ v1_funct_1(F_169)
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(A_168,B_166)))
      | ~ v1_funct_1(E_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_737,plain,(
    ! [A_168,B_166,E_167] :
      ( k1_partfun1(A_168,B_166,'#skF_1','#skF_2',E_167,'#skF_3') = k5_relat_1(E_167,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(A_168,B_166)))
      | ~ v1_funct_1(E_167) ) ),
    inference(resolution,[status(thm)],[c_54,c_733])).

tff(c_767,plain,(
    ! [A_176,B_177,E_178] :
      ( k1_partfun1(A_176,B_177,'#skF_1','#skF_2',E_178,'#skF_3') = k5_relat_1(E_178,'#skF_3')
      | ~ m1_subset_1(E_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ v1_funct_1(E_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_737])).

tff(c_776,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_767])).

tff(c_783,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_575,c_776])).

tff(c_14,plain,(
    ! [A_7,B_9] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_7,B_9)),k2_relat_1(B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_158,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(k2_relat_1(B_69),A_70)
      | ~ v5_relat_1(B_69,A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_107,plain,(
    ! [A_53,B_54] :
      ( r2_xboole_0(A_53,B_54)
      | B_54 = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( ~ r2_xboole_0(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_119,plain,(
    ! [B_54,A_53] :
      ( ~ r1_tarski(B_54,A_53)
      | B_54 = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_107,c_8])).

tff(c_293,plain,(
    ! [B_91,A_92] :
      ( k2_relat_1(B_91) = A_92
      | ~ r1_tarski(A_92,k2_relat_1(B_91))
      | ~ v5_relat_1(B_91,A_92)
      | ~ v1_relat_1(B_91) ) ),
    inference(resolution,[status(thm)],[c_158,c_119])).

tff(c_313,plain,(
    ! [A_7,B_9] :
      ( k2_relat_1(k5_relat_1(A_7,B_9)) = k2_relat_1(B_9)
      | ~ v5_relat_1(B_9,k2_relat_1(k5_relat_1(A_7,B_9)))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_14,c_293])).

tff(c_790,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_3')) = k2_relat_1('#skF_3')
    | ~ v5_relat_1('#skF_3',k2_relat_1(k6_partfun1('#skF_2')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_313])).

tff(c_803,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_104,c_147,c_59,c_59,c_783,c_790])).

tff(c_805,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_803])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:46:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.52  
% 3.07/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.52  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.32/1.52  
% 3.32/1.52  %Foreground sorts:
% 3.32/1.52  
% 3.32/1.52  
% 3.32/1.52  %Background operators:
% 3.32/1.52  
% 3.32/1.52  
% 3.32/1.52  %Foreground operators:
% 3.32/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.32/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.32/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.52  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.32/1.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.32/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.32/1.52  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.32/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.52  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.32/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.32/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.32/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.32/1.52  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.32/1.52  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.32/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.32/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.32/1.52  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.32/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.32/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.32/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.52  
% 3.32/1.54  tff(f_122, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 3.32/1.54  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.32/1.54  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.32/1.54  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.32/1.54  tff(f_104, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.32/1.54  tff(f_54, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.32/1.54  tff(f_102, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.32/1.54  tff(f_92, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.32/1.54  tff(f_76, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.32/1.54  tff(f_88, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.32/1.54  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.32/1.54  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.32/1.54  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.32/1.54  tff(f_37, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 3.32/1.54  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.32/1.54  tff(c_237, plain, (![A_83, B_84, C_85]: (k2_relset_1(A_83, B_84, C_85)=k2_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.32/1.54  tff(c_249, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_237])).
% 3.32/1.54  tff(c_44, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.32/1.54  tff(c_260, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_249, c_44])).
% 3.32/1.54  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.32/1.54  tff(c_93, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.32/1.54  tff(c_105, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_93])).
% 3.32/1.54  tff(c_104, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_93])).
% 3.32/1.54  tff(c_136, plain, (![C_60, B_61, A_62]: (v5_relat_1(C_60, B_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.32/1.54  tff(c_147, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_136])).
% 3.32/1.54  tff(c_42, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.32/1.54  tff(c_18, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.32/1.54  tff(c_59, plain, (![A_10]: (k2_relat_1(k6_partfun1(A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_18])).
% 3.32/1.54  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.32/1.54  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.32/1.54  tff(c_410, plain, (![E_119, B_118, C_122, A_120, F_121, D_117]: (k1_partfun1(A_120, B_118, C_122, D_117, E_119, F_121)=k5_relat_1(E_119, F_121) | ~m1_subset_1(F_121, k1_zfmisc_1(k2_zfmisc_1(C_122, D_117))) | ~v1_funct_1(F_121) | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_120, B_118))) | ~v1_funct_1(E_119))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.32/1.54  tff(c_414, plain, (![A_120, B_118, E_119]: (k1_partfun1(A_120, B_118, '#skF_1', '#skF_2', E_119, '#skF_3')=k5_relat_1(E_119, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_120, B_118))) | ~v1_funct_1(E_119))), inference(resolution, [status(thm)], [c_54, c_410])).
% 3.32/1.54  tff(c_492, plain, (![A_129, B_130, E_131]: (k1_partfun1(A_129, B_130, '#skF_1', '#skF_2', E_131, '#skF_3')=k5_relat_1(E_131, '#skF_3') | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~v1_funct_1(E_131))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_414])).
% 3.32/1.54  tff(c_501, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_492])).
% 3.32/1.54  tff(c_508, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_501])).
% 3.32/1.54  tff(c_38, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.32/1.54  tff(c_46, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.32/1.54  tff(c_265, plain, (![D_87, C_88, A_89, B_90]: (D_87=C_88 | ~r2_relset_1(A_89, B_90, C_88, D_87) | ~m1_subset_1(D_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.32/1.54  tff(c_273, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_46, c_265])).
% 3.32/1.54  tff(c_288, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_273])).
% 3.32/1.54  tff(c_319, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_288])).
% 3.32/1.54  tff(c_515, plain, (~m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_508, c_319])).
% 3.32/1.54  tff(c_526, plain, (![B_133, C_132, F_135, D_137, E_134, A_136]: (m1_subset_1(k1_partfun1(A_136, B_133, C_132, D_137, E_134, F_135), k1_zfmisc_1(k2_zfmisc_1(A_136, D_137))) | ~m1_subset_1(F_135, k1_zfmisc_1(k2_zfmisc_1(C_132, D_137))) | ~v1_funct_1(F_135) | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_136, B_133))) | ~v1_funct_1(E_134))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.32/1.54  tff(c_556, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_508, c_526])).
% 3.32/1.54  tff(c_571, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_58, c_54, c_556])).
% 3.32/1.54  tff(c_574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_515, c_571])).
% 3.32/1.54  tff(c_575, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_288])).
% 3.32/1.54  tff(c_733, plain, (![B_166, C_170, D_165, E_167, A_168, F_169]: (k1_partfun1(A_168, B_166, C_170, D_165, E_167, F_169)=k5_relat_1(E_167, F_169) | ~m1_subset_1(F_169, k1_zfmisc_1(k2_zfmisc_1(C_170, D_165))) | ~v1_funct_1(F_169) | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(A_168, B_166))) | ~v1_funct_1(E_167))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.32/1.54  tff(c_737, plain, (![A_168, B_166, E_167]: (k1_partfun1(A_168, B_166, '#skF_1', '#skF_2', E_167, '#skF_3')=k5_relat_1(E_167, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(A_168, B_166))) | ~v1_funct_1(E_167))), inference(resolution, [status(thm)], [c_54, c_733])).
% 3.32/1.54  tff(c_767, plain, (![A_176, B_177, E_178]: (k1_partfun1(A_176, B_177, '#skF_1', '#skF_2', E_178, '#skF_3')=k5_relat_1(E_178, '#skF_3') | ~m1_subset_1(E_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~v1_funct_1(E_178))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_737])).
% 3.32/1.54  tff(c_776, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_767])).
% 3.32/1.54  tff(c_783, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_575, c_776])).
% 3.32/1.54  tff(c_14, plain, (![A_7, B_9]: (r1_tarski(k2_relat_1(k5_relat_1(A_7, B_9)), k2_relat_1(B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.32/1.54  tff(c_158, plain, (![B_69, A_70]: (r1_tarski(k2_relat_1(B_69), A_70) | ~v5_relat_1(B_69, A_70) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.32/1.54  tff(c_107, plain, (![A_53, B_54]: (r2_xboole_0(A_53, B_54) | B_54=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.32/1.54  tff(c_8, plain, (![B_4, A_3]: (~r2_xboole_0(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.32/1.54  tff(c_119, plain, (![B_54, A_53]: (~r1_tarski(B_54, A_53) | B_54=A_53 | ~r1_tarski(A_53, B_54))), inference(resolution, [status(thm)], [c_107, c_8])).
% 3.32/1.54  tff(c_293, plain, (![B_91, A_92]: (k2_relat_1(B_91)=A_92 | ~r1_tarski(A_92, k2_relat_1(B_91)) | ~v5_relat_1(B_91, A_92) | ~v1_relat_1(B_91))), inference(resolution, [status(thm)], [c_158, c_119])).
% 3.32/1.54  tff(c_313, plain, (![A_7, B_9]: (k2_relat_1(k5_relat_1(A_7, B_9))=k2_relat_1(B_9) | ~v5_relat_1(B_9, k2_relat_1(k5_relat_1(A_7, B_9))) | ~v1_relat_1(B_9) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_14, c_293])).
% 3.32/1.54  tff(c_790, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_3'))=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', k2_relat_1(k6_partfun1('#skF_2'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_783, c_313])).
% 3.32/1.54  tff(c_803, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_105, c_104, c_147, c_59, c_59, c_783, c_790])).
% 3.32/1.54  tff(c_805, plain, $false, inference(negUnitSimplification, [status(thm)], [c_260, c_803])).
% 3.32/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.54  
% 3.32/1.54  Inference rules
% 3.32/1.54  ----------------------
% 3.32/1.54  #Ref     : 0
% 3.32/1.54  #Sup     : 149
% 3.32/1.54  #Fact    : 0
% 3.32/1.54  #Define  : 0
% 3.32/1.54  #Split   : 1
% 3.32/1.54  #Chain   : 0
% 3.32/1.54  #Close   : 0
% 3.32/1.54  
% 3.32/1.54  Ordering : KBO
% 3.32/1.54  
% 3.32/1.54  Simplification rules
% 3.32/1.54  ----------------------
% 3.32/1.54  #Subsume      : 15
% 3.32/1.54  #Demod        : 123
% 3.32/1.54  #Tautology    : 48
% 3.32/1.54  #SimpNegUnit  : 3
% 3.32/1.54  #BackRed      : 6
% 3.32/1.54  
% 3.32/1.54  #Partial instantiations: 0
% 3.32/1.54  #Strategies tried      : 1
% 3.32/1.54  
% 3.32/1.54  Timing (in seconds)
% 3.32/1.54  ----------------------
% 3.32/1.54  Preprocessing        : 0.35
% 3.32/1.54  Parsing              : 0.19
% 3.32/1.54  CNF conversion       : 0.02
% 3.32/1.54  Main loop            : 0.37
% 3.32/1.54  Inferencing          : 0.14
% 3.32/1.54  Reduction            : 0.12
% 3.32/1.55  Demodulation         : 0.09
% 3.32/1.55  BG Simplification    : 0.02
% 3.32/1.55  Subsumption          : 0.07
% 3.32/1.55  Abstraction          : 0.02
% 3.32/1.55  MUC search           : 0.00
% 3.32/1.55  Cooper               : 0.00
% 3.32/1.55  Total                : 0.76
% 3.32/1.55  Index Insertion      : 0.00
% 3.32/1.55  Index Deletion       : 0.00
% 3.32/1.55  Index Matching       : 0.00
% 3.32/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
