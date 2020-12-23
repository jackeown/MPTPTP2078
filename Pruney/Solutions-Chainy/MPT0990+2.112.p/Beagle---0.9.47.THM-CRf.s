%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:12 EST 2020

% Result     : Theorem 9.23s
% Output     : CNFRefutation 9.46s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 355 expanded)
%              Number of leaves         :   50 ( 145 expanded)
%              Depth                    :   15
%              Number of atoms          :  266 (1188 expanded)
%              Number of equality atoms :   61 ( 304 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_181,negated_conjecture,(
    ~ ! [A,B,C] :
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_155,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_139,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_143,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_127,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_153,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_109,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_64,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_131,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_140,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_76,c_131])).

tff(c_149,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_140])).

tff(c_252,plain,(
    ! [C_87,A_88,B_89] :
      ( v4_relat_1(C_87,A_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_265,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_252])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_137,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_82,c_131])).

tff(c_146,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_137])).

tff(c_86,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_70,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_32,plain,(
    ! [A_26] :
      ( v1_relat_1(k2_funct_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_74,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_492,plain,(
    ! [A_109,B_110,C_111] :
      ( k2_relset_1(A_109,B_110,C_111) = k2_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_498,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_492])).

tff(c_505,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_498])).

tff(c_311,plain,(
    ! [A_99] :
      ( k1_relat_1(k2_funct_1(A_99)) = k2_relat_1(A_99)
      | ~ v2_funct_1(A_99)
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_217,plain,(
    ! [B_81,A_82] :
      ( v4_relat_1(B_81,A_82)
      | ~ r1_tarski(k1_relat_1(B_81),A_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_231,plain,(
    ! [B_81] :
      ( v4_relat_1(B_81,k1_relat_1(B_81))
      | ~ v1_relat_1(B_81) ) ),
    inference(resolution,[status(thm)],[c_6,c_217])).

tff(c_2900,plain,(
    ! [A_207] :
      ( v4_relat_1(k2_funct_1(A_207),k2_relat_1(A_207))
      | ~ v1_relat_1(k2_funct_1(A_207))
      | ~ v2_funct_1(A_207)
      | ~ v1_funct_1(A_207)
      | ~ v1_relat_1(A_207) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_231])).

tff(c_2903,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_2900])).

tff(c_2911,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_86,c_70,c_2903])).

tff(c_2931,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2911])).

tff(c_2934,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_2931])).

tff(c_2938,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_86,c_2934])).

tff(c_2940,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2911])).

tff(c_264,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_82,c_252])).

tff(c_62,plain,(
    ! [A_52] : k6_relat_1(A_52) = k6_partfun1(A_52) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_22,plain,(
    ! [A_22] : k1_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_92,plain,(
    ! [A_22] : k1_relat_1(k6_partfun1(A_22)) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_22])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_2448,plain,(
    ! [C_187,A_185,D_188,F_189,E_190,B_186] :
      ( m1_subset_1(k1_partfun1(A_185,B_186,C_187,D_188,E_190,F_189),k1_zfmisc_1(k2_zfmisc_1(A_185,D_188)))
      | ~ m1_subset_1(F_189,k1_zfmisc_1(k2_zfmisc_1(C_187,D_188)))
      | ~ v1_funct_1(F_189)
      | ~ m1_subset_1(E_190,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186)))
      | ~ v1_funct_1(E_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_58,plain,(
    ! [A_45] : m1_subset_1(k6_partfun1(A_45),k1_zfmisc_1(k2_zfmisc_1(A_45,A_45))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_72,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_1489,plain,(
    ! [D_147,C_148,A_149,B_150] :
      ( D_147 = C_148
      | ~ r2_relset_1(A_149,B_150,C_148,D_147)
      | ~ m1_subset_1(D_147,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150)))
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1497,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_72,c_1489])).

tff(c_1512,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1497])).

tff(c_1656,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1512])).

tff(c_2461,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2448,c_1656])).

tff(c_2483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_2461])).

tff(c_2484,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1512])).

tff(c_2941,plain,(
    ! [C_215,B_211,A_216,F_212,D_213,E_214] :
      ( k1_partfun1(A_216,B_211,C_215,D_213,E_214,F_212) = k5_relat_1(E_214,F_212)
      | ~ m1_subset_1(F_212,k1_zfmisc_1(k2_zfmisc_1(C_215,D_213)))
      | ~ v1_funct_1(F_212)
      | ~ m1_subset_1(E_214,k1_zfmisc_1(k2_zfmisc_1(A_216,B_211)))
      | ~ v1_funct_1(E_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2947,plain,(
    ! [A_216,B_211,E_214] :
      ( k1_partfun1(A_216,B_211,'#skF_2','#skF_1',E_214,'#skF_4') = k5_relat_1(E_214,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_214,k1_zfmisc_1(k2_zfmisc_1(A_216,B_211)))
      | ~ v1_funct_1(E_214) ) ),
    inference(resolution,[status(thm)],[c_76,c_2941])).

tff(c_3533,plain,(
    ! [A_233,B_234,E_235] :
      ( k1_partfun1(A_233,B_234,'#skF_2','#skF_1',E_235,'#skF_4') = k5_relat_1(E_235,'#skF_4')
      | ~ m1_subset_1(E_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ v1_funct_1(E_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2947])).

tff(c_3542,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_3533])).

tff(c_3550,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2484,c_3542])).

tff(c_460,plain,(
    ! [A_107,B_108] :
      ( k10_relat_1(A_107,k1_relat_1(B_108)) = k1_relat_1(k5_relat_1(A_107,B_108))
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k10_relat_1(B_11,A_10),k1_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_474,plain,(
    ! [A_107,B_108] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_107,B_108)),k1_relat_1(A_107))
      | ~ v1_relat_1(A_107)
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_16])).

tff(c_3569,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1('#skF_1')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3550,c_474])).

tff(c_3584,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_149,c_146,c_92,c_3569])).

tff(c_208,plain,(
    ! [B_79,A_80] :
      ( r1_tarski(k1_relat_1(B_79),A_80)
      | ~ v4_relat_1(B_79,A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_214,plain,(
    ! [B_79,A_80] :
      ( k1_relat_1(B_79) = A_80
      | ~ r1_tarski(A_80,k1_relat_1(B_79))
      | ~ v4_relat_1(B_79,A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(resolution,[status(thm)],[c_208,c_2])).

tff(c_3590,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3584,c_214])).

tff(c_3595,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_264,c_3590])).

tff(c_442,plain,(
    ! [A_104] :
      ( k2_relat_1(k2_funct_1(A_104)) = k1_relat_1(A_104)
      | ~ v2_funct_1(A_104)
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28,plain,(
    ! [A_25] :
      ( k5_relat_1(A_25,k6_relat_1(k2_relat_1(A_25))) = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_89,plain,(
    ! [A_25] :
      ( k5_relat_1(A_25,k6_partfun1(k2_relat_1(A_25))) = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_28])).

tff(c_4190,plain,(
    ! [A_251] :
      ( k5_relat_1(k2_funct_1(A_251),k6_partfun1(k1_relat_1(A_251))) = k2_funct_1(A_251)
      | ~ v1_relat_1(k2_funct_1(A_251))
      | ~ v2_funct_1(A_251)
      | ~ v1_funct_1(A_251)
      | ~ v1_relat_1(A_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_89])).

tff(c_4214,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3595,c_4190])).

tff(c_4244,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_86,c_70,c_2940,c_4214])).

tff(c_38,plain,(
    ! [A_28] :
      ( k5_relat_1(k2_funct_1(A_28),A_28) = k6_relat_1(k2_relat_1(A_28))
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_88,plain,(
    ! [A_28] :
      ( k5_relat_1(k2_funct_1(A_28),A_28) = k6_partfun1(k2_relat_1(A_28))
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_38])).

tff(c_806,plain,(
    ! [A_124,B_125,C_126] :
      ( k5_relat_1(k5_relat_1(A_124,B_125),C_126) = k5_relat_1(A_124,k5_relat_1(B_125,C_126))
      | ~ v1_relat_1(C_126)
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7036,plain,(
    ! [A_293,C_294] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_293)),C_294) = k5_relat_1(k2_funct_1(A_293),k5_relat_1(A_293,C_294))
      | ~ v1_relat_1(C_294)
      | ~ v1_relat_1(A_293)
      | ~ v1_relat_1(k2_funct_1(A_293))
      | ~ v2_funct_1(A_293)
      | ~ v1_funct_1(A_293)
      | ~ v1_relat_1(A_293) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_806])).

tff(c_7283,plain,(
    ! [C_294] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_294)) = k5_relat_1(k6_partfun1('#skF_2'),C_294)
      | ~ v1_relat_1(C_294)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_7036])).

tff(c_9992,plain,(
    ! [C_358] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_358)) = k5_relat_1(k6_partfun1('#skF_2'),C_358)
      | ~ v1_relat_1(C_358) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_86,c_70,c_2940,c_146,c_7283])).

tff(c_10073,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3550,c_9992])).

tff(c_10132,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_4244,c_10073])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( k5_relat_1(k6_relat_1(A_23),B_24) = B_24
      | ~ r1_tarski(k1_relat_1(B_24),A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_271,plain,(
    ! [A_92,B_93] :
      ( k5_relat_1(k6_partfun1(A_92),B_93) = B_93
      | ~ r1_tarski(k1_relat_1(B_93),A_92)
      | ~ v1_relat_1(B_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_26])).

tff(c_282,plain,(
    ! [A_6,B_7] :
      ( k5_relat_1(k6_partfun1(A_6),B_7) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_271])).

tff(c_10248,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10132,c_282])).

tff(c_10281,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_265,c_10248])).

tff(c_10283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_10281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.23/3.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.41/3.28  
% 9.41/3.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.41/3.28  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.41/3.28  
% 9.41/3.28  %Foreground sorts:
% 9.41/3.28  
% 9.41/3.28  
% 9.41/3.28  %Background operators:
% 9.41/3.28  
% 9.41/3.28  
% 9.41/3.28  %Foreground operators:
% 9.41/3.28  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.41/3.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.41/3.28  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.41/3.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.41/3.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.41/3.28  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.41/3.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.41/3.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.41/3.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.41/3.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.41/3.28  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.41/3.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.41/3.28  tff('#skF_2', type, '#skF_2': $i).
% 9.41/3.28  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.41/3.28  tff('#skF_3', type, '#skF_3': $i).
% 9.41/3.28  tff('#skF_1', type, '#skF_1': $i).
% 9.41/3.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.41/3.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.41/3.28  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.41/3.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.41/3.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.41/3.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.41/3.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.41/3.28  tff('#skF_4', type, '#skF_4': $i).
% 9.41/3.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.41/3.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.41/3.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.41/3.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.41/3.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.41/3.28  
% 9.46/3.30  tff(f_181, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 9.46/3.30  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.46/3.30  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.46/3.30  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.46/3.30  tff(f_89, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.46/3.30  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.46/3.30  tff(f_99, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 9.46/3.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.46/3.30  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 9.46/3.30  tff(f_155, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.46/3.30  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 9.46/3.30  tff(f_139, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.46/3.30  tff(f_143, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.46/3.30  tff(f_127, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.46/3.30  tff(f_153, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.46/3.30  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 9.46/3.30  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 9.46/3.30  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 9.46/3.30  tff(f_109, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 9.46/3.30  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 9.46/3.30  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 9.46/3.30  tff(c_64, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.46/3.30  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.46/3.30  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.46/3.30  tff(c_131, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.46/3.30  tff(c_140, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_76, c_131])).
% 9.46/3.30  tff(c_149, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_140])).
% 9.46/3.30  tff(c_252, plain, (![C_87, A_88, B_89]: (v4_relat_1(C_87, A_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.46/3.30  tff(c_265, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_252])).
% 9.46/3.30  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.46/3.30  tff(c_137, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_82, c_131])).
% 9.46/3.30  tff(c_146, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_137])).
% 9.46/3.30  tff(c_86, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.46/3.30  tff(c_70, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.46/3.30  tff(c_32, plain, (![A_26]: (v1_relat_1(k2_funct_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.46/3.30  tff(c_74, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.46/3.30  tff(c_492, plain, (![A_109, B_110, C_111]: (k2_relset_1(A_109, B_110, C_111)=k2_relat_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.46/3.30  tff(c_498, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_492])).
% 9.46/3.30  tff(c_505, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_498])).
% 9.46/3.30  tff(c_311, plain, (![A_99]: (k1_relat_1(k2_funct_1(A_99))=k2_relat_1(A_99) | ~v2_funct_1(A_99) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.46/3.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.46/3.30  tff(c_217, plain, (![B_81, A_82]: (v4_relat_1(B_81, A_82) | ~r1_tarski(k1_relat_1(B_81), A_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.46/3.30  tff(c_231, plain, (![B_81]: (v4_relat_1(B_81, k1_relat_1(B_81)) | ~v1_relat_1(B_81))), inference(resolution, [status(thm)], [c_6, c_217])).
% 9.46/3.30  tff(c_2900, plain, (![A_207]: (v4_relat_1(k2_funct_1(A_207), k2_relat_1(A_207)) | ~v1_relat_1(k2_funct_1(A_207)) | ~v2_funct_1(A_207) | ~v1_funct_1(A_207) | ~v1_relat_1(A_207))), inference(superposition, [status(thm), theory('equality')], [c_311, c_231])).
% 9.46/3.30  tff(c_2903, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_505, c_2900])).
% 9.46/3.30  tff(c_2911, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_86, c_70, c_2903])).
% 9.46/3.30  tff(c_2931, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2911])).
% 9.46/3.30  tff(c_2934, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_2931])).
% 9.46/3.30  tff(c_2938, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_86, c_2934])).
% 9.46/3.30  tff(c_2940, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2911])).
% 9.46/3.30  tff(c_264, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_82, c_252])).
% 9.46/3.30  tff(c_62, plain, (![A_52]: (k6_relat_1(A_52)=k6_partfun1(A_52))), inference(cnfTransformation, [status(thm)], [f_155])).
% 9.46/3.30  tff(c_22, plain, (![A_22]: (k1_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.46/3.30  tff(c_92, plain, (![A_22]: (k1_relat_1(k6_partfun1(A_22))=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_22])).
% 9.46/3.30  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.46/3.30  tff(c_2448, plain, (![C_187, A_185, D_188, F_189, E_190, B_186]: (m1_subset_1(k1_partfun1(A_185, B_186, C_187, D_188, E_190, F_189), k1_zfmisc_1(k2_zfmisc_1(A_185, D_188))) | ~m1_subset_1(F_189, k1_zfmisc_1(k2_zfmisc_1(C_187, D_188))) | ~v1_funct_1(F_189) | ~m1_subset_1(E_190, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))) | ~v1_funct_1(E_190))), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.46/3.30  tff(c_58, plain, (![A_45]: (m1_subset_1(k6_partfun1(A_45), k1_zfmisc_1(k2_zfmisc_1(A_45, A_45))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 9.46/3.30  tff(c_72, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.46/3.30  tff(c_1489, plain, (![D_147, C_148, A_149, B_150]: (D_147=C_148 | ~r2_relset_1(A_149, B_150, C_148, D_147) | ~m1_subset_1(D_147, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.46/3.30  tff(c_1497, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_72, c_1489])).
% 9.46/3.30  tff(c_1512, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1497])).
% 9.46/3.30  tff(c_1656, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1512])).
% 9.46/3.30  tff(c_2461, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2448, c_1656])).
% 9.46/3.30  tff(c_2483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_2461])).
% 9.46/3.30  tff(c_2484, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1512])).
% 9.46/3.30  tff(c_2941, plain, (![C_215, B_211, A_216, F_212, D_213, E_214]: (k1_partfun1(A_216, B_211, C_215, D_213, E_214, F_212)=k5_relat_1(E_214, F_212) | ~m1_subset_1(F_212, k1_zfmisc_1(k2_zfmisc_1(C_215, D_213))) | ~v1_funct_1(F_212) | ~m1_subset_1(E_214, k1_zfmisc_1(k2_zfmisc_1(A_216, B_211))) | ~v1_funct_1(E_214))), inference(cnfTransformation, [status(thm)], [f_153])).
% 9.46/3.30  tff(c_2947, plain, (![A_216, B_211, E_214]: (k1_partfun1(A_216, B_211, '#skF_2', '#skF_1', E_214, '#skF_4')=k5_relat_1(E_214, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_214, k1_zfmisc_1(k2_zfmisc_1(A_216, B_211))) | ~v1_funct_1(E_214))), inference(resolution, [status(thm)], [c_76, c_2941])).
% 9.46/3.30  tff(c_3533, plain, (![A_233, B_234, E_235]: (k1_partfun1(A_233, B_234, '#skF_2', '#skF_1', E_235, '#skF_4')=k5_relat_1(E_235, '#skF_4') | ~m1_subset_1(E_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~v1_funct_1(E_235))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2947])).
% 9.46/3.30  tff(c_3542, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_3533])).
% 9.46/3.30  tff(c_3550, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2484, c_3542])).
% 9.46/3.30  tff(c_460, plain, (![A_107, B_108]: (k10_relat_1(A_107, k1_relat_1(B_108))=k1_relat_1(k5_relat_1(A_107, B_108)) | ~v1_relat_1(B_108) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.46/3.30  tff(c_16, plain, (![B_11, A_10]: (r1_tarski(k10_relat_1(B_11, A_10), k1_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.46/3.30  tff(c_474, plain, (![A_107, B_108]: (r1_tarski(k1_relat_1(k5_relat_1(A_107, B_108)), k1_relat_1(A_107)) | ~v1_relat_1(A_107) | ~v1_relat_1(B_108) | ~v1_relat_1(A_107))), inference(superposition, [status(thm), theory('equality')], [c_460, c_16])).
% 9.46/3.30  tff(c_3569, plain, (r1_tarski(k1_relat_1(k6_partfun1('#skF_1')), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3550, c_474])).
% 9.46/3.30  tff(c_3584, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_149, c_146, c_92, c_3569])).
% 9.46/3.30  tff(c_208, plain, (![B_79, A_80]: (r1_tarski(k1_relat_1(B_79), A_80) | ~v4_relat_1(B_79, A_80) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.46/3.30  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.46/3.30  tff(c_214, plain, (![B_79, A_80]: (k1_relat_1(B_79)=A_80 | ~r1_tarski(A_80, k1_relat_1(B_79)) | ~v4_relat_1(B_79, A_80) | ~v1_relat_1(B_79))), inference(resolution, [status(thm)], [c_208, c_2])).
% 9.46/3.30  tff(c_3590, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3584, c_214])).
% 9.46/3.30  tff(c_3595, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_264, c_3590])).
% 9.46/3.30  tff(c_442, plain, (![A_104]: (k2_relat_1(k2_funct_1(A_104))=k1_relat_1(A_104) | ~v2_funct_1(A_104) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.46/3.30  tff(c_28, plain, (![A_25]: (k5_relat_1(A_25, k6_relat_1(k2_relat_1(A_25)))=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.46/3.30  tff(c_89, plain, (![A_25]: (k5_relat_1(A_25, k6_partfun1(k2_relat_1(A_25)))=A_25 | ~v1_relat_1(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_28])).
% 9.46/3.30  tff(c_4190, plain, (![A_251]: (k5_relat_1(k2_funct_1(A_251), k6_partfun1(k1_relat_1(A_251)))=k2_funct_1(A_251) | ~v1_relat_1(k2_funct_1(A_251)) | ~v2_funct_1(A_251) | ~v1_funct_1(A_251) | ~v1_relat_1(A_251))), inference(superposition, [status(thm), theory('equality')], [c_442, c_89])).
% 9.46/3.30  tff(c_4214, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3595, c_4190])).
% 9.46/3.30  tff(c_4244, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_86, c_70, c_2940, c_4214])).
% 9.46/3.30  tff(c_38, plain, (![A_28]: (k5_relat_1(k2_funct_1(A_28), A_28)=k6_relat_1(k2_relat_1(A_28)) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.46/3.30  tff(c_88, plain, (![A_28]: (k5_relat_1(k2_funct_1(A_28), A_28)=k6_partfun1(k2_relat_1(A_28)) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_38])).
% 9.46/3.30  tff(c_806, plain, (![A_124, B_125, C_126]: (k5_relat_1(k5_relat_1(A_124, B_125), C_126)=k5_relat_1(A_124, k5_relat_1(B_125, C_126)) | ~v1_relat_1(C_126) | ~v1_relat_1(B_125) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.46/3.30  tff(c_7036, plain, (![A_293, C_294]: (k5_relat_1(k6_partfun1(k2_relat_1(A_293)), C_294)=k5_relat_1(k2_funct_1(A_293), k5_relat_1(A_293, C_294)) | ~v1_relat_1(C_294) | ~v1_relat_1(A_293) | ~v1_relat_1(k2_funct_1(A_293)) | ~v2_funct_1(A_293) | ~v1_funct_1(A_293) | ~v1_relat_1(A_293))), inference(superposition, [status(thm), theory('equality')], [c_88, c_806])).
% 9.46/3.30  tff(c_7283, plain, (![C_294]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_294))=k5_relat_1(k6_partfun1('#skF_2'), C_294) | ~v1_relat_1(C_294) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_505, c_7036])).
% 9.46/3.30  tff(c_9992, plain, (![C_358]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_358))=k5_relat_1(k6_partfun1('#skF_2'), C_358) | ~v1_relat_1(C_358))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_86, c_70, c_2940, c_146, c_7283])).
% 9.46/3.30  tff(c_10073, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3550, c_9992])).
% 9.46/3.30  tff(c_10132, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_4244, c_10073])).
% 9.46/3.30  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.46/3.30  tff(c_26, plain, (![A_23, B_24]: (k5_relat_1(k6_relat_1(A_23), B_24)=B_24 | ~r1_tarski(k1_relat_1(B_24), A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.46/3.30  tff(c_271, plain, (![A_92, B_93]: (k5_relat_1(k6_partfun1(A_92), B_93)=B_93 | ~r1_tarski(k1_relat_1(B_93), A_92) | ~v1_relat_1(B_93))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_26])).
% 9.46/3.30  tff(c_282, plain, (![A_6, B_7]: (k5_relat_1(k6_partfun1(A_6), B_7)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_12, c_271])).
% 9.46/3.30  tff(c_10248, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10132, c_282])).
% 9.46/3.30  tff(c_10281, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_265, c_10248])).
% 9.46/3.30  tff(c_10283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_10281])).
% 9.46/3.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.46/3.30  
% 9.46/3.30  Inference rules
% 9.46/3.30  ----------------------
% 9.46/3.30  #Ref     : 0
% 9.46/3.30  #Sup     : 2151
% 9.46/3.30  #Fact    : 0
% 9.46/3.30  #Define  : 0
% 9.46/3.30  #Split   : 7
% 9.46/3.30  #Chain   : 0
% 9.46/3.30  #Close   : 0
% 9.46/3.30  
% 9.46/3.30  Ordering : KBO
% 9.46/3.30  
% 9.46/3.30  Simplification rules
% 9.46/3.30  ----------------------
% 9.46/3.30  #Subsume      : 182
% 9.46/3.30  #Demod        : 3623
% 9.46/3.30  #Tautology    : 807
% 9.46/3.30  #SimpNegUnit  : 1
% 9.46/3.30  #BackRed      : 17
% 9.46/3.30  
% 9.46/3.30  #Partial instantiations: 0
% 9.46/3.30  #Strategies tried      : 1
% 9.46/3.30  
% 9.46/3.30  Timing (in seconds)
% 9.46/3.30  ----------------------
% 9.46/3.31  Preprocessing        : 0.37
% 9.46/3.31  Parsing              : 0.20
% 9.46/3.31  CNF conversion       : 0.03
% 9.46/3.31  Main loop            : 2.15
% 9.46/3.31  Inferencing          : 0.64
% 9.46/3.31  Reduction            : 0.95
% 9.46/3.31  Demodulation         : 0.76
% 9.46/3.31  BG Simplification    : 0.07
% 9.46/3.31  Subsumption          : 0.37
% 9.46/3.31  Abstraction          : 0.10
% 9.46/3.31  MUC search           : 0.00
% 9.46/3.31  Cooper               : 0.00
% 9.46/3.31  Total                : 2.56
% 9.46/3.31  Index Insertion      : 0.00
% 9.46/3.31  Index Deletion       : 0.00
% 9.46/3.31  Index Matching       : 0.00
% 9.46/3.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
