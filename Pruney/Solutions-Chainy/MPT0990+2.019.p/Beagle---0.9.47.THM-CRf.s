%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:58 EST 2020

% Result     : Theorem 10.55s
% Output     : CNFRefutation 10.63s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 631 expanded)
%              Number of leaves         :   51 ( 246 expanded)
%              Depth                    :   14
%              Number of atoms          :  310 (2382 expanded)
%              Number of equality atoms :   93 ( 697 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_199,negated_conjecture,(
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

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_156,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_154,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_144,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_128,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_140,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_173,axiom,(
    ! [A,B,C] :
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

tff(f_98,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_56,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_119,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_132,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_119])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_171,plain,(
    ! [C_76,A_77,B_78] :
      ( v4_relat_1(C_76,A_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_183,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_171])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_131,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_119])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_52,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_18,plain,(
    ! [A_11] : v2_funct_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_80,plain,(
    ! [A_11] : v2_funct_1(k6_partfun1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_18])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_427,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_relset_1(A_99,B_100,C_101) = k2_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_433,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_427])).

tff(c_440,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_433])).

tff(c_1115,plain,(
    ! [E_166,F_170,A_167,D_169,B_171,C_168] :
      ( k1_partfun1(A_167,B_171,C_168,D_169,E_166,F_170) = k5_relat_1(E_166,F_170)
      | ~ m1_subset_1(F_170,k1_zfmisc_1(k2_zfmisc_1(C_168,D_169)))
      | ~ v1_funct_1(F_170)
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(A_167,B_171)))
      | ~ v1_funct_1(E_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1121,plain,(
    ! [A_167,B_171,E_166] :
      ( k1_partfun1(A_167,B_171,'#skF_2','#skF_1',E_166,'#skF_4') = k5_relat_1(E_166,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(A_167,B_171)))
      | ~ v1_funct_1(E_166) ) ),
    inference(resolution,[status(thm)],[c_68,c_1115])).

tff(c_1157,plain,(
    ! [A_176,B_177,E_178] :
      ( k1_partfun1(A_176,B_177,'#skF_2','#skF_1',E_178,'#skF_4') = k5_relat_1(E_178,'#skF_4')
      | ~ m1_subset_1(E_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ v1_funct_1(E_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1121])).

tff(c_1163,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1157])).

tff(c_1170,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1163])).

tff(c_48,plain,(
    ! [A_40] : m1_subset_1(k6_partfun1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_64,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_814,plain,(
    ! [D_128,C_129,A_130,B_131] :
      ( D_128 = C_129
      | ~ r2_relset_1(A_130,B_131,C_129,D_128)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131)))
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_822,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_64,c_814])).

tff(c_837,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_822])).

tff(c_919,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_837])).

tff(c_1175,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1170,c_919])).

tff(c_1181,plain,(
    ! [B_183,F_181,C_184,A_179,E_182,D_180] :
      ( m1_subset_1(k1_partfun1(A_179,B_183,C_184,D_180,E_182,F_181),k1_zfmisc_1(k2_zfmisc_1(A_179,D_180)))
      | ~ m1_subset_1(F_181,k1_zfmisc_1(k2_zfmisc_1(C_184,D_180)))
      | ~ v1_funct_1(F_181)
      | ~ m1_subset_1(E_182,k1_zfmisc_1(k2_zfmisc_1(A_179,B_183)))
      | ~ v1_funct_1(E_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1214,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1170,c_1181])).

tff(c_1233,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_1214])).

tff(c_1243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1175,c_1233])).

tff(c_1244,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_837])).

tff(c_1452,plain,(
    ! [D_217,B_219,C_216,A_215,F_218,E_214] :
      ( k1_partfun1(A_215,B_219,C_216,D_217,E_214,F_218) = k5_relat_1(E_214,F_218)
      | ~ m1_subset_1(F_218,k1_zfmisc_1(k2_zfmisc_1(C_216,D_217)))
      | ~ v1_funct_1(F_218)
      | ~ m1_subset_1(E_214,k1_zfmisc_1(k2_zfmisc_1(A_215,B_219)))
      | ~ v1_funct_1(E_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1458,plain,(
    ! [A_215,B_219,E_214] :
      ( k1_partfun1(A_215,B_219,'#skF_2','#skF_1',E_214,'#skF_4') = k5_relat_1(E_214,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_214,k1_zfmisc_1(k2_zfmisc_1(A_215,B_219)))
      | ~ v1_funct_1(E_214) ) ),
    inference(resolution,[status(thm)],[c_68,c_1452])).

tff(c_1618,plain,(
    ! [A_231,B_232,E_233] :
      ( k1_partfun1(A_231,B_232,'#skF_2','#skF_1',E_233,'#skF_4') = k5_relat_1(E_233,'#skF_4')
      | ~ m1_subset_1(E_233,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232)))
      | ~ v1_funct_1(E_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1458])).

tff(c_1630,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1618])).

tff(c_1641,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1244,c_1630])).

tff(c_22,plain,(
    ! [A_14,B_16] :
      ( v2_funct_1(A_14)
      | k2_relat_1(B_16) != k1_relat_1(A_14)
      | ~ v2_funct_1(k5_relat_1(B_16,A_14))
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1654,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1641,c_22])).

tff(c_1662,plain,
    ( v2_funct_1('#skF_4')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_72,c_131,c_78,c_80,c_440,c_1654])).

tff(c_1664,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1662])).

tff(c_182,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_171])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_186,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_182,c_10])).

tff(c_189,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_186])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_216,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_6])).

tff(c_220,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_216])).

tff(c_442,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_220])).

tff(c_12,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_83,plain,(
    ! [A_10] : k1_relat_1(k6_partfun1(A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_12])).

tff(c_8,plain,(
    ! [A_5,B_7] :
      ( k10_relat_1(A_5,k1_relat_1(B_7)) = k1_relat_1(k5_relat_1(A_5,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_478,plain,(
    ! [B_105,A_106] :
      ( k9_relat_1(B_105,k10_relat_1(B_105,A_106)) = A_106
      | ~ r1_tarski(A_106,k2_relat_1(B_105))
      | ~ v1_funct_1(B_105)
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_480,plain,(
    ! [A_106] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_106)) = A_106
      | ~ r1_tarski(A_106,'#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_478])).

tff(c_497,plain,(
    ! [A_107] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_107)) = A_107
      | ~ r1_tarski(A_107,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_78,c_480])).

tff(c_507,plain,(
    ! [B_7] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_7))) = k1_relat_1(B_7)
      | ~ r1_tarski(k1_relat_1(B_7),'#skF_2')
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_497])).

tff(c_511,plain,(
    ! [B_7] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_7))) = k1_relat_1(B_7)
      | ~ r1_tarski(k1_relat_1(B_7),'#skF_2')
      | ~ v1_relat_1(B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_507])).

tff(c_1651,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1641,c_511])).

tff(c_1660,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_442,c_83,c_1651])).

tff(c_1728,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1664,c_1660])).

tff(c_1731,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_1728])).

tff(c_1735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_183,c_1731])).

tff(c_1736,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1662])).

tff(c_192,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_183,c_10])).

tff(c_195,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_192])).

tff(c_1737,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1662])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_416,plain,(
    ! [A_95,B_96,D_97] :
      ( r2_relset_1(A_95,B_96,D_97,D_97)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_423,plain,(
    ! [A_40] : r2_relset_1(A_40,A_40,k6_partfun1(A_40),k6_partfun1(A_40)) ),
    inference(resolution,[status(thm)],[c_48,c_416])).

tff(c_441,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_427])).

tff(c_1792,plain,(
    ! [A_238,B_239,C_240,D_241] :
      ( k2_relset_1(A_238,B_239,C_240) = B_239
      | ~ r2_relset_1(B_239,B_239,k1_partfun1(B_239,A_238,A_238,B_239,D_241,C_240),k6_partfun1(B_239))
      | ~ m1_subset_1(D_241,k1_zfmisc_1(k2_zfmisc_1(B_239,A_238)))
      | ~ v1_funct_2(D_241,B_239,A_238)
      | ~ v1_funct_1(D_241)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239)))
      | ~ v1_funct_2(C_240,A_238,B_239)
      | ~ v1_funct_1(C_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1798,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1244,c_1792])).

tff(c_1802,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_78,c_76,c_74,c_423,c_441,c_1798])).

tff(c_225,plain,
    ( k9_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_6])).

tff(c_229,plain,(
    k9_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_225])).

tff(c_1805,plain,(
    k9_relat_1('#skF_4','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1802,c_229])).

tff(c_26,plain,(
    ! [A_17,B_19] :
      ( k2_funct_1(A_17) = B_19
      | k6_relat_1(k2_relat_1(A_17)) != k5_relat_1(B_19,A_17)
      | k2_relat_1(B_19) != k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1301,plain,(
    ! [A_195,B_196] :
      ( k2_funct_1(A_195) = B_196
      | k6_partfun1(k2_relat_1(A_195)) != k5_relat_1(B_196,A_195)
      | k2_relat_1(B_196) != k1_relat_1(A_195)
      | ~ v2_funct_1(A_195)
      | ~ v1_funct_1(B_196)
      | ~ v1_relat_1(B_196)
      | ~ v1_funct_1(A_195)
      | ~ v1_relat_1(A_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_26])).

tff(c_3185,plain,(
    ! [B_312,A_313,B_314] :
      ( k2_funct_1(k7_relat_1(B_312,A_313)) = B_314
      | k5_relat_1(B_314,k7_relat_1(B_312,A_313)) != k6_partfun1(k9_relat_1(B_312,A_313))
      | k2_relat_1(B_314) != k1_relat_1(k7_relat_1(B_312,A_313))
      | ~ v2_funct_1(k7_relat_1(B_312,A_313))
      | ~ v1_funct_1(B_314)
      | ~ v1_relat_1(B_314)
      | ~ v1_funct_1(k7_relat_1(B_312,A_313))
      | ~ v1_relat_1(k7_relat_1(B_312,A_313))
      | ~ v1_relat_1(B_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1301])).

tff(c_3203,plain,(
    ! [B_314] :
      ( k2_funct_1(k7_relat_1('#skF_4','#skF_2')) = B_314
      | k6_partfun1(k9_relat_1('#skF_4','#skF_2')) != k5_relat_1(B_314,'#skF_4')
      | k2_relat_1(B_314) != k1_relat_1(k7_relat_1('#skF_4','#skF_2'))
      | ~ v2_funct_1(k7_relat_1('#skF_4','#skF_2'))
      | ~ v1_funct_1(B_314)
      | ~ v1_relat_1(B_314)
      | ~ v1_funct_1(k7_relat_1('#skF_4','#skF_2'))
      | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_3185])).

tff(c_9127,plain,(
    ! [B_544] :
      ( k2_funct_1('#skF_4') = B_544
      | k5_relat_1(B_544,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_544) != '#skF_2'
      | ~ v1_funct_1(B_544)
      | ~ v1_relat_1(B_544) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_132,c_195,c_72,c_195,c_1736,c_195,c_1737,c_195,c_1805,c_195,c_3203])).

tff(c_9286,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_9127])).

tff(c_9424,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_440,c_1641,c_9286])).

tff(c_28,plain,(
    ! [A_20] :
      ( k2_funct_1(k2_funct_1(A_20)) = A_20
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_9431,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9424,c_28])).

tff(c_9435,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_72,c_1736,c_9431])).

tff(c_9437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_9435])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.55/4.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.63/4.22  
% 10.63/4.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.63/4.22  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.63/4.22  
% 10.63/4.22  %Foreground sorts:
% 10.63/4.22  
% 10.63/4.22  
% 10.63/4.22  %Background operators:
% 10.63/4.22  
% 10.63/4.22  
% 10.63/4.22  %Foreground operators:
% 10.63/4.22  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.63/4.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.63/4.22  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.63/4.22  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.63/4.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.63/4.22  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.63/4.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.63/4.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.63/4.22  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.63/4.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.63/4.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.63/4.22  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.63/4.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.63/4.22  tff('#skF_2', type, '#skF_2': $i).
% 10.63/4.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.63/4.22  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 10.63/4.22  tff('#skF_3', type, '#skF_3': $i).
% 10.63/4.22  tff('#skF_1', type, '#skF_1': $i).
% 10.63/4.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.63/4.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.63/4.22  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 10.63/4.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.63/4.22  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.63/4.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.63/4.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.63/4.22  tff('#skF_4', type, '#skF_4': $i).
% 10.63/4.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.63/4.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.63/4.22  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.63/4.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.63/4.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.63/4.22  
% 10.63/4.24  tff(f_199, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 10.63/4.24  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.63/4.24  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.63/4.24  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 10.63/4.24  tff(f_156, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.63/4.24  tff(f_56, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 10.63/4.24  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.63/4.24  tff(f_154, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.63/4.24  tff(f_144, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 10.63/4.24  tff(f_128, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.63/4.24  tff(f_140, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 10.63/4.24  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 10.63/4.24  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 10.63/4.24  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 10.63/4.24  tff(f_52, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 10.63/4.24  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 10.63/4.24  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 10.63/4.24  tff(f_173, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 10.63/4.24  tff(f_98, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 10.63/4.24  tff(f_106, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 10.63/4.24  tff(c_56, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_199])).
% 10.63/4.24  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 10.63/4.24  tff(c_119, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.63/4.24  tff(c_132, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_119])).
% 10.63/4.24  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_199])).
% 10.63/4.24  tff(c_171, plain, (![C_76, A_77, B_78]: (v4_relat_1(C_76, A_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.63/4.24  tff(c_183, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_171])).
% 10.63/4.24  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.63/4.24  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 10.63/4.24  tff(c_131, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_119])).
% 10.63/4.24  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 10.63/4.24  tff(c_52, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.63/4.24  tff(c_18, plain, (![A_11]: (v2_funct_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.63/4.24  tff(c_80, plain, (![A_11]: (v2_funct_1(k6_partfun1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_18])).
% 10.63/4.24  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_199])).
% 10.63/4.24  tff(c_427, plain, (![A_99, B_100, C_101]: (k2_relset_1(A_99, B_100, C_101)=k2_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.63/4.24  tff(c_433, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_427])).
% 10.63/4.24  tff(c_440, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_433])).
% 10.63/4.24  tff(c_1115, plain, (![E_166, F_170, A_167, D_169, B_171, C_168]: (k1_partfun1(A_167, B_171, C_168, D_169, E_166, F_170)=k5_relat_1(E_166, F_170) | ~m1_subset_1(F_170, k1_zfmisc_1(k2_zfmisc_1(C_168, D_169))) | ~v1_funct_1(F_170) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(A_167, B_171))) | ~v1_funct_1(E_166))), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.63/4.24  tff(c_1121, plain, (![A_167, B_171, E_166]: (k1_partfun1(A_167, B_171, '#skF_2', '#skF_1', E_166, '#skF_4')=k5_relat_1(E_166, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(A_167, B_171))) | ~v1_funct_1(E_166))), inference(resolution, [status(thm)], [c_68, c_1115])).
% 10.63/4.24  tff(c_1157, plain, (![A_176, B_177, E_178]: (k1_partfun1(A_176, B_177, '#skF_2', '#skF_1', E_178, '#skF_4')=k5_relat_1(E_178, '#skF_4') | ~m1_subset_1(E_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~v1_funct_1(E_178))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1121])).
% 10.63/4.24  tff(c_1163, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1157])).
% 10.63/4.24  tff(c_1170, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1163])).
% 10.63/4.24  tff(c_48, plain, (![A_40]: (m1_subset_1(k6_partfun1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 10.63/4.24  tff(c_64, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_199])).
% 10.63/4.24  tff(c_814, plain, (![D_128, C_129, A_130, B_131]: (D_128=C_129 | ~r2_relset_1(A_130, B_131, C_129, D_128) | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.63/4.24  tff(c_822, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_64, c_814])).
% 10.63/4.24  tff(c_837, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_822])).
% 10.63/4.24  tff(c_919, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_837])).
% 10.63/4.24  tff(c_1175, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1170, c_919])).
% 10.63/4.24  tff(c_1181, plain, (![B_183, F_181, C_184, A_179, E_182, D_180]: (m1_subset_1(k1_partfun1(A_179, B_183, C_184, D_180, E_182, F_181), k1_zfmisc_1(k2_zfmisc_1(A_179, D_180))) | ~m1_subset_1(F_181, k1_zfmisc_1(k2_zfmisc_1(C_184, D_180))) | ~v1_funct_1(F_181) | ~m1_subset_1(E_182, k1_zfmisc_1(k2_zfmisc_1(A_179, B_183))) | ~v1_funct_1(E_182))), inference(cnfTransformation, [status(thm)], [f_140])).
% 10.63/4.24  tff(c_1214, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1170, c_1181])).
% 10.63/4.24  tff(c_1233, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_1214])).
% 10.63/4.24  tff(c_1243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1175, c_1233])).
% 10.63/4.24  tff(c_1244, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_837])).
% 10.63/4.24  tff(c_1452, plain, (![D_217, B_219, C_216, A_215, F_218, E_214]: (k1_partfun1(A_215, B_219, C_216, D_217, E_214, F_218)=k5_relat_1(E_214, F_218) | ~m1_subset_1(F_218, k1_zfmisc_1(k2_zfmisc_1(C_216, D_217))) | ~v1_funct_1(F_218) | ~m1_subset_1(E_214, k1_zfmisc_1(k2_zfmisc_1(A_215, B_219))) | ~v1_funct_1(E_214))), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.63/4.24  tff(c_1458, plain, (![A_215, B_219, E_214]: (k1_partfun1(A_215, B_219, '#skF_2', '#skF_1', E_214, '#skF_4')=k5_relat_1(E_214, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_214, k1_zfmisc_1(k2_zfmisc_1(A_215, B_219))) | ~v1_funct_1(E_214))), inference(resolution, [status(thm)], [c_68, c_1452])).
% 10.63/4.24  tff(c_1618, plain, (![A_231, B_232, E_233]: (k1_partfun1(A_231, B_232, '#skF_2', '#skF_1', E_233, '#skF_4')=k5_relat_1(E_233, '#skF_4') | ~m1_subset_1(E_233, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))) | ~v1_funct_1(E_233))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1458])).
% 10.63/4.24  tff(c_1630, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1618])).
% 10.63/4.24  tff(c_1641, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1244, c_1630])).
% 10.63/4.24  tff(c_22, plain, (![A_14, B_16]: (v2_funct_1(A_14) | k2_relat_1(B_16)!=k1_relat_1(A_14) | ~v2_funct_1(k5_relat_1(B_16, A_14)) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.63/4.24  tff(c_1654, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1641, c_22])).
% 10.63/4.24  tff(c_1662, plain, (v2_funct_1('#skF_4') | k1_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_72, c_131, c_78, c_80, c_440, c_1654])).
% 10.63/4.24  tff(c_1664, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_1662])).
% 10.63/4.24  tff(c_182, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_171])).
% 10.63/4.24  tff(c_10, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.63/4.24  tff(c_186, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_182, c_10])).
% 10.63/4.24  tff(c_189, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_186])).
% 10.63/4.24  tff(c_6, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.63/4.24  tff(c_216, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_189, c_6])).
% 10.63/4.24  tff(c_220, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_216])).
% 10.63/4.24  tff(c_442, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_440, c_220])).
% 10.63/4.24  tff(c_12, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.63/4.24  tff(c_83, plain, (![A_10]: (k1_relat_1(k6_partfun1(A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_12])).
% 10.63/4.24  tff(c_8, plain, (![A_5, B_7]: (k10_relat_1(A_5, k1_relat_1(B_7))=k1_relat_1(k5_relat_1(A_5, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.63/4.24  tff(c_478, plain, (![B_105, A_106]: (k9_relat_1(B_105, k10_relat_1(B_105, A_106))=A_106 | ~r1_tarski(A_106, k2_relat_1(B_105)) | ~v1_funct_1(B_105) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.63/4.24  tff(c_480, plain, (![A_106]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_106))=A_106 | ~r1_tarski(A_106, '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_440, c_478])).
% 10.63/4.24  tff(c_497, plain, (![A_107]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_107))=A_107 | ~r1_tarski(A_107, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_78, c_480])).
% 10.63/4.24  tff(c_507, plain, (![B_7]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_7)))=k1_relat_1(B_7) | ~r1_tarski(k1_relat_1(B_7), '#skF_2') | ~v1_relat_1(B_7) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_497])).
% 10.63/4.24  tff(c_511, plain, (![B_7]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_7)))=k1_relat_1(B_7) | ~r1_tarski(k1_relat_1(B_7), '#skF_2') | ~v1_relat_1(B_7))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_507])).
% 10.63/4.24  tff(c_1651, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1')))=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1641, c_511])).
% 10.63/4.24  tff(c_1660, plain, (k1_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_442, c_83, c_1651])).
% 10.63/4.24  tff(c_1728, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1664, c_1660])).
% 10.63/4.24  tff(c_1731, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4, c_1728])).
% 10.63/4.24  tff(c_1735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_183, c_1731])).
% 10.63/4.24  tff(c_1736, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1662])).
% 10.63/4.24  tff(c_192, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_183, c_10])).
% 10.63/4.24  tff(c_195, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_192])).
% 10.63/4.24  tff(c_1737, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_1662])).
% 10.63/4.24  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_199])).
% 10.63/4.24  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 10.63/4.24  tff(c_416, plain, (![A_95, B_96, D_97]: (r2_relset_1(A_95, B_96, D_97, D_97) | ~m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.63/4.24  tff(c_423, plain, (![A_40]: (r2_relset_1(A_40, A_40, k6_partfun1(A_40), k6_partfun1(A_40)))), inference(resolution, [status(thm)], [c_48, c_416])).
% 10.63/4.24  tff(c_441, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_427])).
% 10.63/4.24  tff(c_1792, plain, (![A_238, B_239, C_240, D_241]: (k2_relset_1(A_238, B_239, C_240)=B_239 | ~r2_relset_1(B_239, B_239, k1_partfun1(B_239, A_238, A_238, B_239, D_241, C_240), k6_partfun1(B_239)) | ~m1_subset_1(D_241, k1_zfmisc_1(k2_zfmisc_1(B_239, A_238))) | ~v1_funct_2(D_241, B_239, A_238) | ~v1_funct_1(D_241) | ~m1_subset_1(C_240, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))) | ~v1_funct_2(C_240, A_238, B_239) | ~v1_funct_1(C_240))), inference(cnfTransformation, [status(thm)], [f_173])).
% 10.63/4.24  tff(c_1798, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1244, c_1792])).
% 10.63/4.24  tff(c_1802, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_78, c_76, c_74, c_423, c_441, c_1798])).
% 10.63/4.24  tff(c_225, plain, (k9_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_195, c_6])).
% 10.63/4.24  tff(c_229, plain, (k9_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_225])).
% 10.63/4.24  tff(c_1805, plain, (k9_relat_1('#skF_4', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1802, c_229])).
% 10.63/4.24  tff(c_26, plain, (![A_17, B_19]: (k2_funct_1(A_17)=B_19 | k6_relat_1(k2_relat_1(A_17))!=k5_relat_1(B_19, A_17) | k2_relat_1(B_19)!=k1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_98])).
% 10.63/4.24  tff(c_1301, plain, (![A_195, B_196]: (k2_funct_1(A_195)=B_196 | k6_partfun1(k2_relat_1(A_195))!=k5_relat_1(B_196, A_195) | k2_relat_1(B_196)!=k1_relat_1(A_195) | ~v2_funct_1(A_195) | ~v1_funct_1(B_196) | ~v1_relat_1(B_196) | ~v1_funct_1(A_195) | ~v1_relat_1(A_195))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_26])).
% 10.63/4.24  tff(c_3185, plain, (![B_312, A_313, B_314]: (k2_funct_1(k7_relat_1(B_312, A_313))=B_314 | k5_relat_1(B_314, k7_relat_1(B_312, A_313))!=k6_partfun1(k9_relat_1(B_312, A_313)) | k2_relat_1(B_314)!=k1_relat_1(k7_relat_1(B_312, A_313)) | ~v2_funct_1(k7_relat_1(B_312, A_313)) | ~v1_funct_1(B_314) | ~v1_relat_1(B_314) | ~v1_funct_1(k7_relat_1(B_312, A_313)) | ~v1_relat_1(k7_relat_1(B_312, A_313)) | ~v1_relat_1(B_312))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1301])).
% 10.63/4.24  tff(c_3203, plain, (![B_314]: (k2_funct_1(k7_relat_1('#skF_4', '#skF_2'))=B_314 | k6_partfun1(k9_relat_1('#skF_4', '#skF_2'))!=k5_relat_1(B_314, '#skF_4') | k2_relat_1(B_314)!=k1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~v2_funct_1(k7_relat_1('#skF_4', '#skF_2')) | ~v1_funct_1(B_314) | ~v1_relat_1(B_314) | ~v1_funct_1(k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_195, c_3185])).
% 10.63/4.24  tff(c_9127, plain, (![B_544]: (k2_funct_1('#skF_4')=B_544 | k5_relat_1(B_544, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_544)!='#skF_2' | ~v1_funct_1(B_544) | ~v1_relat_1(B_544))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_132, c_195, c_72, c_195, c_1736, c_195, c_1737, c_195, c_1805, c_195, c_3203])).
% 10.63/4.24  tff(c_9286, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_131, c_9127])).
% 10.63/4.24  tff(c_9424, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_440, c_1641, c_9286])).
% 10.63/4.24  tff(c_28, plain, (![A_20]: (k2_funct_1(k2_funct_1(A_20))=A_20 | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.63/4.24  tff(c_9431, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9424, c_28])).
% 10.63/4.24  tff(c_9435, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_72, c_1736, c_9431])).
% 10.63/4.24  tff(c_9437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_9435])).
% 10.63/4.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.63/4.24  
% 10.63/4.24  Inference rules
% 10.63/4.24  ----------------------
% 10.63/4.24  #Ref     : 0
% 10.63/4.24  #Sup     : 1946
% 10.63/4.24  #Fact    : 0
% 10.63/4.24  #Define  : 0
% 10.63/4.24  #Split   : 9
% 10.63/4.24  #Chain   : 0
% 10.63/4.24  #Close   : 0
% 10.63/4.24  
% 10.63/4.24  Ordering : KBO
% 10.63/4.24  
% 10.63/4.24  Simplification rules
% 10.63/4.24  ----------------------
% 10.63/4.24  #Subsume      : 46
% 10.63/4.24  #Demod        : 3810
% 10.63/4.24  #Tautology    : 438
% 10.63/4.24  #SimpNegUnit  : 5
% 10.63/4.24  #BackRed      : 44
% 10.63/4.24  
% 10.63/4.24  #Partial instantiations: 0
% 10.63/4.24  #Strategies tried      : 1
% 10.63/4.24  
% 10.63/4.24  Timing (in seconds)
% 10.63/4.24  ----------------------
% 10.80/4.25  Preprocessing        : 0.37
% 10.80/4.25  Parsing              : 0.20
% 10.80/4.25  CNF conversion       : 0.02
% 10.80/4.25  Main loop            : 3.10
% 10.80/4.25  Inferencing          : 0.83
% 10.80/4.25  Reduction            : 1.50
% 10.80/4.25  Demodulation         : 1.23
% 10.80/4.25  BG Simplification    : 0.07
% 10.80/4.25  Subsumption          : 0.54
% 10.80/4.25  Abstraction          : 0.12
% 10.80/4.25  MUC search           : 0.00
% 10.80/4.25  Cooper               : 0.00
% 10.80/4.25  Total                : 3.51
% 10.80/4.25  Index Insertion      : 0.00
% 10.80/4.25  Index Deletion       : 0.00
% 10.80/4.25  Index Matching       : 0.00
% 10.80/4.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
