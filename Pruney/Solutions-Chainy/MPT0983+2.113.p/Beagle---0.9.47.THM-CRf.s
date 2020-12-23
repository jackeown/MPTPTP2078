%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:17 EST 2020

% Result     : Theorem 9.18s
% Output     : CNFRefutation 9.31s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 364 expanded)
%              Number of leaves         :   49 ( 145 expanded)
%              Depth                    :   12
%              Number of atoms          :  280 (1075 expanded)
%              Number of equality atoms :   48 ( 107 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_187,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_145,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_143,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_129,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_133,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_167,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_91,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_72,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_68,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_121,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( v1_xboole_0(k2_zfmisc_1(A_8,B_9))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_288,plain,(
    ! [B_83,A_84] :
      ( v1_xboole_0(B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_84))
      | ~ v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_299,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_288])).

tff(c_314,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_321,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_314])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_62,plain,(
    ! [A_48] : k6_relat_1(A_48) = k6_partfun1(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_38,plain,(
    ! [A_25] : v2_funct_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_83,plain,(
    ! [A_25] : v2_funct_1(k6_partfun1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_38])).

tff(c_1741,plain,(
    ! [D_181,C_185,F_184,E_180,A_183,B_182] :
      ( k1_partfun1(A_183,B_182,C_185,D_181,E_180,F_184) = k5_relat_1(E_180,F_184)
      | ~ m1_subset_1(F_184,k1_zfmisc_1(k2_zfmisc_1(C_185,D_181)))
      | ~ v1_funct_1(F_184)
      | ~ m1_subset_1(E_180,k1_zfmisc_1(k2_zfmisc_1(A_183,B_182)))
      | ~ v1_funct_1(E_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1757,plain,(
    ! [A_183,B_182,E_180] :
      ( k1_partfun1(A_183,B_182,'#skF_2','#skF_1',E_180,'#skF_4') = k5_relat_1(E_180,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_180,k1_zfmisc_1(k2_zfmisc_1(A_183,B_182)))
      | ~ v1_funct_1(E_180) ) ),
    inference(resolution,[status(thm)],[c_72,c_1741])).

tff(c_3773,plain,(
    ! [A_242,B_243,E_244] :
      ( k1_partfun1(A_242,B_243,'#skF_2','#skF_1',E_244,'#skF_4') = k5_relat_1(E_244,'#skF_4')
      | ~ m1_subset_1(E_244,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243)))
      | ~ v1_funct_1(E_244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1757])).

tff(c_3818,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_3773])).

tff(c_3832,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3818])).

tff(c_52,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39] :
      ( m1_subset_1(k1_partfun1(A_35,B_36,C_37,D_38,E_39,F_40),k1_zfmisc_1(k2_zfmisc_1(A_35,D_38)))
      | ~ m1_subset_1(F_40,k1_zfmisc_1(k2_zfmisc_1(C_37,D_38)))
      | ~ v1_funct_1(F_40)
      | ~ m1_subset_1(E_39,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_1(E_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4522,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3832,c_52])).

tff(c_4529,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_4522])).

tff(c_58,plain,(
    ! [A_41] : m1_subset_1(k6_partfun1(A_41),k1_zfmisc_1(k2_zfmisc_1(A_41,A_41))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_1233,plain,(
    ! [D_148,C_149,A_150,B_151] :
      ( D_148 = C_149
      | ~ r2_relset_1(A_150,B_151,C_149,D_148)
      | ~ m1_subset_1(D_148,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151)))
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1243,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_1233])).

tff(c_1262,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1243])).

tff(c_1270,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1262])).

tff(c_4593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4529,c_3832,c_1270])).

tff(c_4594,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1262])).

tff(c_7019,plain,(
    ! [A_350,B_349,D_351,E_347,C_348] :
      ( k1_xboole_0 = C_348
      | v2_funct_1(D_351)
      | ~ v2_funct_1(k1_partfun1(A_350,B_349,B_349,C_348,D_351,E_347))
      | ~ m1_subset_1(E_347,k1_zfmisc_1(k2_zfmisc_1(B_349,C_348)))
      | ~ v1_funct_2(E_347,B_349,C_348)
      | ~ v1_funct_1(E_347)
      | ~ m1_subset_1(D_351,k1_zfmisc_1(k2_zfmisc_1(A_350,B_349)))
      | ~ v1_funct_2(D_351,A_350,B_349)
      | ~ v1_funct_1(D_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_7023,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4594,c_7019])).

tff(c_7027,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_72,c_83,c_7023])).

tff(c_7028,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_7027])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_7079,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7028,c_2])).

tff(c_7081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_321,c_7079])).

tff(c_7082,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_124,plain,(
    ! [B_70,A_71] :
      ( ~ v1_xboole_0(B_70)
      | B_70 = A_71
      | ~ v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_133,plain,(
    ! [A_71] :
      ( k1_xboole_0 = A_71
      | ~ v1_xboole_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_2,c_124])).

tff(c_7099,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_7082,c_133])).

tff(c_36,plain,(
    ! [A_25] : v1_relat_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_84,plain,(
    ! [A_25] : v1_relat_1(k6_partfun1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_36])).

tff(c_34,plain,(
    ! [A_24] : k2_relat_1(k6_relat_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_85,plain,(
    ! [A_24] : k2_relat_1(k6_partfun1(A_24)) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_34])).

tff(c_191,plain,(
    ! [A_79] :
      ( ~ v1_xboole_0(k2_relat_1(A_79))
      | ~ v1_relat_1(A_79)
      | v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_194,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(A_24)
      | ~ v1_relat_1(k6_partfun1(A_24))
      | v1_xboole_0(k6_partfun1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_191])).

tff(c_229,plain,(
    ! [A_81] :
      ( ~ v1_xboole_0(A_81)
      | v1_xboole_0(k6_partfun1(A_81)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_194])).

tff(c_243,plain,(
    ! [A_82] :
      ( k6_partfun1(A_82) = k1_xboole_0
      | ~ v1_xboole_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_229,c_133])).

tff(c_259,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_243])).

tff(c_280,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_83])).

tff(c_7104,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7099,c_280])).

tff(c_7116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_7104])).

tff(c_7117,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_26,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_7319,plain,(
    ! [B_372,A_373] :
      ( v1_relat_1(B_372)
      | ~ m1_subset_1(B_372,k1_zfmisc_1(A_373))
      | ~ v1_relat_1(A_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_7328,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_7319])).

tff(c_7340,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_7328])).

tff(c_7434,plain,(
    ! [C_384,B_385,A_386] :
      ( v5_relat_1(C_384,B_385)
      | ~ m1_subset_1(C_384,k1_zfmisc_1(k2_zfmisc_1(A_386,B_385))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_7451,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_7434])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_7331,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_7319])).

tff(c_7343,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_7331])).

tff(c_8328,plain,(
    ! [F_452,C_453,B_450,E_448,A_451,D_449] :
      ( k1_partfun1(A_451,B_450,C_453,D_449,E_448,F_452) = k5_relat_1(E_448,F_452)
      | ~ m1_subset_1(F_452,k1_zfmisc_1(k2_zfmisc_1(C_453,D_449)))
      | ~ v1_funct_1(F_452)
      | ~ m1_subset_1(E_448,k1_zfmisc_1(k2_zfmisc_1(A_451,B_450)))
      | ~ v1_funct_1(E_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_8340,plain,(
    ! [A_451,B_450,E_448] :
      ( k1_partfun1(A_451,B_450,'#skF_2','#skF_1',E_448,'#skF_4') = k5_relat_1(E_448,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_448,k1_zfmisc_1(k2_zfmisc_1(A_451,B_450)))
      | ~ v1_funct_1(E_448) ) ),
    inference(resolution,[status(thm)],[c_72,c_8328])).

tff(c_9368,plain,(
    ! [A_502,B_503,E_504] :
      ( k1_partfun1(A_502,B_503,'#skF_2','#skF_1',E_504,'#skF_4') = k5_relat_1(E_504,'#skF_4')
      | ~ m1_subset_1(E_504,k1_zfmisc_1(k2_zfmisc_1(A_502,B_503)))
      | ~ v1_funct_1(E_504) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_8340])).

tff(c_9401,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_9368])).

tff(c_9409,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_9401])).

tff(c_10189,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9409,c_52])).

tff(c_10195,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_10189])).

tff(c_7787,plain,(
    ! [D_413,C_414,A_415,B_416] :
      ( D_413 = C_414
      | ~ r2_relset_1(A_415,B_416,C_414,D_413)
      | ~ m1_subset_1(D_413,k1_zfmisc_1(k2_zfmisc_1(A_415,B_416)))
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(A_415,B_416))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_7797,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_7787])).

tff(c_7816,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_7797])).

tff(c_7919,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_7816])).

tff(c_11118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10195,c_9409,c_7919])).

tff(c_11119,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_7816])).

tff(c_11719,plain,(
    ! [E_575,D_576,C_580,F_579,A_578,B_577] :
      ( k1_partfun1(A_578,B_577,C_580,D_576,E_575,F_579) = k5_relat_1(E_575,F_579)
      | ~ m1_subset_1(F_579,k1_zfmisc_1(k2_zfmisc_1(C_580,D_576)))
      | ~ v1_funct_1(F_579)
      | ~ m1_subset_1(E_575,k1_zfmisc_1(k2_zfmisc_1(A_578,B_577)))
      | ~ v1_funct_1(E_575) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_11731,plain,(
    ! [A_578,B_577,E_575] :
      ( k1_partfun1(A_578,B_577,'#skF_2','#skF_1',E_575,'#skF_4') = k5_relat_1(E_575,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_575,k1_zfmisc_1(k2_zfmisc_1(A_578,B_577)))
      | ~ v1_funct_1(E_575) ) ),
    inference(resolution,[status(thm)],[c_72,c_11719])).

tff(c_12838,plain,(
    ! [A_629,B_630,E_631] :
      ( k1_partfun1(A_629,B_630,'#skF_2','#skF_1',E_631,'#skF_4') = k5_relat_1(E_631,'#skF_4')
      | ~ m1_subset_1(E_631,k1_zfmisc_1(k2_zfmisc_1(A_629,B_630)))
      | ~ v1_funct_1(E_631) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_11731])).

tff(c_12874,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_12838])).

tff(c_12882,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_11119,c_12874])).

tff(c_30,plain,(
    ! [A_21,B_23] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_21,B_23)),k2_relat_1(B_23))
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_12886,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12882,c_30])).

tff(c_12890,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7343,c_7340,c_85,c_12886])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12894,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_12890,c_4])).

tff(c_12895,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_12894])).

tff(c_12898,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_12895])).

tff(c_12902,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7340,c_7451,c_12898])).

tff(c_12903,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12894])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7374,plain,(
    ! [B_376,A_377] :
      ( v5_relat_1(B_376,A_377)
      | ~ r1_tarski(k2_relat_1(B_376),A_377)
      | ~ v1_relat_1(B_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_7389,plain,(
    ! [B_376] :
      ( v5_relat_1(B_376,k2_relat_1(B_376))
      | ~ v1_relat_1(B_376) ) ),
    inference(resolution,[status(thm)],[c_8,c_7374])).

tff(c_7578,plain,(
    ! [B_395] :
      ( v2_funct_2(B_395,k2_relat_1(B_395))
      | ~ v5_relat_1(B_395,k2_relat_1(B_395))
      | ~ v1_relat_1(B_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_7592,plain,(
    ! [B_376] :
      ( v2_funct_2(B_376,k2_relat_1(B_376))
      | ~ v1_relat_1(B_376) ) ),
    inference(resolution,[status(thm)],[c_7389,c_7578])).

tff(c_12913,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12903,c_7592])).

tff(c_12931,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7340,c_12913])).

tff(c_12933,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7117,c_12931])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.18/3.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.18/3.02  
% 9.18/3.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.18/3.02  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.18/3.02  
% 9.18/3.02  %Foreground sorts:
% 9.18/3.02  
% 9.18/3.02  
% 9.18/3.02  %Background operators:
% 9.18/3.02  
% 9.18/3.02  
% 9.18/3.02  %Foreground operators:
% 9.18/3.02  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.18/3.02  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.18/3.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.18/3.02  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.18/3.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.18/3.02  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.18/3.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.18/3.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.18/3.02  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.18/3.02  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.18/3.02  tff('#skF_2', type, '#skF_2': $i).
% 9.18/3.02  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.18/3.02  tff('#skF_3', type, '#skF_3': $i).
% 9.18/3.02  tff('#skF_1', type, '#skF_1': $i).
% 9.18/3.02  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.18/3.02  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.18/3.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.18/3.02  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.18/3.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.18/3.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.18/3.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.18/3.02  tff('#skF_4', type, '#skF_4': $i).
% 9.18/3.02  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.18/3.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.18/3.02  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.18/3.02  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.18/3.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.18/3.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.18/3.02  
% 9.31/3.05  tff(f_187, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 9.31/3.05  tff(f_50, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 9.31/3.05  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 9.31/3.05  tff(f_145, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.31/3.05  tff(f_95, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 9.31/3.05  tff(f_143, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.31/3.05  tff(f_129, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.31/3.05  tff(f_133, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.31/3.05  tff(f_109, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.31/3.05  tff(f_167, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 9.31/3.05  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.31/3.05  tff(f_42, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 9.31/3.05  tff(f_91, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 9.31/3.05  tff(f_80, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 9.31/3.05  tff(f_72, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.31/3.05  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.31/3.05  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.31/3.05  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 9.31/3.05  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 9.31/3.05  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.31/3.05  tff(f_117, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 9.31/3.05  tff(c_68, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.31/3.05  tff(c_121, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 9.31/3.05  tff(c_16, plain, (![A_8, B_9]: (v1_xboole_0(k2_zfmisc_1(A_8, B_9)) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.31/3.05  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.31/3.05  tff(c_288, plain, (![B_83, A_84]: (v1_xboole_0(B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_84)) | ~v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.31/3.05  tff(c_299, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_288])).
% 9.31/3.05  tff(c_314, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_299])).
% 9.31/3.05  tff(c_321, plain, (~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_314])).
% 9.31/3.05  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.31/3.05  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.31/3.05  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.31/3.05  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.31/3.05  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.31/3.05  tff(c_62, plain, (![A_48]: (k6_relat_1(A_48)=k6_partfun1(A_48))), inference(cnfTransformation, [status(thm)], [f_145])).
% 9.31/3.05  tff(c_38, plain, (![A_25]: (v2_funct_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.31/3.05  tff(c_83, plain, (![A_25]: (v2_funct_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_38])).
% 9.31/3.05  tff(c_1741, plain, (![D_181, C_185, F_184, E_180, A_183, B_182]: (k1_partfun1(A_183, B_182, C_185, D_181, E_180, F_184)=k5_relat_1(E_180, F_184) | ~m1_subset_1(F_184, k1_zfmisc_1(k2_zfmisc_1(C_185, D_181))) | ~v1_funct_1(F_184) | ~m1_subset_1(E_180, k1_zfmisc_1(k2_zfmisc_1(A_183, B_182))) | ~v1_funct_1(E_180))), inference(cnfTransformation, [status(thm)], [f_143])).
% 9.31/3.05  tff(c_1757, plain, (![A_183, B_182, E_180]: (k1_partfun1(A_183, B_182, '#skF_2', '#skF_1', E_180, '#skF_4')=k5_relat_1(E_180, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_180, k1_zfmisc_1(k2_zfmisc_1(A_183, B_182))) | ~v1_funct_1(E_180))), inference(resolution, [status(thm)], [c_72, c_1741])).
% 9.31/3.05  tff(c_3773, plain, (![A_242, B_243, E_244]: (k1_partfun1(A_242, B_243, '#skF_2', '#skF_1', E_244, '#skF_4')=k5_relat_1(E_244, '#skF_4') | ~m1_subset_1(E_244, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))) | ~v1_funct_1(E_244))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1757])).
% 9.31/3.05  tff(c_3818, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_3773])).
% 9.31/3.05  tff(c_3832, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3818])).
% 9.31/3.05  tff(c_52, plain, (![A_35, F_40, B_36, C_37, D_38, E_39]: (m1_subset_1(k1_partfun1(A_35, B_36, C_37, D_38, E_39, F_40), k1_zfmisc_1(k2_zfmisc_1(A_35, D_38))) | ~m1_subset_1(F_40, k1_zfmisc_1(k2_zfmisc_1(C_37, D_38))) | ~v1_funct_1(F_40) | ~m1_subset_1(E_39, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_1(E_39))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.31/3.05  tff(c_4522, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3832, c_52])).
% 9.31/3.05  tff(c_4529, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_4522])).
% 9.31/3.05  tff(c_58, plain, (![A_41]: (m1_subset_1(k6_partfun1(A_41), k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.31/3.05  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.31/3.05  tff(c_1233, plain, (![D_148, C_149, A_150, B_151]: (D_148=C_149 | ~r2_relset_1(A_150, B_151, C_149, D_148) | ~m1_subset_1(D_148, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.31/3.05  tff(c_1243, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_1233])).
% 9.31/3.05  tff(c_1262, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1243])).
% 9.31/3.05  tff(c_1270, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1262])).
% 9.31/3.05  tff(c_4593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4529, c_3832, c_1270])).
% 9.31/3.05  tff(c_4594, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1262])).
% 9.31/3.05  tff(c_7019, plain, (![A_350, B_349, D_351, E_347, C_348]: (k1_xboole_0=C_348 | v2_funct_1(D_351) | ~v2_funct_1(k1_partfun1(A_350, B_349, B_349, C_348, D_351, E_347)) | ~m1_subset_1(E_347, k1_zfmisc_1(k2_zfmisc_1(B_349, C_348))) | ~v1_funct_2(E_347, B_349, C_348) | ~v1_funct_1(E_347) | ~m1_subset_1(D_351, k1_zfmisc_1(k2_zfmisc_1(A_350, B_349))) | ~v1_funct_2(D_351, A_350, B_349) | ~v1_funct_1(D_351))), inference(cnfTransformation, [status(thm)], [f_167])).
% 9.31/3.05  tff(c_7023, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4594, c_7019])).
% 9.31/3.05  tff(c_7027, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_72, c_83, c_7023])).
% 9.31/3.05  tff(c_7028, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_121, c_7027])).
% 9.31/3.05  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.31/3.05  tff(c_7079, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7028, c_2])).
% 9.31/3.05  tff(c_7081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_321, c_7079])).
% 9.31/3.05  tff(c_7082, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_299])).
% 9.31/3.05  tff(c_124, plain, (![B_70, A_71]: (~v1_xboole_0(B_70) | B_70=A_71 | ~v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.31/3.05  tff(c_133, plain, (![A_71]: (k1_xboole_0=A_71 | ~v1_xboole_0(A_71))), inference(resolution, [status(thm)], [c_2, c_124])).
% 9.31/3.05  tff(c_7099, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_7082, c_133])).
% 9.31/3.05  tff(c_36, plain, (![A_25]: (v1_relat_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.31/3.05  tff(c_84, plain, (![A_25]: (v1_relat_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_36])).
% 9.31/3.05  tff(c_34, plain, (![A_24]: (k2_relat_1(k6_relat_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.31/3.05  tff(c_85, plain, (![A_24]: (k2_relat_1(k6_partfun1(A_24))=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_34])).
% 9.31/3.05  tff(c_191, plain, (![A_79]: (~v1_xboole_0(k2_relat_1(A_79)) | ~v1_relat_1(A_79) | v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.31/3.05  tff(c_194, plain, (![A_24]: (~v1_xboole_0(A_24) | ~v1_relat_1(k6_partfun1(A_24)) | v1_xboole_0(k6_partfun1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_191])).
% 9.31/3.05  tff(c_229, plain, (![A_81]: (~v1_xboole_0(A_81) | v1_xboole_0(k6_partfun1(A_81)))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_194])).
% 9.31/3.05  tff(c_243, plain, (![A_82]: (k6_partfun1(A_82)=k1_xboole_0 | ~v1_xboole_0(A_82))), inference(resolution, [status(thm)], [c_229, c_133])).
% 9.31/3.05  tff(c_259, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_243])).
% 9.31/3.05  tff(c_280, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_259, c_83])).
% 9.31/3.05  tff(c_7104, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7099, c_280])).
% 9.31/3.05  tff(c_7116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_7104])).
% 9.31/3.05  tff(c_7117, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_68])).
% 9.31/3.05  tff(c_26, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.31/3.05  tff(c_7319, plain, (![B_372, A_373]: (v1_relat_1(B_372) | ~m1_subset_1(B_372, k1_zfmisc_1(A_373)) | ~v1_relat_1(A_373))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.31/3.05  tff(c_7328, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_7319])).
% 9.31/3.05  tff(c_7340, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_7328])).
% 9.31/3.05  tff(c_7434, plain, (![C_384, B_385, A_386]: (v5_relat_1(C_384, B_385) | ~m1_subset_1(C_384, k1_zfmisc_1(k2_zfmisc_1(A_386, B_385))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.31/3.05  tff(c_7451, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_7434])).
% 9.31/3.05  tff(c_24, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.31/3.05  tff(c_7331, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_7319])).
% 9.31/3.05  tff(c_7343, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_7331])).
% 9.31/3.05  tff(c_8328, plain, (![F_452, C_453, B_450, E_448, A_451, D_449]: (k1_partfun1(A_451, B_450, C_453, D_449, E_448, F_452)=k5_relat_1(E_448, F_452) | ~m1_subset_1(F_452, k1_zfmisc_1(k2_zfmisc_1(C_453, D_449))) | ~v1_funct_1(F_452) | ~m1_subset_1(E_448, k1_zfmisc_1(k2_zfmisc_1(A_451, B_450))) | ~v1_funct_1(E_448))), inference(cnfTransformation, [status(thm)], [f_143])).
% 9.31/3.05  tff(c_8340, plain, (![A_451, B_450, E_448]: (k1_partfun1(A_451, B_450, '#skF_2', '#skF_1', E_448, '#skF_4')=k5_relat_1(E_448, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_448, k1_zfmisc_1(k2_zfmisc_1(A_451, B_450))) | ~v1_funct_1(E_448))), inference(resolution, [status(thm)], [c_72, c_8328])).
% 9.31/3.05  tff(c_9368, plain, (![A_502, B_503, E_504]: (k1_partfun1(A_502, B_503, '#skF_2', '#skF_1', E_504, '#skF_4')=k5_relat_1(E_504, '#skF_4') | ~m1_subset_1(E_504, k1_zfmisc_1(k2_zfmisc_1(A_502, B_503))) | ~v1_funct_1(E_504))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_8340])).
% 9.31/3.05  tff(c_9401, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_9368])).
% 9.31/3.05  tff(c_9409, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_9401])).
% 9.31/3.05  tff(c_10189, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9409, c_52])).
% 9.31/3.05  tff(c_10195, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_10189])).
% 9.31/3.05  tff(c_7787, plain, (![D_413, C_414, A_415, B_416]: (D_413=C_414 | ~r2_relset_1(A_415, B_416, C_414, D_413) | ~m1_subset_1(D_413, k1_zfmisc_1(k2_zfmisc_1(A_415, B_416))) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(A_415, B_416))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.31/3.05  tff(c_7797, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_7787])).
% 9.31/3.05  tff(c_7816, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_7797])).
% 9.31/3.05  tff(c_7919, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_7816])).
% 9.31/3.05  tff(c_11118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10195, c_9409, c_7919])).
% 9.31/3.05  tff(c_11119, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_7816])).
% 9.31/3.05  tff(c_11719, plain, (![E_575, D_576, C_580, F_579, A_578, B_577]: (k1_partfun1(A_578, B_577, C_580, D_576, E_575, F_579)=k5_relat_1(E_575, F_579) | ~m1_subset_1(F_579, k1_zfmisc_1(k2_zfmisc_1(C_580, D_576))) | ~v1_funct_1(F_579) | ~m1_subset_1(E_575, k1_zfmisc_1(k2_zfmisc_1(A_578, B_577))) | ~v1_funct_1(E_575))), inference(cnfTransformation, [status(thm)], [f_143])).
% 9.31/3.05  tff(c_11731, plain, (![A_578, B_577, E_575]: (k1_partfun1(A_578, B_577, '#skF_2', '#skF_1', E_575, '#skF_4')=k5_relat_1(E_575, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_575, k1_zfmisc_1(k2_zfmisc_1(A_578, B_577))) | ~v1_funct_1(E_575))), inference(resolution, [status(thm)], [c_72, c_11719])).
% 9.31/3.05  tff(c_12838, plain, (![A_629, B_630, E_631]: (k1_partfun1(A_629, B_630, '#skF_2', '#skF_1', E_631, '#skF_4')=k5_relat_1(E_631, '#skF_4') | ~m1_subset_1(E_631, k1_zfmisc_1(k2_zfmisc_1(A_629, B_630))) | ~v1_funct_1(E_631))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_11731])).
% 9.31/3.05  tff(c_12874, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_12838])).
% 9.31/3.05  tff(c_12882, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_11119, c_12874])).
% 9.31/3.05  tff(c_30, plain, (![A_21, B_23]: (r1_tarski(k2_relat_1(k5_relat_1(A_21, B_23)), k2_relat_1(B_23)) | ~v1_relat_1(B_23) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.31/3.05  tff(c_12886, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12882, c_30])).
% 9.31/3.05  tff(c_12890, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7343, c_7340, c_85, c_12886])).
% 9.31/3.05  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.31/3.05  tff(c_12894, plain, (k2_relat_1('#skF_4')='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_12890, c_4])).
% 9.31/3.05  tff(c_12895, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_12894])).
% 9.31/3.05  tff(c_12898, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_12895])).
% 9.31/3.05  tff(c_12902, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7340, c_7451, c_12898])).
% 9.31/3.05  tff(c_12903, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_12894])).
% 9.31/3.05  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.31/3.05  tff(c_7374, plain, (![B_376, A_377]: (v5_relat_1(B_376, A_377) | ~r1_tarski(k2_relat_1(B_376), A_377) | ~v1_relat_1(B_376))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.31/3.05  tff(c_7389, plain, (![B_376]: (v5_relat_1(B_376, k2_relat_1(B_376)) | ~v1_relat_1(B_376))), inference(resolution, [status(thm)], [c_8, c_7374])).
% 9.31/3.05  tff(c_7578, plain, (![B_395]: (v2_funct_2(B_395, k2_relat_1(B_395)) | ~v5_relat_1(B_395, k2_relat_1(B_395)) | ~v1_relat_1(B_395))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.31/3.05  tff(c_7592, plain, (![B_376]: (v2_funct_2(B_376, k2_relat_1(B_376)) | ~v1_relat_1(B_376))), inference(resolution, [status(thm)], [c_7389, c_7578])).
% 9.31/3.05  tff(c_12913, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12903, c_7592])).
% 9.31/3.05  tff(c_12931, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7340, c_12913])).
% 9.31/3.05  tff(c_12933, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7117, c_12931])).
% 9.31/3.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.31/3.05  
% 9.31/3.05  Inference rules
% 9.31/3.05  ----------------------
% 9.31/3.05  #Ref     : 0
% 9.31/3.05  #Sup     : 3198
% 9.31/3.05  #Fact    : 0
% 9.31/3.05  #Define  : 0
% 9.31/3.05  #Split   : 15
% 9.31/3.05  #Chain   : 0
% 9.31/3.05  #Close   : 0
% 9.31/3.05  
% 9.31/3.05  Ordering : KBO
% 9.31/3.05  
% 9.31/3.05  Simplification rules
% 9.31/3.05  ----------------------
% 9.31/3.05  #Subsume      : 205
% 9.31/3.05  #Demod        : 2802
% 9.31/3.05  #Tautology    : 1975
% 9.31/3.05  #SimpNegUnit  : 5
% 9.31/3.05  #BackRed      : 77
% 9.31/3.05  
% 9.31/3.05  #Partial instantiations: 0
% 9.31/3.05  #Strategies tried      : 1
% 9.31/3.05  
% 9.31/3.05  Timing (in seconds)
% 9.31/3.05  ----------------------
% 9.31/3.05  Preprocessing        : 0.35
% 9.31/3.05  Parsing              : 0.18
% 9.31/3.05  CNF conversion       : 0.03
% 9.31/3.05  Main loop            : 1.92
% 9.31/3.05  Inferencing          : 0.54
% 9.31/3.05  Reduction            : 0.73
% 9.31/3.05  Demodulation         : 0.55
% 9.31/3.05  BG Simplification    : 0.07
% 9.31/3.05  Subsumption          : 0.44
% 9.31/3.05  Abstraction          : 0.08
% 9.31/3.05  MUC search           : 0.00
% 9.31/3.05  Cooper               : 0.00
% 9.31/3.05  Total                : 2.32
% 9.31/3.05  Index Insertion      : 0.00
% 9.31/3.05  Index Deletion       : 0.00
% 9.31/3.05  Index Matching       : 0.00
% 9.31/3.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
