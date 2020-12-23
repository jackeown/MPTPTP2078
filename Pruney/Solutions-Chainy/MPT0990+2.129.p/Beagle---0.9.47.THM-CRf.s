%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:15 EST 2020

% Result     : Theorem 5.75s
% Output     : CNFRefutation 5.75s
% Verified   : 
% Statistics : Number of formulae       :  189 (3408 expanded)
%              Number of leaves         :   52 (1204 expanded)
%              Depth                    :   25
%              Number of atoms          :  377 (9169 expanded)
%              Number of equality atoms :  114 (2708 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_187,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_161,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_137,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_149,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_135,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_159,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_107,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_117,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_60,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_125,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_131,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_125])).

tff(c_140,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_131])).

tff(c_168,plain,(
    ! [C_69,A_70,B_71] :
      ( v4_relat_1(C_69,A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_179,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_168])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_58,plain,(
    ! [A_54] : k6_relat_1(A_54) = k6_partfun1(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_50,plain,(
    ! [A_41] : m1_subset_1(k6_relat_1(A_41),k1_zfmisc_1(k2_zfmisc_1(A_41,A_41))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_83,plain,(
    ! [A_41] : m1_subset_1(k6_partfun1(A_41),k1_zfmisc_1(k2_zfmisc_1(A_41,A_41))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50])).

tff(c_128,plain,(
    ! [A_41] :
      ( v1_relat_1(k6_partfun1(A_41))
      | ~ v1_relat_1(k2_zfmisc_1(A_41,A_41)) ) ),
    inference(resolution,[status(thm)],[c_83,c_125])).

tff(c_137,plain,(
    ! [A_41] : v1_relat_1(k6_partfun1(A_41)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_128])).

tff(c_18,plain,(
    ! [A_22] : k1_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_89,plain,(
    ! [A_22] : k1_relat_1(k6_partfun1(A_22)) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_18])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_134,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_125])).

tff(c_143,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_134])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_2117,plain,(
    ! [B_180,A_181,D_179,E_178,C_183,F_182] :
      ( m1_subset_1(k1_partfun1(A_181,B_180,C_183,D_179,E_178,F_182),k1_zfmisc_1(k2_zfmisc_1(A_181,D_179)))
      | ~ m1_subset_1(F_182,k1_zfmisc_1(k2_zfmisc_1(C_183,D_179)))
      | ~ v1_funct_1(F_182)
      | ~ m1_subset_1(E_178,k1_zfmisc_1(k2_zfmisc_1(A_181,B_180)))
      | ~ v1_funct_1(E_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_68,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_1515,plain,(
    ! [D_145,C_146,A_147,B_148] :
      ( D_145 = C_146
      | ~ r2_relset_1(A_147,B_148,C_146,D_145)
      | ~ m1_subset_1(D_145,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148)))
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1523,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_1515])).

tff(c_1538,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1523])).

tff(c_1566,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1538])).

tff(c_2130,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2117,c_1566])).

tff(c_2152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_2130])).

tff(c_2153,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1538])).

tff(c_2637,plain,(
    ! [E_206,B_203,F_201,C_205,A_204,D_202] :
      ( k1_partfun1(A_204,B_203,C_205,D_202,E_206,F_201) = k5_relat_1(E_206,F_201)
      | ~ m1_subset_1(F_201,k1_zfmisc_1(k2_zfmisc_1(C_205,D_202)))
      | ~ v1_funct_1(F_201)
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_203)))
      | ~ v1_funct_1(E_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_2643,plain,(
    ! [A_204,B_203,E_206] :
      ( k1_partfun1(A_204,B_203,'#skF_2','#skF_1',E_206,'#skF_4') = k5_relat_1(E_206,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_203)))
      | ~ v1_funct_1(E_206) ) ),
    inference(resolution,[status(thm)],[c_72,c_2637])).

tff(c_3139,plain,(
    ! [A_223,B_224,E_225] :
      ( k1_partfun1(A_223,B_224,'#skF_2','#skF_1',E_225,'#skF_4') = k5_relat_1(E_225,'#skF_4')
      | ~ m1_subset_1(E_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224)))
      | ~ v1_funct_1(E_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2643])).

tff(c_3148,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_3139])).

tff(c_3156,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2153,c_3148])).

tff(c_22,plain,(
    ! [A_23] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_23)),A_23) = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_87,plain,(
    ! [A_23] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_23)),A_23) = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_22])).

tff(c_1261,plain,(
    ! [A_139,B_140,C_141] :
      ( k5_relat_1(k5_relat_1(A_139,B_140),C_141) = k5_relat_1(A_139,k5_relat_1(B_140,C_141))
      | ~ v1_relat_1(C_141)
      | ~ v1_relat_1(B_140)
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1317,plain,(
    ! [A_23,C_141] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_23)),k5_relat_1(A_23,C_141)) = k5_relat_1(A_23,C_141)
      | ~ v1_relat_1(C_141)
      | ~ v1_relat_1(A_23)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_23)))
      | ~ v1_relat_1(A_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_1261])).

tff(c_1337,plain,(
    ! [A_23,C_141] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_23)),k5_relat_1(A_23,C_141)) = k5_relat_1(A_23,C_141)
      | ~ v1_relat_1(C_141)
      | ~ v1_relat_1(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_1317])).

tff(c_3163,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_1')) = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3156,c_1337])).

tff(c_3176,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_1')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_143,c_3156,c_3163])).

tff(c_12,plain,(
    ! [A_10,B_12] :
      ( k10_relat_1(A_10,k1_relat_1(B_12)) = k1_relat_1(k5_relat_1(A_10,B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_22] : k2_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_88,plain,(
    ! [A_22] : k2_relat_1(k6_partfun1(A_22)) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_20])).

tff(c_24,plain,(
    ! [B_25,A_24] :
      ( k5_relat_1(B_25,k6_relat_1(A_24)) = B_25
      | ~ r1_tarski(k2_relat_1(B_25),A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_472,plain,(
    ! [B_104,A_105] :
      ( k5_relat_1(B_104,k6_partfun1(A_105)) = B_104
      | ~ r1_tarski(k2_relat_1(B_104),A_105)
      | ~ v1_relat_1(B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_24])).

tff(c_482,plain,(
    ! [A_22,A_105] :
      ( k5_relat_1(k6_partfun1(A_22),k6_partfun1(A_105)) = k6_partfun1(A_22)
      | ~ r1_tarski(A_22,A_105)
      | ~ v1_relat_1(k6_partfun1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_472])).

tff(c_485,plain,(
    ! [A_22,A_105] :
      ( k5_relat_1(k6_partfun1(A_22),k6_partfun1(A_105)) = k6_partfun1(A_22)
      | ~ r1_tarski(A_22,A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_482])).

tff(c_566,plain,(
    ! [A_110,B_111] :
      ( k10_relat_1(A_110,k1_relat_1(B_111)) = k1_relat_1(k5_relat_1(A_110,B_111))
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_578,plain,(
    ! [A_110,A_22] :
      ( k1_relat_1(k5_relat_1(A_110,k6_partfun1(A_22))) = k10_relat_1(A_110,A_22)
      | ~ v1_relat_1(k6_partfun1(A_22))
      | ~ v1_relat_1(A_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_566])).

tff(c_583,plain,(
    ! [A_112,A_113] :
      ( k1_relat_1(k5_relat_1(A_112,k6_partfun1(A_113))) = k10_relat_1(A_112,A_113)
      | ~ v1_relat_1(A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_578])).

tff(c_613,plain,(
    ! [A_22,A_105] :
      ( k10_relat_1(k6_partfun1(A_22),A_105) = k1_relat_1(k6_partfun1(A_22))
      | ~ v1_relat_1(k6_partfun1(A_22))
      | ~ r1_tarski(A_22,A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_583])).

tff(c_654,plain,(
    ! [A_115,A_116] :
      ( k10_relat_1(k6_partfun1(A_115),A_116) = A_115
      | ~ r1_tarski(A_115,A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_89,c_613])).

tff(c_675,plain,(
    ! [A_115,B_12] :
      ( k1_relat_1(k5_relat_1(k6_partfun1(A_115),B_12)) = A_115
      | ~ r1_tarski(A_115,k1_relat_1(B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(k6_partfun1(A_115)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_654])).

tff(c_687,plain,(
    ! [A_115,B_12] :
      ( k1_relat_1(k5_relat_1(k6_partfun1(A_115),B_12)) = A_115
      | ~ r1_tarski(A_115,k1_relat_1(B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_675])).

tff(c_3355,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(k6_partfun1('#skF_1')))
    | ~ v1_relat_1(k6_partfun1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3176,c_687])).

tff(c_3374,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_89,c_89,c_3355])).

tff(c_3407,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3374])).

tff(c_3410,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_3407])).

tff(c_3414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_179,c_3410])).

tff(c_3415,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3374])).

tff(c_66,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_32,plain,(
    ! [A_29] :
      ( k2_relat_1(k2_funct_1(A_29)) = k1_relat_1(A_29)
      | ~ v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_28,plain,(
    ! [A_26] :
      ( v1_relat_1(k2_funct_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_178,plain,(
    ! [A_41] : v4_relat_1(k6_partfun1(A_41),A_41) ),
    inference(resolution,[status(thm)],[c_83,c_168])).

tff(c_189,plain,(
    ! [B_77,A_78] :
      ( r1_tarski(k1_relat_1(B_77),A_78)
      | ~ v4_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_195,plain,(
    ! [A_22,A_78] :
      ( r1_tarski(A_22,A_78)
      | ~ v4_relat_1(k6_partfun1(A_22),A_78)
      | ~ v1_relat_1(k6_partfun1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_189])).

tff(c_199,plain,(
    ! [A_79,A_80] :
      ( r1_tarski(A_79,A_80)
      | ~ v4_relat_1(k6_partfun1(A_79),A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_195])).

tff(c_207,plain,(
    ! [A_41] : r1_tarski(A_41,A_41) ),
    inference(resolution,[status(thm)],[c_178,c_199])).

tff(c_70,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_688,plain,(
    ! [A_117,B_118,C_119] :
      ( k2_relset_1(A_117,B_118,C_119) = k2_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_694,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_688])).

tff(c_701,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_694])).

tff(c_483,plain,(
    ! [B_104] :
      ( k5_relat_1(B_104,k6_partfun1(k2_relat_1(B_104))) = B_104
      | ~ v1_relat_1(B_104) ) ),
    inference(resolution,[status(thm)],[c_207,c_472])).

tff(c_616,plain,(
    ! [B_104] :
      ( k10_relat_1(B_104,k2_relat_1(B_104)) = k1_relat_1(B_104)
      | ~ v1_relat_1(B_104)
      | ~ v1_relat_1(B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_583])).

tff(c_996,plain,(
    ! [B_128,A_129] :
      ( k9_relat_1(B_128,k10_relat_1(B_128,A_129)) = A_129
      | ~ r1_tarski(A_129,k2_relat_1(B_128))
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_998,plain,(
    ! [A_129] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_129)) = A_129
      | ~ r1_tarski(A_129,'#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_701,c_996])).

tff(c_1017,plain,(
    ! [A_130] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_130)) = A_130
      | ~ r1_tarski(A_130,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_82,c_998])).

tff(c_1027,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_1017])).

tff(c_1038,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_140,c_207,c_701,c_701,c_1027])).

tff(c_38,plain,(
    ! [A_30] :
      ( k5_relat_1(A_30,k2_funct_1(A_30)) = k6_relat_1(k1_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_84,plain,(
    ! [A_30] :
      ( k5_relat_1(A_30,k2_funct_1(A_30)) = k6_partfun1(k1_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_38])).

tff(c_1034,plain,(
    ! [B_12] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_12))) = k1_relat_1(B_12)
      | ~ r1_tarski(k1_relat_1(B_12),'#skF_2')
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1017])).

tff(c_1190,plain,(
    ! [B_137] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_137))) = k1_relat_1(B_137)
      | ~ r1_tarski(k1_relat_1(B_137),'#skF_2')
      | ~ v1_relat_1(B_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_1034])).

tff(c_1200,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_1190])).

tff(c_1218,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_82,c_66,c_1038,c_89,c_1200])).

tff(c_1239,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1218])).

tff(c_1242,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1239])).

tff(c_1246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_82,c_1242])).

tff(c_1248,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1218])).

tff(c_34,plain,(
    ! [A_29] :
      ( k1_relat_1(k2_funct_1(A_29)) = k2_relat_1(A_29)
      | ~ v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1247,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1218])).

tff(c_1249,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1247])).

tff(c_1252,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1249])).

tff(c_1258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_82,c_66,c_207,c_701,c_1252])).

tff(c_1259,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1247])).

tff(c_1365,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1259,c_87])).

tff(c_1388,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1248,c_1365])).

tff(c_16,plain,(
    ! [A_15,B_19,C_21] :
      ( k5_relat_1(k5_relat_1(A_15,B_19),C_21) = k5_relat_1(A_15,k5_relat_1(B_19,C_21))
      | ~ v1_relat_1(C_21)
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1547,plain,(
    ! [C_21] :
      ( k5_relat_1(k6_partfun1('#skF_2'),k5_relat_1(k2_funct_1('#skF_3'),C_21)) = k5_relat_1(k2_funct_1('#skF_3'),C_21)
      | ~ v1_relat_1(C_21)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k6_partfun1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1388,c_16])).

tff(c_2460,plain,(
    ! [C_197] :
      ( k5_relat_1(k6_partfun1('#skF_2'),k5_relat_1(k2_funct_1('#skF_3'),C_197)) = k5_relat_1(k2_funct_1('#skF_3'),C_197)
      | ~ v1_relat_1(C_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_1248,c_1547])).

tff(c_2490,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_2460])).

tff(c_2502,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1248,c_137,c_1388,c_2490])).

tff(c_2543,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2502])).

tff(c_2559,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_82,c_66,c_2543])).

tff(c_3420,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3415,c_2559])).

tff(c_180,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_168])).

tff(c_241,plain,(
    ! [B_87,A_88] :
      ( k7_relat_1(B_87,A_88) = B_87
      | ~ v4_relat_1(B_87,A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_256,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_179,c_241])).

tff(c_269,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_256])).

tff(c_301,plain,(
    ! [B_91,A_92] :
      ( k2_relat_1(k7_relat_1(B_91,A_92)) = k9_relat_1(B_91,A_92)
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_316,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_301])).

tff(c_325,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_316])).

tff(c_703,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_701,c_325])).

tff(c_1042,plain,(
    ! [B_12] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_12))) = k1_relat_1(B_12)
      | ~ r1_tarski(k1_relat_1(B_12),'#skF_2')
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_1034])).

tff(c_3172,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3156,c_1042])).

tff(c_3182,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_703,c_89,c_3172])).

tff(c_3184,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3182])).

tff(c_3187,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_3184])).

tff(c_3191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_180,c_3187])).

tff(c_3192,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3182])).

tff(c_3227,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3192,c_87])).

tff(c_3251,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_3227])).

tff(c_145,plain,(
    ! [A_67] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_67)),A_67) = A_67
      | ~ v1_relat_1(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_22])).

tff(c_154,plain,(
    ! [A_22] :
      ( k5_relat_1(k6_partfun1(A_22),k6_partfun1(A_22)) = k6_partfun1(A_22)
      | ~ v1_relat_1(k6_partfun1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_145])).

tff(c_158,plain,(
    ! [A_22] : k5_relat_1(k6_partfun1(A_22),k6_partfun1(A_22)) = k6_partfun1(A_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_154])).

tff(c_36,plain,(
    ! [A_30] :
      ( k5_relat_1(k2_funct_1(A_30),A_30) = k6_relat_1(k2_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_85,plain,(
    ! [A_30] :
      ( k5_relat_1(k2_funct_1(A_30),A_30) = k6_partfun1(k2_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_36])).

tff(c_2486,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k6_partfun1(k2_relat_1('#skF_3'))) = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_2460])).

tff(c_2500,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_82,c_66,c_140,c_158,c_701,c_2486])).

tff(c_2509,plain,(
    ! [C_21] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_21)) = k5_relat_1(k6_partfun1('#skF_2'),C_21)
      | ~ v1_relat_1(C_21)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2500,c_16])).

tff(c_2521,plain,(
    ! [C_21] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_21)) = k5_relat_1(k6_partfun1('#skF_2'),C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1248,c_140,c_2509])).

tff(c_3166,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3156,c_2521])).

tff(c_3178,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_3166])).

tff(c_4733,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3420,c_3251,c_3178])).

tff(c_4734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4733])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:17:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.75/2.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.75/2.22  
% 5.75/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.75/2.22  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.75/2.22  
% 5.75/2.22  %Foreground sorts:
% 5.75/2.22  
% 5.75/2.22  
% 5.75/2.22  %Background operators:
% 5.75/2.22  
% 5.75/2.22  
% 5.75/2.22  %Foreground operators:
% 5.75/2.22  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.75/2.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.75/2.22  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.75/2.22  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.75/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.75/2.22  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.75/2.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.75/2.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.75/2.22  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.75/2.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.75/2.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.75/2.22  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.75/2.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.75/2.22  tff('#skF_2', type, '#skF_2': $i).
% 5.75/2.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.75/2.22  tff('#skF_3', type, '#skF_3': $i).
% 5.75/2.22  tff('#skF_1', type, '#skF_1': $i).
% 5.75/2.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.75/2.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.75/2.22  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.75/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.75/2.22  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.75/2.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.75/2.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.75/2.22  tff('#skF_4', type, '#skF_4': $i).
% 5.75/2.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.75/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.75/2.22  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.75/2.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.75/2.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.75/2.22  
% 5.75/2.25  tff(f_187, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 5.75/2.25  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.75/2.25  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.75/2.25  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.75/2.25  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 5.75/2.25  tff(f_161, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.75/2.25  tff(f_137, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.75/2.25  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.75/2.25  tff(f_149, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.75/2.25  tff(f_135, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.75/2.25  tff(f_159, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.75/2.25  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 5.75/2.25  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 5.75/2.25  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 5.75/2.25  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 5.75/2.25  tff(f_107, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 5.75/2.25  tff(f_89, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.75/2.25  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.75/2.25  tff(f_97, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 5.75/2.25  tff(f_117, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.75/2.25  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 5.75/2.25  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 5.75/2.25  tff(c_60, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.75/2.25  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.75/2.25  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.75/2.25  tff(c_125, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.75/2.25  tff(c_131, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_125])).
% 5.75/2.25  tff(c_140, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_131])).
% 5.75/2.25  tff(c_168, plain, (![C_69, A_70, B_71]: (v4_relat_1(C_69, A_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.75/2.25  tff(c_179, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_168])).
% 5.75/2.25  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.75/2.25  tff(c_58, plain, (![A_54]: (k6_relat_1(A_54)=k6_partfun1(A_54))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.75/2.25  tff(c_50, plain, (![A_41]: (m1_subset_1(k6_relat_1(A_41), k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.75/2.25  tff(c_83, plain, (![A_41]: (m1_subset_1(k6_partfun1(A_41), k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50])).
% 5.75/2.25  tff(c_128, plain, (![A_41]: (v1_relat_1(k6_partfun1(A_41)) | ~v1_relat_1(k2_zfmisc_1(A_41, A_41)))), inference(resolution, [status(thm)], [c_83, c_125])).
% 5.75/2.25  tff(c_137, plain, (![A_41]: (v1_relat_1(k6_partfun1(A_41)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_128])).
% 5.75/2.25  tff(c_18, plain, (![A_22]: (k1_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.75/2.25  tff(c_89, plain, (![A_22]: (k1_relat_1(k6_partfun1(A_22))=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_18])).
% 5.75/2.25  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.75/2.25  tff(c_134, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_125])).
% 5.75/2.25  tff(c_143, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_134])).
% 5.75/2.25  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.75/2.25  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.75/2.25  tff(c_2117, plain, (![B_180, A_181, D_179, E_178, C_183, F_182]: (m1_subset_1(k1_partfun1(A_181, B_180, C_183, D_179, E_178, F_182), k1_zfmisc_1(k2_zfmisc_1(A_181, D_179))) | ~m1_subset_1(F_182, k1_zfmisc_1(k2_zfmisc_1(C_183, D_179))) | ~v1_funct_1(F_182) | ~m1_subset_1(E_178, k1_zfmisc_1(k2_zfmisc_1(A_181, B_180))) | ~v1_funct_1(E_178))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.75/2.25  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.75/2.25  tff(c_1515, plain, (![D_145, C_146, A_147, B_148]: (D_145=C_146 | ~r2_relset_1(A_147, B_148, C_146, D_145) | ~m1_subset_1(D_145, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.75/2.25  tff(c_1523, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_1515])).
% 5.75/2.25  tff(c_1538, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_1523])).
% 5.75/2.25  tff(c_1566, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1538])).
% 5.75/2.25  tff(c_2130, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2117, c_1566])).
% 5.75/2.25  tff(c_2152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_2130])).
% 5.75/2.25  tff(c_2153, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1538])).
% 5.75/2.25  tff(c_2637, plain, (![E_206, B_203, F_201, C_205, A_204, D_202]: (k1_partfun1(A_204, B_203, C_205, D_202, E_206, F_201)=k5_relat_1(E_206, F_201) | ~m1_subset_1(F_201, k1_zfmisc_1(k2_zfmisc_1(C_205, D_202))) | ~v1_funct_1(F_201) | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_203))) | ~v1_funct_1(E_206))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.75/2.25  tff(c_2643, plain, (![A_204, B_203, E_206]: (k1_partfun1(A_204, B_203, '#skF_2', '#skF_1', E_206, '#skF_4')=k5_relat_1(E_206, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_203))) | ~v1_funct_1(E_206))), inference(resolution, [status(thm)], [c_72, c_2637])).
% 5.75/2.25  tff(c_3139, plain, (![A_223, B_224, E_225]: (k1_partfun1(A_223, B_224, '#skF_2', '#skF_1', E_225, '#skF_4')=k5_relat_1(E_225, '#skF_4') | ~m1_subset_1(E_225, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))) | ~v1_funct_1(E_225))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2643])).
% 5.75/2.25  tff(c_3148, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_3139])).
% 5.75/2.25  tff(c_3156, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2153, c_3148])).
% 5.75/2.25  tff(c_22, plain, (![A_23]: (k5_relat_1(k6_relat_1(k1_relat_1(A_23)), A_23)=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.75/2.25  tff(c_87, plain, (![A_23]: (k5_relat_1(k6_partfun1(k1_relat_1(A_23)), A_23)=A_23 | ~v1_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_22])).
% 5.75/2.25  tff(c_1261, plain, (![A_139, B_140, C_141]: (k5_relat_1(k5_relat_1(A_139, B_140), C_141)=k5_relat_1(A_139, k5_relat_1(B_140, C_141)) | ~v1_relat_1(C_141) | ~v1_relat_1(B_140) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.75/2.25  tff(c_1317, plain, (![A_23, C_141]: (k5_relat_1(k6_partfun1(k1_relat_1(A_23)), k5_relat_1(A_23, C_141))=k5_relat_1(A_23, C_141) | ~v1_relat_1(C_141) | ~v1_relat_1(A_23) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_23))) | ~v1_relat_1(A_23))), inference(superposition, [status(thm), theory('equality')], [c_87, c_1261])).
% 5.75/2.25  tff(c_1337, plain, (![A_23, C_141]: (k5_relat_1(k6_partfun1(k1_relat_1(A_23)), k5_relat_1(A_23, C_141))=k5_relat_1(A_23, C_141) | ~v1_relat_1(C_141) | ~v1_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_1317])).
% 5.75/2.25  tff(c_3163, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_1'))=k5_relat_1('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3156, c_1337])).
% 5.75/2.25  tff(c_3176, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_1'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_143, c_3156, c_3163])).
% 5.75/2.25  tff(c_12, plain, (![A_10, B_12]: (k10_relat_1(A_10, k1_relat_1(B_12))=k1_relat_1(k5_relat_1(A_10, B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.75/2.25  tff(c_20, plain, (![A_22]: (k2_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.75/2.25  tff(c_88, plain, (![A_22]: (k2_relat_1(k6_partfun1(A_22))=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_20])).
% 5.75/2.25  tff(c_24, plain, (![B_25, A_24]: (k5_relat_1(B_25, k6_relat_1(A_24))=B_25 | ~r1_tarski(k2_relat_1(B_25), A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.75/2.25  tff(c_472, plain, (![B_104, A_105]: (k5_relat_1(B_104, k6_partfun1(A_105))=B_104 | ~r1_tarski(k2_relat_1(B_104), A_105) | ~v1_relat_1(B_104))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_24])).
% 5.75/2.25  tff(c_482, plain, (![A_22, A_105]: (k5_relat_1(k6_partfun1(A_22), k6_partfun1(A_105))=k6_partfun1(A_22) | ~r1_tarski(A_22, A_105) | ~v1_relat_1(k6_partfun1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_472])).
% 5.75/2.25  tff(c_485, plain, (![A_22, A_105]: (k5_relat_1(k6_partfun1(A_22), k6_partfun1(A_105))=k6_partfun1(A_22) | ~r1_tarski(A_22, A_105))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_482])).
% 5.75/2.25  tff(c_566, plain, (![A_110, B_111]: (k10_relat_1(A_110, k1_relat_1(B_111))=k1_relat_1(k5_relat_1(A_110, B_111)) | ~v1_relat_1(B_111) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.75/2.25  tff(c_578, plain, (![A_110, A_22]: (k1_relat_1(k5_relat_1(A_110, k6_partfun1(A_22)))=k10_relat_1(A_110, A_22) | ~v1_relat_1(k6_partfun1(A_22)) | ~v1_relat_1(A_110))), inference(superposition, [status(thm), theory('equality')], [c_89, c_566])).
% 5.75/2.25  tff(c_583, plain, (![A_112, A_113]: (k1_relat_1(k5_relat_1(A_112, k6_partfun1(A_113)))=k10_relat_1(A_112, A_113) | ~v1_relat_1(A_112))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_578])).
% 5.75/2.25  tff(c_613, plain, (![A_22, A_105]: (k10_relat_1(k6_partfun1(A_22), A_105)=k1_relat_1(k6_partfun1(A_22)) | ~v1_relat_1(k6_partfun1(A_22)) | ~r1_tarski(A_22, A_105))), inference(superposition, [status(thm), theory('equality')], [c_485, c_583])).
% 5.75/2.25  tff(c_654, plain, (![A_115, A_116]: (k10_relat_1(k6_partfun1(A_115), A_116)=A_115 | ~r1_tarski(A_115, A_116))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_89, c_613])).
% 5.75/2.25  tff(c_675, plain, (![A_115, B_12]: (k1_relat_1(k5_relat_1(k6_partfun1(A_115), B_12))=A_115 | ~r1_tarski(A_115, k1_relat_1(B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(k6_partfun1(A_115)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_654])).
% 5.75/2.25  tff(c_687, plain, (![A_115, B_12]: (k1_relat_1(k5_relat_1(k6_partfun1(A_115), B_12))=A_115 | ~r1_tarski(A_115, k1_relat_1(B_12)) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_675])).
% 5.75/2.25  tff(c_3355, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(k6_partfun1('#skF_1'))) | ~v1_relat_1(k6_partfun1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3176, c_687])).
% 5.75/2.25  tff(c_3374, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_89, c_89, c_3355])).
% 5.75/2.25  tff(c_3407, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_3374])).
% 5.75/2.25  tff(c_3410, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_3407])).
% 5.75/2.25  tff(c_3414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_179, c_3410])).
% 5.75/2.25  tff(c_3415, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_3374])).
% 5.75/2.25  tff(c_66, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.75/2.25  tff(c_32, plain, (![A_29]: (k2_relat_1(k2_funct_1(A_29))=k1_relat_1(A_29) | ~v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.75/2.25  tff(c_28, plain, (![A_26]: (v1_relat_1(k2_funct_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.75/2.25  tff(c_178, plain, (![A_41]: (v4_relat_1(k6_partfun1(A_41), A_41))), inference(resolution, [status(thm)], [c_83, c_168])).
% 5.75/2.25  tff(c_189, plain, (![B_77, A_78]: (r1_tarski(k1_relat_1(B_77), A_78) | ~v4_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.75/2.25  tff(c_195, plain, (![A_22, A_78]: (r1_tarski(A_22, A_78) | ~v4_relat_1(k6_partfun1(A_22), A_78) | ~v1_relat_1(k6_partfun1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_189])).
% 5.75/2.25  tff(c_199, plain, (![A_79, A_80]: (r1_tarski(A_79, A_80) | ~v4_relat_1(k6_partfun1(A_79), A_80))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_195])).
% 5.75/2.25  tff(c_207, plain, (![A_41]: (r1_tarski(A_41, A_41))), inference(resolution, [status(thm)], [c_178, c_199])).
% 5.75/2.25  tff(c_70, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.75/2.25  tff(c_688, plain, (![A_117, B_118, C_119]: (k2_relset_1(A_117, B_118, C_119)=k2_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.75/2.25  tff(c_694, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_688])).
% 5.75/2.25  tff(c_701, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_694])).
% 5.75/2.25  tff(c_483, plain, (![B_104]: (k5_relat_1(B_104, k6_partfun1(k2_relat_1(B_104)))=B_104 | ~v1_relat_1(B_104))), inference(resolution, [status(thm)], [c_207, c_472])).
% 5.75/2.25  tff(c_616, plain, (![B_104]: (k10_relat_1(B_104, k2_relat_1(B_104))=k1_relat_1(B_104) | ~v1_relat_1(B_104) | ~v1_relat_1(B_104))), inference(superposition, [status(thm), theory('equality')], [c_483, c_583])).
% 5.75/2.25  tff(c_996, plain, (![B_128, A_129]: (k9_relat_1(B_128, k10_relat_1(B_128, A_129))=A_129 | ~r1_tarski(A_129, k2_relat_1(B_128)) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.75/2.25  tff(c_998, plain, (![A_129]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_129))=A_129 | ~r1_tarski(A_129, '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_701, c_996])).
% 5.75/2.25  tff(c_1017, plain, (![A_130]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_130))=A_130 | ~r1_tarski(A_130, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_82, c_998])).
% 5.75/2.25  tff(c_1027, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_616, c_1017])).
% 5.75/2.25  tff(c_1038, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_140, c_207, c_701, c_701, c_1027])).
% 5.75/2.25  tff(c_38, plain, (![A_30]: (k5_relat_1(A_30, k2_funct_1(A_30))=k6_relat_1(k1_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.75/2.25  tff(c_84, plain, (![A_30]: (k5_relat_1(A_30, k2_funct_1(A_30))=k6_partfun1(k1_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_38])).
% 5.75/2.25  tff(c_1034, plain, (![B_12]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_12)))=k1_relat_1(B_12) | ~r1_tarski(k1_relat_1(B_12), '#skF_2') | ~v1_relat_1(B_12) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1017])).
% 5.75/2.25  tff(c_1190, plain, (![B_137]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_137)))=k1_relat_1(B_137) | ~r1_tarski(k1_relat_1(B_137), '#skF_2') | ~v1_relat_1(B_137))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_1034])).
% 5.75/2.25  tff(c_1200, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))))=k1_relat_1(k2_funct_1('#skF_3')) | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_84, c_1190])).
% 5.75/2.25  tff(c_1218, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_82, c_66, c_1038, c_89, c_1200])).
% 5.75/2.25  tff(c_1239, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1218])).
% 5.75/2.25  tff(c_1242, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_1239])).
% 5.75/2.25  tff(c_1246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_82, c_1242])).
% 5.75/2.25  tff(c_1248, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1218])).
% 5.75/2.25  tff(c_34, plain, (![A_29]: (k1_relat_1(k2_funct_1(A_29))=k2_relat_1(A_29) | ~v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.75/2.25  tff(c_1247, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_1218])).
% 5.75/2.25  tff(c_1249, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_1247])).
% 5.75/2.25  tff(c_1252, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_1249])).
% 5.75/2.25  tff(c_1258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_82, c_66, c_207, c_701, c_1252])).
% 5.75/2.25  tff(c_1259, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_1247])).
% 5.75/2.25  tff(c_1365, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1259, c_87])).
% 5.75/2.25  tff(c_1388, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1248, c_1365])).
% 5.75/2.25  tff(c_16, plain, (![A_15, B_19, C_21]: (k5_relat_1(k5_relat_1(A_15, B_19), C_21)=k5_relat_1(A_15, k5_relat_1(B_19, C_21)) | ~v1_relat_1(C_21) | ~v1_relat_1(B_19) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.75/2.25  tff(c_1547, plain, (![C_21]: (k5_relat_1(k6_partfun1('#skF_2'), k5_relat_1(k2_funct_1('#skF_3'), C_21))=k5_relat_1(k2_funct_1('#skF_3'), C_21) | ~v1_relat_1(C_21) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k6_partfun1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1388, c_16])).
% 5.75/2.25  tff(c_2460, plain, (![C_197]: (k5_relat_1(k6_partfun1('#skF_2'), k5_relat_1(k2_funct_1('#skF_3'), C_197))=k5_relat_1(k2_funct_1('#skF_3'), C_197) | ~v1_relat_1(C_197))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_1248, c_1547])).
% 5.75/2.25  tff(c_2490, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3')) | ~v1_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_483, c_2460])).
% 5.75/2.25  tff(c_2502, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1248, c_137, c_1388, c_2490])).
% 5.75/2.25  tff(c_2543, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_2502])).
% 5.75/2.25  tff(c_2559, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_82, c_66, c_2543])).
% 5.75/2.25  tff(c_3420, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3415, c_2559])).
% 5.75/2.25  tff(c_180, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_168])).
% 5.75/2.25  tff(c_241, plain, (![B_87, A_88]: (k7_relat_1(B_87, A_88)=B_87 | ~v4_relat_1(B_87, A_88) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.75/2.25  tff(c_256, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_179, c_241])).
% 5.75/2.25  tff(c_269, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_256])).
% 5.75/2.25  tff(c_301, plain, (![B_91, A_92]: (k2_relat_1(k7_relat_1(B_91, A_92))=k9_relat_1(B_91, A_92) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.75/2.25  tff(c_316, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_269, c_301])).
% 5.75/2.25  tff(c_325, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_316])).
% 5.75/2.25  tff(c_703, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_701, c_325])).
% 5.75/2.25  tff(c_1042, plain, (![B_12]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_12)))=k1_relat_1(B_12) | ~r1_tarski(k1_relat_1(B_12), '#skF_2') | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_1034])).
% 5.75/2.25  tff(c_3172, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1')))=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3156, c_1042])).
% 5.75/2.25  tff(c_3182, plain, (k1_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_703, c_89, c_3172])).
% 5.75/2.25  tff(c_3184, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_3182])).
% 5.75/2.25  tff(c_3187, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_3184])).
% 5.75/2.25  tff(c_3191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_180, c_3187])).
% 5.75/2.25  tff(c_3192, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_3182])).
% 5.75/2.25  tff(c_3227, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3192, c_87])).
% 5.75/2.25  tff(c_3251, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_3227])).
% 5.75/2.25  tff(c_145, plain, (![A_67]: (k5_relat_1(k6_partfun1(k1_relat_1(A_67)), A_67)=A_67 | ~v1_relat_1(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_22])).
% 5.75/2.25  tff(c_154, plain, (![A_22]: (k5_relat_1(k6_partfun1(A_22), k6_partfun1(A_22))=k6_partfun1(A_22) | ~v1_relat_1(k6_partfun1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_145])).
% 5.75/2.25  tff(c_158, plain, (![A_22]: (k5_relat_1(k6_partfun1(A_22), k6_partfun1(A_22))=k6_partfun1(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_154])).
% 5.75/2.25  tff(c_36, plain, (![A_30]: (k5_relat_1(k2_funct_1(A_30), A_30)=k6_relat_1(k2_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.75/2.25  tff(c_85, plain, (![A_30]: (k5_relat_1(k2_funct_1(A_30), A_30)=k6_partfun1(k2_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_36])).
% 5.75/2.25  tff(c_2486, plain, (k5_relat_1(k6_partfun1('#skF_2'), k6_partfun1(k2_relat_1('#skF_3')))=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_85, c_2460])).
% 5.75/2.25  tff(c_2500, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_82, c_66, c_140, c_158, c_701, c_2486])).
% 5.75/2.25  tff(c_2509, plain, (![C_21]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_21))=k5_relat_1(k6_partfun1('#skF_2'), C_21) | ~v1_relat_1(C_21) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2500, c_16])).
% 5.75/2.25  tff(c_2521, plain, (![C_21]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_21))=k5_relat_1(k6_partfun1('#skF_2'), C_21) | ~v1_relat_1(C_21))), inference(demodulation, [status(thm), theory('equality')], [c_1248, c_140, c_2509])).
% 5.75/2.25  tff(c_3166, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3156, c_2521])).
% 5.75/2.25  tff(c_3178, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_3166])).
% 5.75/2.25  tff(c_4733, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3420, c_3251, c_3178])).
% 5.75/2.25  tff(c_4734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_4733])).
% 5.75/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.75/2.25  
% 5.75/2.25  Inference rules
% 5.75/2.25  ----------------------
% 5.75/2.25  #Ref     : 0
% 5.75/2.25  #Sup     : 1013
% 5.75/2.25  #Fact    : 0
% 5.75/2.25  #Define  : 0
% 5.75/2.25  #Split   : 6
% 5.75/2.25  #Chain   : 0
% 5.75/2.25  #Close   : 0
% 5.75/2.25  
% 5.75/2.25  Ordering : KBO
% 5.75/2.25  
% 5.75/2.25  Simplification rules
% 5.75/2.25  ----------------------
% 5.75/2.25  #Subsume      : 37
% 5.75/2.25  #Demod        : 1394
% 5.75/2.25  #Tautology    : 509
% 5.75/2.25  #SimpNegUnit  : 1
% 5.75/2.25  #BackRed      : 14
% 5.75/2.25  
% 5.75/2.25  #Partial instantiations: 0
% 5.75/2.25  #Strategies tried      : 1
% 5.75/2.25  
% 5.75/2.25  Timing (in seconds)
% 5.75/2.25  ----------------------
% 6.13/2.25  Preprocessing        : 0.36
% 6.13/2.25  Parsing              : 0.19
% 6.13/2.25  CNF conversion       : 0.03
% 6.13/2.25  Main loop            : 0.99
% 6.13/2.25  Inferencing          : 0.35
% 6.13/2.25  Reduction            : 0.37
% 6.13/2.25  Demodulation         : 0.28
% 6.13/2.25  BG Simplification    : 0.04
% 6.13/2.25  Subsumption          : 0.16
% 6.13/2.25  Abstraction          : 0.04
% 6.13/2.25  MUC search           : 0.00
% 6.13/2.25  Cooper               : 0.00
% 6.13/2.25  Total                : 1.41
% 6.13/2.25  Index Insertion      : 0.00
% 6.13/2.25  Index Deletion       : 0.00
% 6.13/2.25  Index Matching       : 0.00
% 6.13/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
