%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:29 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 121 expanded)
%              Number of leaves         :   31 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  125 ( 358 expanded)
%              Number of equality atoms :   14 (  41 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( B != k1_xboole_0
            & ? [D] :
                ( v1_funct_1(D)
                & v1_funct_2(D,B,A)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A)) )
            & ~ v2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_2)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_81,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_79,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_67,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_103,axiom,(
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

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_78,plain,(
    ! [A_34] :
      ( v2_funct_1(A_34)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_36,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_81,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_36])).

tff(c_84,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_81])).

tff(c_85,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_86,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_xboole_0(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_92,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_86])).

tff(c_99,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_92])).

tff(c_50,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_42,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_30,plain,(
    ! [A_20] : k6_relat_1(A_20) = k6_partfun1(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16,plain,(
    ! [A_4] : v2_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_54,plain,(
    ! [A_4] : v2_funct_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_16])).

tff(c_163,plain,(
    ! [D_56,E_54,A_59,C_57,B_58,F_55] :
      ( m1_subset_1(k1_partfun1(A_59,B_58,C_57,D_56,E_54,F_55),k1_zfmisc_1(k2_zfmisc_1(A_59,D_56)))
      | ~ m1_subset_1(F_55,k1_zfmisc_1(k2_zfmisc_1(C_57,D_56)))
      | ~ v1_funct_1(F_55)
      | ~ m1_subset_1(E_54,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58)))
      | ~ v1_funct_1(E_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    ! [A_13] : m1_subset_1(k6_relat_1(A_13),k1_zfmisc_1(k2_zfmisc_1(A_13,A_13))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_53,plain,(
    ! [A_13] : m1_subset_1(k6_partfun1(A_13),k1_zfmisc_1(k2_zfmisc_1(A_13,A_13))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24])).

tff(c_38,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_122,plain,(
    ! [D_42,C_43,A_44,B_45] :
      ( D_42 = C_43
      | ~ r2_relset_1(A_44,B_45,C_43,D_42)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_128,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_38,c_122])).

tff(c_139,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_128])).

tff(c_148,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_168,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_163,c_148])).

tff(c_178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_44,c_40,c_168])).

tff(c_179,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_427,plain,(
    ! [E_127,C_128,B_129,D_126,A_125] :
      ( k1_xboole_0 = C_128
      | v2_funct_1(D_126)
      | ~ v2_funct_1(k1_partfun1(A_125,B_129,B_129,C_128,D_126,E_127))
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(B_129,C_128)))
      | ~ v1_funct_2(E_127,B_129,C_128)
      | ~ v1_funct_1(E_127)
      | ~ m1_subset_1(D_126,k1_zfmisc_1(k2_zfmisc_1(A_125,B_129)))
      | ~ v1_funct_2(D_126,A_125,B_129)
      | ~ v1_funct_1(D_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_429,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_427])).

tff(c_434,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_44,c_42,c_40,c_54,c_429])).

tff(c_435,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_434])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_441,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_2])).

tff(c_444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_441])).

tff(c_445,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_446,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_452,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_446,c_4])).

tff(c_458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_445,c_452])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:56:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.38  
% 2.66/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.39  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.66/1.39  
% 2.66/1.39  %Foreground sorts:
% 2.66/1.39  
% 2.66/1.39  
% 2.66/1.39  %Background operators:
% 2.66/1.39  
% 2.66/1.39  
% 2.66/1.39  %Foreground operators:
% 2.66/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.66/1.39  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.66/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.39  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.66/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.39  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.66/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.66/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.39  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.66/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.66/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.39  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.66/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.66/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.39  
% 2.92/1.40  tff(f_126, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((~(B = k1_xboole_0) & (?[D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))))) & ~v2_funct_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_funct_2)).
% 2.92/1.40  tff(f_46, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_1)).
% 2.92/1.40  tff(f_57, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 2.92/1.40  tff(f_81, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.92/1.40  tff(f_50, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.92/1.40  tff(f_79, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 2.92/1.40  tff(f_67, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 2.92/1.40  tff(f_65, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.92/1.40  tff(f_103, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 2.92/1.40  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.92/1.40  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.92/1.40  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.92/1.40  tff(c_78, plain, (![A_34]: (v2_funct_1(A_34) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.92/1.40  tff(c_36, plain, (~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.92/1.40  tff(c_81, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_36])).
% 2.92/1.40  tff(c_84, plain, (~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_81])).
% 2.92/1.40  tff(c_85, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_84])).
% 2.92/1.40  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.92/1.40  tff(c_86, plain, (![C_35, A_36, B_37]: (v1_xboole_0(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.92/1.40  tff(c_92, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_86])).
% 2.92/1.40  tff(c_99, plain, (~v1_xboole_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_85, c_92])).
% 2.92/1.40  tff(c_50, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.92/1.40  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.92/1.40  tff(c_42, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.92/1.40  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.92/1.40  tff(c_30, plain, (![A_20]: (k6_relat_1(A_20)=k6_partfun1(A_20))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.92/1.40  tff(c_16, plain, (![A_4]: (v2_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.92/1.40  tff(c_54, plain, (![A_4]: (v2_funct_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_16])).
% 2.92/1.40  tff(c_163, plain, (![D_56, E_54, A_59, C_57, B_58, F_55]: (m1_subset_1(k1_partfun1(A_59, B_58, C_57, D_56, E_54, F_55), k1_zfmisc_1(k2_zfmisc_1(A_59, D_56))) | ~m1_subset_1(F_55, k1_zfmisc_1(k2_zfmisc_1(C_57, D_56))) | ~v1_funct_1(F_55) | ~m1_subset_1(E_54, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))) | ~v1_funct_1(E_54))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.92/1.40  tff(c_24, plain, (![A_13]: (m1_subset_1(k6_relat_1(A_13), k1_zfmisc_1(k2_zfmisc_1(A_13, A_13))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.92/1.40  tff(c_53, plain, (![A_13]: (m1_subset_1(k6_partfun1(A_13), k1_zfmisc_1(k2_zfmisc_1(A_13, A_13))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24])).
% 2.92/1.40  tff(c_38, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.92/1.40  tff(c_122, plain, (![D_42, C_43, A_44, B_45]: (D_42=C_43 | ~r2_relset_1(A_44, B_45, C_43, D_42) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.92/1.40  tff(c_128, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_38, c_122])).
% 2.92/1.40  tff(c_139, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_128])).
% 2.92/1.40  tff(c_148, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_139])).
% 2.92/1.40  tff(c_168, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_163, c_148])).
% 2.92/1.40  tff(c_178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_44, c_40, c_168])).
% 2.92/1.40  tff(c_179, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_139])).
% 2.92/1.40  tff(c_427, plain, (![E_127, C_128, B_129, D_126, A_125]: (k1_xboole_0=C_128 | v2_funct_1(D_126) | ~v2_funct_1(k1_partfun1(A_125, B_129, B_129, C_128, D_126, E_127)) | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(B_129, C_128))) | ~v1_funct_2(E_127, B_129, C_128) | ~v1_funct_1(E_127) | ~m1_subset_1(D_126, k1_zfmisc_1(k2_zfmisc_1(A_125, B_129))) | ~v1_funct_2(D_126, A_125, B_129) | ~v1_funct_1(D_126))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.92/1.40  tff(c_429, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_179, c_427])).
% 2.92/1.40  tff(c_434, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_44, c_42, c_40, c_54, c_429])).
% 2.92/1.40  tff(c_435, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_36, c_434])).
% 2.92/1.40  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.92/1.40  tff(c_441, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_435, c_2])).
% 2.92/1.40  tff(c_444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_441])).
% 2.92/1.40  tff(c_445, plain, (~v1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_84])).
% 2.92/1.40  tff(c_446, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_84])).
% 2.92/1.40  tff(c_4, plain, (![A_1]: (v1_relat_1(A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.92/1.40  tff(c_452, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_446, c_4])).
% 2.92/1.40  tff(c_458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_445, c_452])).
% 2.92/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.40  
% 2.92/1.40  Inference rules
% 2.92/1.40  ----------------------
% 2.92/1.40  #Ref     : 0
% 2.92/1.40  #Sup     : 80
% 2.92/1.40  #Fact    : 0
% 2.92/1.40  #Define  : 0
% 2.92/1.40  #Split   : 3
% 2.92/1.40  #Chain   : 0
% 2.92/1.40  #Close   : 0
% 2.92/1.40  
% 2.92/1.40  Ordering : KBO
% 2.92/1.40  
% 2.92/1.40  Simplification rules
% 2.92/1.40  ----------------------
% 2.92/1.40  #Subsume      : 9
% 2.92/1.40  #Demod        : 67
% 2.92/1.40  #Tautology    : 14
% 2.92/1.40  #SimpNegUnit  : 4
% 2.92/1.40  #BackRed      : 7
% 2.92/1.40  
% 2.92/1.40  #Partial instantiations: 0
% 2.92/1.40  #Strategies tried      : 1
% 2.92/1.40  
% 2.92/1.40  Timing (in seconds)
% 2.92/1.40  ----------------------
% 2.92/1.40  Preprocessing        : 0.32
% 2.92/1.41  Parsing              : 0.17
% 2.92/1.41  CNF conversion       : 0.02
% 2.92/1.41  Main loop            : 0.32
% 2.92/1.41  Inferencing          : 0.12
% 2.92/1.41  Reduction            : 0.10
% 2.92/1.41  Demodulation         : 0.07
% 2.92/1.41  BG Simplification    : 0.02
% 2.92/1.41  Subsumption          : 0.06
% 2.92/1.41  Abstraction          : 0.01
% 2.92/1.41  MUC search           : 0.00
% 2.92/1.41  Cooper               : 0.00
% 2.92/1.41  Total                : 0.67
% 2.92/1.41  Index Insertion      : 0.00
% 2.92/1.41  Index Deletion       : 0.00
% 2.92/1.41  Index Matching       : 0.00
% 2.92/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
