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
% DateTime   : Thu Dec  3 10:13:28 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 116 expanded)
%              Number of leaves         :   32 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  125 ( 354 expanded)
%              Number of equality atoms :   14 (  37 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_128,negated_conjecture,(
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

tff(f_83,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_77,axiom,(
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
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_105,axiom,(
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

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_80,plain,(
    ! [A_35] :
      ( v2_funct_1(A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35)
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_38,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_83,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_38])).

tff(c_86,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_83])).

tff(c_87,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_88,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_xboole_0(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38)))
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_97,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_88])).

tff(c_102,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_97])).

tff(c_52,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_32,plain,(
    ! [A_20] : k6_relat_1(A_20) = k6_partfun1(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_16,plain,(
    ! [A_4] : v2_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_55,plain,(
    ! [A_4] : v2_funct_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_16])).

tff(c_215,plain,(
    ! [F_67,E_70,C_72,D_68,B_69,A_71] :
      ( m1_subset_1(k1_partfun1(A_71,B_69,C_72,D_68,E_70,F_67),k1_zfmisc_1(k2_zfmisc_1(A_71,D_68)))
      | ~ m1_subset_1(F_67,k1_zfmisc_1(k2_zfmisc_1(C_72,D_68)))
      | ~ v1_funct_1(F_67)
      | ~ m1_subset_1(E_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_69)))
      | ~ v1_funct_1(E_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    ! [A_19] : m1_subset_1(k6_partfun1(A_19),k1_zfmisc_1(k2_zfmisc_1(A_19,A_19))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_114,plain,(
    ! [D_42,C_43,A_44,B_45] :
      ( D_42 = C_43
      | ~ r2_relset_1(A_44,B_45,C_43,D_42)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_120,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_40,c_114])).

tff(c_131,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_120])).

tff(c_150,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_228,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_215,c_150])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_46,c_42,c_228])).

tff(c_242,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_490,plain,(
    ! [E_140,A_138,C_141,B_142,D_139] :
      ( k1_xboole_0 = C_141
      | v2_funct_1(D_139)
      | ~ v2_funct_1(k1_partfun1(A_138,B_142,B_142,C_141,D_139,E_140))
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(B_142,C_141)))
      | ~ v1_funct_2(E_140,B_142,C_141)
      | ~ v1_funct_1(E_140)
      | ~ m1_subset_1(D_139,k1_zfmisc_1(k2_zfmisc_1(A_138,B_142)))
      | ~ v1_funct_2(D_139,A_138,B_142)
      | ~ v1_funct_1(D_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_492,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_490])).

tff(c_497,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_46,c_44,c_42,c_55,c_492])).

tff(c_498,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_497])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_504,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_2])).

tff(c_507,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_504])).

tff(c_508,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_509,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_515,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_509,c_4])).

tff(c_521,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_508,c_515])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:25:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.47  
% 3.11/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.47  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.11/1.47  
% 3.11/1.47  %Foreground sorts:
% 3.11/1.47  
% 3.11/1.47  
% 3.11/1.47  %Background operators:
% 3.11/1.47  
% 3.11/1.47  
% 3.11/1.47  %Foreground operators:
% 3.11/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.11/1.47  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.47  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.11/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.47  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.11/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.47  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.11/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.11/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.47  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.11/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.11/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.11/1.47  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.11/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.47  
% 3.11/1.48  tff(f_128, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((~(B = k1_xboole_0) & (?[D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))))) & ~v2_funct_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_funct_2)).
% 3.11/1.48  tff(f_46, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_1)).
% 3.11/1.48  tff(f_57, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 3.11/1.48  tff(f_83, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.11/1.48  tff(f_50, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.11/1.48  tff(f_77, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.11/1.48  tff(f_81, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.11/1.48  tff(f_65, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.11/1.48  tff(f_105, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 3.11/1.48  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.11/1.48  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.11/1.48  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.11/1.48  tff(c_80, plain, (![A_35]: (v2_funct_1(A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35) | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.11/1.48  tff(c_38, plain, (~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.11/1.48  tff(c_83, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_80, c_38])).
% 3.11/1.48  tff(c_86, plain, (~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_83])).
% 3.11/1.48  tff(c_87, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_86])).
% 3.11/1.48  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.11/1.48  tff(c_88, plain, (![C_36, A_37, B_38]: (v1_xboole_0(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.11/1.48  tff(c_97, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_88])).
% 3.11/1.48  tff(c_102, plain, (~v1_xboole_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_87, c_97])).
% 3.11/1.48  tff(c_52, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.11/1.48  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.11/1.48  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.11/1.48  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.11/1.48  tff(c_32, plain, (![A_20]: (k6_relat_1(A_20)=k6_partfun1(A_20))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.11/1.48  tff(c_16, plain, (![A_4]: (v2_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.11/1.48  tff(c_55, plain, (![A_4]: (v2_funct_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_16])).
% 3.11/1.48  tff(c_215, plain, (![F_67, E_70, C_72, D_68, B_69, A_71]: (m1_subset_1(k1_partfun1(A_71, B_69, C_72, D_68, E_70, F_67), k1_zfmisc_1(k2_zfmisc_1(A_71, D_68))) | ~m1_subset_1(F_67, k1_zfmisc_1(k2_zfmisc_1(C_72, D_68))) | ~v1_funct_1(F_67) | ~m1_subset_1(E_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_69))) | ~v1_funct_1(E_70))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.11/1.48  tff(c_30, plain, (![A_19]: (m1_subset_1(k6_partfun1(A_19), k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.11/1.48  tff(c_40, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.11/1.48  tff(c_114, plain, (![D_42, C_43, A_44, B_45]: (D_42=C_43 | ~r2_relset_1(A_44, B_45, C_43, D_42) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.11/1.48  tff(c_120, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_40, c_114])).
% 3.11/1.48  tff(c_131, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_120])).
% 3.11/1.48  tff(c_150, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_131])).
% 3.11/1.48  tff(c_228, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_215, c_150])).
% 3.11/1.48  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_46, c_42, c_228])).
% 3.11/1.48  tff(c_242, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_131])).
% 3.11/1.48  tff(c_490, plain, (![E_140, A_138, C_141, B_142, D_139]: (k1_xboole_0=C_141 | v2_funct_1(D_139) | ~v2_funct_1(k1_partfun1(A_138, B_142, B_142, C_141, D_139, E_140)) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(B_142, C_141))) | ~v1_funct_2(E_140, B_142, C_141) | ~v1_funct_1(E_140) | ~m1_subset_1(D_139, k1_zfmisc_1(k2_zfmisc_1(A_138, B_142))) | ~v1_funct_2(D_139, A_138, B_142) | ~v1_funct_1(D_139))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.11/1.48  tff(c_492, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_242, c_490])).
% 3.11/1.48  tff(c_497, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_46, c_44, c_42, c_55, c_492])).
% 3.11/1.48  tff(c_498, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_38, c_497])).
% 3.11/1.48  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.11/1.48  tff(c_504, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_498, c_2])).
% 3.11/1.48  tff(c_507, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_504])).
% 3.11/1.48  tff(c_508, plain, (~v1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_86])).
% 3.11/1.48  tff(c_509, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_86])).
% 3.11/1.48  tff(c_4, plain, (![A_1]: (v1_relat_1(A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.11/1.48  tff(c_515, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_509, c_4])).
% 3.11/1.48  tff(c_521, plain, $false, inference(negUnitSimplification, [status(thm)], [c_508, c_515])).
% 3.11/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.48  
% 3.11/1.48  Inference rules
% 3.11/1.48  ----------------------
% 3.11/1.48  #Ref     : 0
% 3.11/1.48  #Sup     : 92
% 3.11/1.48  #Fact    : 0
% 3.11/1.48  #Define  : 0
% 3.11/1.48  #Split   : 3
% 3.11/1.48  #Chain   : 0
% 3.11/1.48  #Close   : 0
% 3.11/1.48  
% 3.11/1.48  Ordering : KBO
% 3.11/1.48  
% 3.11/1.48  Simplification rules
% 3.11/1.48  ----------------------
% 3.11/1.48  #Subsume      : 9
% 3.11/1.48  #Demod        : 74
% 3.11/1.48  #Tautology    : 14
% 3.11/1.48  #SimpNegUnit  : 4
% 3.11/1.48  #BackRed      : 7
% 3.11/1.48  
% 3.11/1.48  #Partial instantiations: 0
% 3.11/1.48  #Strategies tried      : 1
% 3.11/1.48  
% 3.11/1.48  Timing (in seconds)
% 3.11/1.48  ----------------------
% 3.11/1.49  Preprocessing        : 0.33
% 3.11/1.49  Parsing              : 0.18
% 3.11/1.49  CNF conversion       : 0.02
% 3.11/1.49  Main loop            : 0.34
% 3.11/1.49  Inferencing          : 0.13
% 3.11/1.49  Reduction            : 0.11
% 3.11/1.49  Demodulation         : 0.08
% 3.11/1.49  BG Simplification    : 0.02
% 3.11/1.49  Subsumption          : 0.06
% 3.11/1.49  Abstraction          : 0.01
% 3.11/1.49  MUC search           : 0.00
% 3.11/1.49  Cooper               : 0.00
% 3.11/1.49  Total                : 0.70
% 3.11/1.49  Index Insertion      : 0.00
% 3.11/1.49  Index Deletion       : 0.00
% 3.11/1.49  Index Matching       : 0.00
% 3.11/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
