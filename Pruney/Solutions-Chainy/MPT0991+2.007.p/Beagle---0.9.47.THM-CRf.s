%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:27 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 119 expanded)
%              Number of leaves         :   37 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  136 ( 332 expanded)
%              Number of equality atoms :   14 (  35 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_141,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_2)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_96,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_70,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_90,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_118,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( v1_xboole_0(k2_zfmisc_1(A_5,B_6))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_87,plain,(
    ! [B_47,A_48] :
      ( v1_xboole_0(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_99,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_87])).

tff(c_105,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_117,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_105])).

tff(c_42,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_56,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_48,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36,plain,(
    ! [A_25] : k6_relat_1(A_25) = k6_partfun1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_22,plain,(
    ! [A_13] : v2_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_59,plain,(
    ! [A_13] : v2_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_22])).

tff(c_240,plain,(
    ! [C_80,B_84,E_81,F_82,D_83,A_79] :
      ( m1_subset_1(k1_partfun1(A_79,B_84,C_80,D_83,E_81,F_82),k1_zfmisc_1(k2_zfmisc_1(A_79,D_83)))
      | ~ m1_subset_1(F_82,k1_zfmisc_1(k2_zfmisc_1(C_80,D_83)))
      | ~ v1_funct_1(F_82)
      | ~ m1_subset_1(E_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_84)))
      | ~ v1_funct_1(E_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_44,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_165,plain,(
    ! [D_61,C_62,A_63,B_64] :
      ( D_61 = C_62
      | ~ r2_relset_1(A_63,B_64,C_62,D_61)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64)))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_173,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_44,c_165])).

tff(c_188,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_173])).

tff(c_189,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_249,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_240,c_189])).

tff(c_262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_50,c_46,c_249])).

tff(c_263,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_490,plain,(
    ! [B_140,E_143,A_141,D_139,C_142] :
      ( k1_xboole_0 = C_142
      | v2_funct_1(D_139)
      | ~ v2_funct_1(k1_partfun1(A_141,B_140,B_140,C_142,D_139,E_143))
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(B_140,C_142)))
      | ~ v1_funct_2(E_143,B_140,C_142)
      | ~ v1_funct_1(E_143)
      | ~ m1_subset_1(D_139,k1_zfmisc_1(k2_zfmisc_1(A_141,B_140)))
      | ~ v1_funct_2(D_139,A_141,B_140)
      | ~ v1_funct_1(D_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

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
    inference(superposition,[status(thm),theory(equality)],[c_263,c_490])).

tff(c_497,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_50,c_48,c_46,c_59,c_492])).

tff(c_498,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_497])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_135,plain,(
    ! [B_54,A_55] :
      ( ~ r1_xboole_0(B_54,A_55)
      | ~ r1_tarski(B_54,A_55)
      | v1_xboole_0(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_150,plain,(
    ! [A_59] :
      ( ~ r1_tarski(A_59,k1_xboole_0)
      | v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_4,c_135])).

tff(c_155,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_150])).

tff(c_504,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_155])).

tff(c_510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_504])).

tff(c_511,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_12,plain,(
    ! [A_10] :
      ( v1_relat_1(A_10)
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_521,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_511,c_12])).

tff(c_565,plain,(
    ! [A_150] :
      ( v2_funct_1(A_150)
      | ~ v1_funct_1(A_150)
      | ~ v1_relat_1(A_150)
      | ~ v1_xboole_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_568,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_565,c_42])).

tff(c_572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_521,c_58,c_568])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:12:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.44  
% 2.95/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.44  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.95/1.44  
% 2.95/1.44  %Foreground sorts:
% 2.95/1.44  
% 2.95/1.44  
% 2.95/1.44  %Background operators:
% 2.95/1.44  
% 2.95/1.44  
% 2.95/1.44  %Foreground operators:
% 2.95/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.95/1.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.95/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.44  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.95/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.44  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.95/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.95/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.95/1.44  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.95/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.95/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.44  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.95/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.95/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.95/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.95/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.95/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.44  
% 3.25/1.46  tff(f_41, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 3.25/1.46  tff(f_141, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((~(B = k1_xboole_0) & (?[D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))))) & ~v2_funct_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_funct_2)).
% 3.25/1.46  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.25/1.46  tff(f_96, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.25/1.46  tff(f_70, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 3.25/1.46  tff(f_90, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.25/1.46  tff(f_94, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.25/1.46  tff(f_78, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.25/1.46  tff(f_118, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 3.25/1.46  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.25/1.46  tff(f_29, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.25/1.46  tff(f_37, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.25/1.46  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.25/1.46  tff(f_68, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_1)).
% 3.25/1.46  tff(c_8, plain, (![A_5, B_6]: (v1_xboole_0(k2_zfmisc_1(A_5, B_6)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.25/1.46  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.25/1.46  tff(c_87, plain, (![B_47, A_48]: (v1_xboole_0(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.25/1.46  tff(c_99, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_87])).
% 3.25/1.46  tff(c_105, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_99])).
% 3.25/1.46  tff(c_117, plain, (~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_8, c_105])).
% 3.25/1.46  tff(c_42, plain, (~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.25/1.46  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.25/1.46  tff(c_56, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.25/1.46  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.25/1.46  tff(c_48, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.25/1.46  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.25/1.46  tff(c_36, plain, (![A_25]: (k6_relat_1(A_25)=k6_partfun1(A_25))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.25/1.46  tff(c_22, plain, (![A_13]: (v2_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.25/1.46  tff(c_59, plain, (![A_13]: (v2_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_22])).
% 3.25/1.46  tff(c_240, plain, (![C_80, B_84, E_81, F_82, D_83, A_79]: (m1_subset_1(k1_partfun1(A_79, B_84, C_80, D_83, E_81, F_82), k1_zfmisc_1(k2_zfmisc_1(A_79, D_83))) | ~m1_subset_1(F_82, k1_zfmisc_1(k2_zfmisc_1(C_80, D_83))) | ~v1_funct_1(F_82) | ~m1_subset_1(E_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_84))) | ~v1_funct_1(E_81))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.25/1.46  tff(c_34, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.25/1.46  tff(c_44, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.25/1.46  tff(c_165, plain, (![D_61, C_62, A_63, B_64]: (D_61=C_62 | ~r2_relset_1(A_63, B_64, C_62, D_61) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.25/1.46  tff(c_173, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_44, c_165])).
% 3.25/1.46  tff(c_188, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_173])).
% 3.25/1.46  tff(c_189, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_188])).
% 3.25/1.46  tff(c_249, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_240, c_189])).
% 3.25/1.46  tff(c_262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_50, c_46, c_249])).
% 3.25/1.46  tff(c_263, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_188])).
% 3.25/1.46  tff(c_490, plain, (![B_140, E_143, A_141, D_139, C_142]: (k1_xboole_0=C_142 | v2_funct_1(D_139) | ~v2_funct_1(k1_partfun1(A_141, B_140, B_140, C_142, D_139, E_143)) | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(B_140, C_142))) | ~v1_funct_2(E_143, B_140, C_142) | ~v1_funct_1(E_143) | ~m1_subset_1(D_139, k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))) | ~v1_funct_2(D_139, A_141, B_140) | ~v1_funct_1(D_139))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.25/1.46  tff(c_492, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_263, c_490])).
% 3.25/1.46  tff(c_497, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_50, c_48, c_46, c_59, c_492])).
% 3.25/1.46  tff(c_498, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_42, c_497])).
% 3.25/1.46  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.25/1.46  tff(c_4, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.25/1.46  tff(c_135, plain, (![B_54, A_55]: (~r1_xboole_0(B_54, A_55) | ~r1_tarski(B_54, A_55) | v1_xboole_0(B_54))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.25/1.46  tff(c_150, plain, (![A_59]: (~r1_tarski(A_59, k1_xboole_0) | v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_4, c_135])).
% 3.25/1.46  tff(c_155, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_150])).
% 3.25/1.46  tff(c_504, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_498, c_155])).
% 3.25/1.46  tff(c_510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_504])).
% 3.25/1.46  tff(c_511, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_99])).
% 3.25/1.46  tff(c_12, plain, (![A_10]: (v1_relat_1(A_10) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.25/1.46  tff(c_521, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_511, c_12])).
% 3.25/1.46  tff(c_565, plain, (![A_150]: (v2_funct_1(A_150) | ~v1_funct_1(A_150) | ~v1_relat_1(A_150) | ~v1_xboole_0(A_150))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.25/1.46  tff(c_568, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_565, c_42])).
% 3.25/1.46  tff(c_572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_511, c_521, c_58, c_568])).
% 3.25/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.46  
% 3.25/1.46  Inference rules
% 3.25/1.46  ----------------------
% 3.25/1.46  #Ref     : 0
% 3.25/1.46  #Sup     : 100
% 3.25/1.46  #Fact    : 0
% 3.25/1.46  #Define  : 0
% 3.25/1.46  #Split   : 5
% 3.25/1.46  #Chain   : 0
% 3.25/1.46  #Close   : 0
% 3.25/1.46  
% 3.25/1.46  Ordering : KBO
% 3.25/1.46  
% 3.25/1.46  Simplification rules
% 3.25/1.46  ----------------------
% 3.25/1.46  #Subsume      : 8
% 3.25/1.46  #Demod        : 68
% 3.25/1.46  #Tautology    : 13
% 3.25/1.46  #SimpNegUnit  : 2
% 3.25/1.46  #BackRed      : 10
% 3.25/1.46  
% 3.25/1.46  #Partial instantiations: 0
% 3.25/1.46  #Strategies tried      : 1
% 3.25/1.46  
% 3.25/1.46  Timing (in seconds)
% 3.25/1.46  ----------------------
% 3.30/1.46  Preprocessing        : 0.34
% 3.30/1.46  Parsing              : 0.18
% 3.30/1.46  CNF conversion       : 0.02
% 3.30/1.46  Main loop            : 0.35
% 3.30/1.46  Inferencing          : 0.13
% 3.30/1.46  Reduction            : 0.11
% 3.30/1.46  Demodulation         : 0.08
% 3.30/1.46  BG Simplification    : 0.02
% 3.30/1.46  Subsumption          : 0.07
% 3.30/1.46  Abstraction          : 0.01
% 3.30/1.46  MUC search           : 0.00
% 3.30/1.46  Cooper               : 0.00
% 3.30/1.46  Total                : 0.73
% 3.30/1.46  Index Insertion      : 0.00
% 3.30/1.46  Index Deletion       : 0.00
% 3.30/1.46  Index Matching       : 0.00
% 3.30/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
