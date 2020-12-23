%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:23 EST 2020

% Result     : Theorem 7.78s
% Output     : CNFRefutation 7.99s
% Verified   : 
% Statistics : Number of formulae       :  197 (1196 expanded)
%              Number of leaves         :   49 ( 414 expanded)
%              Depth                    :   17
%              Number of atoms          :  347 (2716 expanded)
%              Number of equality atoms :   90 ( 912 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_175,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_133,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_80,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_131,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_121,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_101,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_155,axiom,(
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

tff(f_61,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_81,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_68,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_150,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_62,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_34,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_86,plain,(
    ! [A_19] : k2_relat_1(k6_partfun1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_34])).

tff(c_38,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_85,plain,(
    ! [A_20] : v1_relat_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_38])).

tff(c_197,plain,(
    ! [A_66] :
      ( k2_relat_1(A_66) != k1_xboole_0
      | k1_xboole_0 = A_66
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_206,plain,(
    ! [A_20] :
      ( k2_relat_1(k6_partfun1(A_20)) != k1_xboole_0
      | k6_partfun1(A_20) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_85,c_197])).

tff(c_216,plain,(
    ! [A_67] :
      ( k1_xboole_0 != A_67
      | k6_partfun1(A_67) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_206])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_222,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_70])).

tff(c_311,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_40,plain,(
    ! [A_20] : v2_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_84,plain,(
    ! [A_20] : v2_funct_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_40])).

tff(c_2889,plain,(
    ! [F_322,E_324,A_320,B_321,D_323,C_325] :
      ( k1_partfun1(A_320,B_321,C_325,D_323,E_324,F_322) = k5_relat_1(E_324,F_322)
      | ~ m1_subset_1(F_322,k1_zfmisc_1(k2_zfmisc_1(C_325,D_323)))
      | ~ v1_funct_1(F_322)
      | ~ m1_subset_1(E_324,k1_zfmisc_1(k2_zfmisc_1(A_320,B_321)))
      | ~ v1_funct_1(E_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2901,plain,(
    ! [A_320,B_321,E_324] :
      ( k1_partfun1(A_320,B_321,'#skF_2','#skF_1',E_324,'#skF_4') = k5_relat_1(E_324,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_324,k1_zfmisc_1(k2_zfmisc_1(A_320,B_321)))
      | ~ v1_funct_1(E_324) ) ),
    inference(resolution,[status(thm)],[c_72,c_2889])).

tff(c_3086,plain,(
    ! [A_342,B_343,E_344] :
      ( k1_partfun1(A_342,B_343,'#skF_2','#skF_1',E_344,'#skF_4') = k5_relat_1(E_344,'#skF_4')
      | ~ m1_subset_1(E_344,k1_zfmisc_1(k2_zfmisc_1(A_342,B_343)))
      | ~ v1_funct_1(E_344) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2901])).

tff(c_3104,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_3086])).

tff(c_3113,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3104])).

tff(c_56,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,D_34] :
      ( m1_subset_1(k1_partfun1(A_31,B_32,C_33,D_34,E_35,F_36),k1_zfmisc_1(k2_zfmisc_1(A_31,D_34)))
      | ~ m1_subset_1(F_36,k1_zfmisc_1(k2_zfmisc_1(C_33,D_34)))
      | ~ v1_funct_1(F_36)
      | ~ m1_subset_1(E_35,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_1(E_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_3380,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3113,c_56])).

tff(c_3387,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_3380])).

tff(c_50,plain,(
    ! [A_28] : m1_subset_1(k6_relat_1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_83,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50])).

tff(c_2593,plain,(
    ! [D_291,C_292,A_293,B_294] :
      ( D_291 = C_292
      | ~ r2_relset_1(A_293,B_294,C_292,D_291)
      | ~ m1_subset_1(D_291,k1_zfmisc_1(k2_zfmisc_1(A_293,B_294)))
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_293,B_294))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2601,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_2593])).

tff(c_2616,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_2601])).

tff(c_2679,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2616])).

tff(c_3782,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3387,c_3113,c_2679])).

tff(c_3783,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2616])).

tff(c_4488,plain,(
    ! [D_463,C_464,E_466,A_467,B_465] :
      ( k1_xboole_0 = C_464
      | v2_funct_1(D_463)
      | ~ v2_funct_1(k1_partfun1(A_467,B_465,B_465,C_464,D_463,E_466))
      | ~ m1_subset_1(E_466,k1_zfmisc_1(k2_zfmisc_1(B_465,C_464)))
      | ~ v1_funct_2(E_466,B_465,C_464)
      | ~ v1_funct_1(E_466)
      | ~ m1_subset_1(D_463,k1_zfmisc_1(k2_zfmisc_1(A_467,B_465)))
      | ~ v1_funct_2(D_463,A_467,B_465)
      | ~ v1_funct_1(D_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_4492,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3783,c_4488])).

tff(c_4496,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_72,c_84,c_4492])).

tff(c_4498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_311,c_4496])).

tff(c_4500,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_24,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_262,plain,(
    ! [B_69,A_70] :
      ( v1_relat_1(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70))
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_274,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_262])).

tff(c_286,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_274])).

tff(c_30,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) != k1_xboole_0
      | k1_xboole_0 = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_308,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_286,c_30])).

tff(c_4643,plain,
    ( k1_relat_1('#skF_4') != '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4500,c_4500,c_308])).

tff(c_4644,plain,(
    k1_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4643])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_160,plain,(
    ! [A_60,B_61] :
      ( v1_xboole_0(k2_zfmisc_1(A_60,B_61))
      | ~ v1_xboole_0(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_169,plain,(
    ! [A_63,B_64] :
      ( k2_zfmisc_1(A_63,B_64) = k1_xboole_0
      | ~ v1_xboole_0(B_64) ) ),
    inference(resolution,[status(thm)],[c_160,c_4])).

tff(c_175,plain,(
    ! [A_63] : k2_zfmisc_1(A_63,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_169])).

tff(c_4505,plain,(
    ! [A_63] : k2_zfmisc_1(A_63,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4500,c_4500,c_175])).

tff(c_4607,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4505,c_72])).

tff(c_4608,plain,(
    ! [A_475] : k2_zfmisc_1(A_475,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4500,c_4500,c_175])).

tff(c_44,plain,(
    ! [C_23,A_21,B_22] :
      ( v4_relat_1(C_23,A_21)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5078,plain,(
    ! [C_525,A_526] :
      ( v4_relat_1(C_525,A_526)
      | ~ m1_subset_1(C_525,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4608,c_44])).

tff(c_5084,plain,(
    ! [A_526] : v4_relat_1('#skF_4',A_526) ),
    inference(resolution,[status(thm)],[c_4607,c_5078])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4512,plain,(
    k6_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4500,c_4500,c_36])).

tff(c_4523,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4512,c_62])).

tff(c_4617,plain,(
    m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4608,c_83])).

tff(c_4626,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4523,c_4617])).

tff(c_5083,plain,(
    ! [A_526] : v4_relat_1('#skF_1',A_526) ),
    inference(resolution,[status(thm)],[c_4626,c_5078])).

tff(c_121,plain,(
    ! [A_59] : k6_relat_1(A_59) = k6_partfun1(A_59) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_127,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_36])).

tff(c_144,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_85])).

tff(c_4510,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4500,c_144])).

tff(c_32,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_87,plain,(
    ! [A_19] : k1_relat_1(k6_partfun1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_32])).

tff(c_139,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_87])).

tff(c_4508,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4500,c_4500,c_139])).

tff(c_4679,plain,(
    ! [B_477,A_478] :
      ( r1_tarski(k1_relat_1(B_477),A_478)
      | ~ v4_relat_1(B_477,A_478)
      | ~ v1_relat_1(B_477) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4684,plain,(
    ! [A_478] :
      ( r1_tarski('#skF_1',A_478)
      | ~ v4_relat_1('#skF_1',A_478)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4508,c_4679])).

tff(c_4690,plain,(
    ! [A_478] :
      ( r1_tarski('#skF_1',A_478)
      | ~ v4_relat_1('#skF_1',A_478) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4510,c_4684])).

tff(c_5096,plain,(
    ! [A_529] : r1_tarski('#skF_1',A_529) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5083,c_4690])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_5119,plain,(
    ! [A_537] :
      ( A_537 = '#skF_1'
      | ~ r1_tarski(A_537,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_5096,c_6])).

tff(c_5557,plain,(
    ! [B_581] :
      ( k1_relat_1(B_581) = '#skF_1'
      | ~ v4_relat_1(B_581,'#skF_1')
      | ~ v1_relat_1(B_581) ) ),
    inference(resolution,[status(thm)],[c_18,c_5119])).

tff(c_5568,plain,
    ( k1_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5084,c_5557])).

tff(c_5590,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_5568])).

tff(c_5592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4644,c_5590])).

tff(c_5593,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4643])).

tff(c_271,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_262])).

tff(c_283,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_271])).

tff(c_300,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_283,c_30])).

tff(c_310,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_4519,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4500,c_310])).

tff(c_5606,plain,(
    k1_relat_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5593,c_4519])).

tff(c_4538,plain,(
    ! [C_468,A_469,B_470] :
      ( v4_relat_1(C_468,A_469)
      | ~ m1_subset_1(C_468,k1_zfmisc_1(k2_zfmisc_1(A_469,B_470))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4549,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_4538])).

tff(c_5602,plain,(
    v4_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5593,c_4549])).

tff(c_5596,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5593,c_4607])).

tff(c_5726,plain,(
    ! [A_587] : k2_zfmisc_1(A_587,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5593,c_5593,c_4505])).

tff(c_6143,plain,(
    ! [C_632,A_633] :
      ( v4_relat_1(C_632,A_633)
      | ~ m1_subset_1(C_632,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5726,c_44])).

tff(c_6146,plain,(
    ! [A_633] : v4_relat_1('#skF_4',A_633) ),
    inference(resolution,[status(thm)],[c_5596,c_6143])).

tff(c_5594,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4643])).

tff(c_5642,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5593,c_5594])).

tff(c_5646,plain,(
    ! [A_9] :
      ( r1_tarski('#skF_4',A_9)
      | ~ v4_relat_1('#skF_4',A_9)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5642,c_18])).

tff(c_5650,plain,(
    ! [A_9] :
      ( r1_tarski('#skF_4',A_9)
      | ~ v4_relat_1('#skF_4',A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_5646])).

tff(c_6169,plain,(
    ! [A_641] : r1_tarski('#skF_4',A_641) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6146,c_5650])).

tff(c_6195,plain,(
    ! [A_646] :
      ( A_646 = '#skF_4'
      | ~ r1_tarski(A_646,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6169,c_6])).

tff(c_6636,plain,(
    ! [B_692] :
      ( k1_relat_1(B_692) = '#skF_4'
      | ~ v4_relat_1(B_692,'#skF_4')
      | ~ v1_relat_1(B_692) ) ),
    inference(resolution,[status(thm)],[c_18,c_6195])).

tff(c_6654,plain,
    ( k1_relat_1('#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5602,c_6636])).

tff(c_6671,plain,(
    k1_relat_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_6654])).

tff(c_6673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5606,c_6671])).

tff(c_6674,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_146,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_84])).

tff(c_6684,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6674,c_146])).

tff(c_6690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_6684])).

tff(c_6691,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_6807,plain,(
    ! [B_704,A_705] :
      ( v1_relat_1(B_704)
      | ~ m1_subset_1(B_704,k1_zfmisc_1(A_705))
      | ~ v1_relat_1(A_705) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6819,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_6807])).

tff(c_6831,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_6819])).

tff(c_7061,plain,(
    ! [C_736,B_737,A_738] :
      ( v5_relat_1(C_736,B_737)
      | ~ m1_subset_1(C_736,k1_zfmisc_1(k2_zfmisc_1(A_738,B_737))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_7077,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_7061])).

tff(c_6816,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_6807])).

tff(c_6828,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_6816])).

tff(c_7486,plain,(
    ! [D_786,F_785,B_784,A_783,C_788,E_787] :
      ( k1_partfun1(A_783,B_784,C_788,D_786,E_787,F_785) = k5_relat_1(E_787,F_785)
      | ~ m1_subset_1(F_785,k1_zfmisc_1(k2_zfmisc_1(C_788,D_786)))
      | ~ v1_funct_1(F_785)
      | ~ m1_subset_1(E_787,k1_zfmisc_1(k2_zfmisc_1(A_783,B_784)))
      | ~ v1_funct_1(E_787) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_7498,plain,(
    ! [A_783,B_784,E_787] :
      ( k1_partfun1(A_783,B_784,'#skF_2','#skF_1',E_787,'#skF_4') = k5_relat_1(E_787,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_787,k1_zfmisc_1(k2_zfmisc_1(A_783,B_784)))
      | ~ v1_funct_1(E_787) ) ),
    inference(resolution,[status(thm)],[c_72,c_7486])).

tff(c_8173,plain,(
    ! [A_847,B_848,E_849] :
      ( k1_partfun1(A_847,B_848,'#skF_2','#skF_1',E_849,'#skF_4') = k5_relat_1(E_849,'#skF_4')
      | ~ m1_subset_1(E_849,k1_zfmisc_1(k2_zfmisc_1(A_847,B_848)))
      | ~ v1_funct_1(E_849) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7498])).

tff(c_8197,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_8173])).

tff(c_8212,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_8197])).

tff(c_8427,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8212,c_56])).

tff(c_8434,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_8427])).

tff(c_7263,plain,(
    ! [D_757,C_758,A_759,B_760] :
      ( D_757 = C_758
      | ~ r2_relset_1(A_759,B_760,C_758,D_757)
      | ~ m1_subset_1(D_757,k1_zfmisc_1(k2_zfmisc_1(A_759,B_760)))
      | ~ m1_subset_1(C_758,k1_zfmisc_1(k2_zfmisc_1(A_759,B_760))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_7269,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_7263])).

tff(c_7280,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_7269])).

tff(c_8547,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8434,c_8212,c_8212,c_7280])).

tff(c_26,plain,(
    ! [A_15,B_17] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_15,B_17)),k2_relat_1(B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8571,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8547,c_26])).

tff(c_8579,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6828,c_6831,c_86,c_8571])).

tff(c_6939,plain,(
    ! [B_720,A_721] :
      ( r1_tarski(k2_relat_1(B_720),A_721)
      | ~ v5_relat_1(B_720,A_721)
      | ~ v1_relat_1(B_720) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6952,plain,(
    ! [B_720,A_721] :
      ( k2_relat_1(B_720) = A_721
      | ~ r1_tarski(A_721,k2_relat_1(B_720))
      | ~ v5_relat_1(B_720,A_721)
      | ~ v1_relat_1(B_720) ) ),
    inference(resolution,[status(thm)],[c_6939,c_6])).

tff(c_8586,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8579,c_6952])).

tff(c_8594,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6831,c_7077,c_8586])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6884,plain,(
    ! [B_710,A_711] :
      ( v5_relat_1(B_710,A_711)
      | ~ r1_tarski(k2_relat_1(B_710),A_711)
      | ~ v1_relat_1(B_710) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6899,plain,(
    ! [B_710] :
      ( v5_relat_1(B_710,k2_relat_1(B_710))
      | ~ v1_relat_1(B_710) ) ),
    inference(resolution,[status(thm)],[c_10,c_6884])).

tff(c_7082,plain,(
    ! [B_741] :
      ( v2_funct_2(B_741,k2_relat_1(B_741))
      | ~ v5_relat_1(B_741,k2_relat_1(B_741))
      | ~ v1_relat_1(B_741) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_7113,plain,(
    ! [B_710] :
      ( v2_funct_2(B_710,k2_relat_1(B_710))
      | ~ v1_relat_1(B_710) ) ),
    inference(resolution,[status(thm)],[c_6899,c_7082])).

tff(c_8612,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8594,c_7113])).

tff(c_8634,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6831,c_8612])).

tff(c_8636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6691,c_8634])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:08:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.78/2.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.78/2.70  
% 7.78/2.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.78/2.70  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.78/2.70  
% 7.78/2.70  %Foreground sorts:
% 7.78/2.70  
% 7.78/2.70  
% 7.78/2.70  %Background operators:
% 7.78/2.70  
% 7.78/2.70  
% 7.78/2.70  %Foreground operators:
% 7.78/2.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.78/2.70  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.78/2.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.78/2.70  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.78/2.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.78/2.70  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.78/2.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.78/2.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.78/2.70  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.78/2.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.78/2.70  tff('#skF_2', type, '#skF_2': $i).
% 7.78/2.70  tff('#skF_3', type, '#skF_3': $i).
% 7.78/2.70  tff('#skF_1', type, '#skF_1': $i).
% 7.78/2.70  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.78/2.70  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.78/2.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.78/2.70  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.78/2.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.78/2.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.78/2.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.78/2.70  tff('#skF_4', type, '#skF_4': $i).
% 7.78/2.70  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.78/2.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.78/2.70  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.78/2.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.78/2.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.78/2.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.78/2.70  
% 7.99/2.73  tff(f_175, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 7.99/2.73  tff(f_133, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.99/2.73  tff(f_80, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.99/2.73  tff(f_85, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.99/2.73  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 7.99/2.73  tff(f_131, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.99/2.73  tff(f_121, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.99/2.73  tff(f_101, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 7.99/2.73  tff(f_99, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.99/2.73  tff(f_155, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 7.99/2.73  tff(f_61, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.99/2.73  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.99/2.73  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.99/2.73  tff(f_40, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 7.99/2.73  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.99/2.73  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.99/2.73  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 7.99/2.73  tff(f_81, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 7.99/2.73  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.99/2.73  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 7.99/2.73  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 7.99/2.73  tff(f_109, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 7.99/2.73  tff(c_68, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 7.99/2.73  tff(c_150, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 7.99/2.73  tff(c_62, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.99/2.73  tff(c_34, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.99/2.73  tff(c_86, plain, (![A_19]: (k2_relat_1(k6_partfun1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_34])).
% 7.99/2.73  tff(c_38, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.99/2.73  tff(c_85, plain, (![A_20]: (v1_relat_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_38])).
% 7.99/2.73  tff(c_197, plain, (![A_66]: (k2_relat_1(A_66)!=k1_xboole_0 | k1_xboole_0=A_66 | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.99/2.73  tff(c_206, plain, (![A_20]: (k2_relat_1(k6_partfun1(A_20))!=k1_xboole_0 | k6_partfun1(A_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_85, c_197])).
% 7.99/2.73  tff(c_216, plain, (![A_67]: (k1_xboole_0!=A_67 | k6_partfun1(A_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_206])).
% 7.99/2.73  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 7.99/2.73  tff(c_222, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_216, c_70])).
% 7.99/2.73  tff(c_311, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_222])).
% 7.99/2.73  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 7.99/2.73  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 7.99/2.73  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 7.99/2.73  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 7.99/2.73  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 7.99/2.73  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 7.99/2.73  tff(c_40, plain, (![A_20]: (v2_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.99/2.73  tff(c_84, plain, (![A_20]: (v2_funct_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_40])).
% 7.99/2.73  tff(c_2889, plain, (![F_322, E_324, A_320, B_321, D_323, C_325]: (k1_partfun1(A_320, B_321, C_325, D_323, E_324, F_322)=k5_relat_1(E_324, F_322) | ~m1_subset_1(F_322, k1_zfmisc_1(k2_zfmisc_1(C_325, D_323))) | ~v1_funct_1(F_322) | ~m1_subset_1(E_324, k1_zfmisc_1(k2_zfmisc_1(A_320, B_321))) | ~v1_funct_1(E_324))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.99/2.73  tff(c_2901, plain, (![A_320, B_321, E_324]: (k1_partfun1(A_320, B_321, '#skF_2', '#skF_1', E_324, '#skF_4')=k5_relat_1(E_324, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_324, k1_zfmisc_1(k2_zfmisc_1(A_320, B_321))) | ~v1_funct_1(E_324))), inference(resolution, [status(thm)], [c_72, c_2889])).
% 7.99/2.73  tff(c_3086, plain, (![A_342, B_343, E_344]: (k1_partfun1(A_342, B_343, '#skF_2', '#skF_1', E_344, '#skF_4')=k5_relat_1(E_344, '#skF_4') | ~m1_subset_1(E_344, k1_zfmisc_1(k2_zfmisc_1(A_342, B_343))) | ~v1_funct_1(E_344))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2901])).
% 7.99/2.73  tff(c_3104, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_3086])).
% 7.99/2.73  tff(c_3113, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3104])).
% 7.99/2.73  tff(c_56, plain, (![A_31, C_33, B_32, F_36, E_35, D_34]: (m1_subset_1(k1_partfun1(A_31, B_32, C_33, D_34, E_35, F_36), k1_zfmisc_1(k2_zfmisc_1(A_31, D_34))) | ~m1_subset_1(F_36, k1_zfmisc_1(k2_zfmisc_1(C_33, D_34))) | ~v1_funct_1(F_36) | ~m1_subset_1(E_35, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_1(E_35))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.99/2.73  tff(c_3380, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3113, c_56])).
% 7.99/2.73  tff(c_3387, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_3380])).
% 7.99/2.73  tff(c_50, plain, (![A_28]: (m1_subset_1(k6_relat_1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.99/2.73  tff(c_83, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50])).
% 7.99/2.73  tff(c_2593, plain, (![D_291, C_292, A_293, B_294]: (D_291=C_292 | ~r2_relset_1(A_293, B_294, C_292, D_291) | ~m1_subset_1(D_291, k1_zfmisc_1(k2_zfmisc_1(A_293, B_294))) | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_293, B_294))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.99/2.73  tff(c_2601, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_2593])).
% 7.99/2.73  tff(c_2616, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_2601])).
% 7.99/2.73  tff(c_2679, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2616])).
% 7.99/2.73  tff(c_3782, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3387, c_3113, c_2679])).
% 7.99/2.73  tff(c_3783, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2616])).
% 7.99/2.73  tff(c_4488, plain, (![D_463, C_464, E_466, A_467, B_465]: (k1_xboole_0=C_464 | v2_funct_1(D_463) | ~v2_funct_1(k1_partfun1(A_467, B_465, B_465, C_464, D_463, E_466)) | ~m1_subset_1(E_466, k1_zfmisc_1(k2_zfmisc_1(B_465, C_464))) | ~v1_funct_2(E_466, B_465, C_464) | ~v1_funct_1(E_466) | ~m1_subset_1(D_463, k1_zfmisc_1(k2_zfmisc_1(A_467, B_465))) | ~v1_funct_2(D_463, A_467, B_465) | ~v1_funct_1(D_463))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.99/2.73  tff(c_4492, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3783, c_4488])).
% 7.99/2.73  tff(c_4496, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_72, c_84, c_4492])).
% 7.99/2.73  tff(c_4498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_311, c_4496])).
% 7.99/2.73  tff(c_4500, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_222])).
% 7.99/2.73  tff(c_24, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.99/2.73  tff(c_262, plain, (![B_69, A_70]: (v1_relat_1(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.99/2.73  tff(c_274, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_262])).
% 7.99/2.73  tff(c_286, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_274])).
% 7.99/2.73  tff(c_30, plain, (![A_18]: (k1_relat_1(A_18)!=k1_xboole_0 | k1_xboole_0=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.99/2.73  tff(c_308, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_286, c_30])).
% 7.99/2.73  tff(c_4643, plain, (k1_relat_1('#skF_4')!='#skF_1' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4500, c_4500, c_308])).
% 7.99/2.73  tff(c_4644, plain, (k1_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_4643])).
% 7.99/2.73  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.99/2.73  tff(c_160, plain, (![A_60, B_61]: (v1_xboole_0(k2_zfmisc_1(A_60, B_61)) | ~v1_xboole_0(B_61))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.99/2.73  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 7.99/2.73  tff(c_169, plain, (![A_63, B_64]: (k2_zfmisc_1(A_63, B_64)=k1_xboole_0 | ~v1_xboole_0(B_64))), inference(resolution, [status(thm)], [c_160, c_4])).
% 7.99/2.73  tff(c_175, plain, (![A_63]: (k2_zfmisc_1(A_63, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_169])).
% 7.99/2.73  tff(c_4505, plain, (![A_63]: (k2_zfmisc_1(A_63, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4500, c_4500, c_175])).
% 7.99/2.73  tff(c_4607, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4505, c_72])).
% 7.99/2.73  tff(c_4608, plain, (![A_475]: (k2_zfmisc_1(A_475, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4500, c_4500, c_175])).
% 7.99/2.73  tff(c_44, plain, (![C_23, A_21, B_22]: (v4_relat_1(C_23, A_21) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.99/2.73  tff(c_5078, plain, (![C_525, A_526]: (v4_relat_1(C_525, A_526) | ~m1_subset_1(C_525, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4608, c_44])).
% 7.99/2.73  tff(c_5084, plain, (![A_526]: (v4_relat_1('#skF_4', A_526))), inference(resolution, [status(thm)], [c_4607, c_5078])).
% 7.99/2.73  tff(c_18, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.99/2.73  tff(c_36, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.99/2.73  tff(c_4512, plain, (k6_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4500, c_4500, c_36])).
% 7.99/2.73  tff(c_4523, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_4512, c_62])).
% 7.99/2.73  tff(c_4617, plain, (m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4608, c_83])).
% 7.99/2.73  tff(c_4626, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4523, c_4617])).
% 7.99/2.73  tff(c_5083, plain, (![A_526]: (v4_relat_1('#skF_1', A_526))), inference(resolution, [status(thm)], [c_4626, c_5078])).
% 7.99/2.73  tff(c_121, plain, (![A_59]: (k6_relat_1(A_59)=k6_partfun1(A_59))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.99/2.73  tff(c_127, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_121, c_36])).
% 7.99/2.73  tff(c_144, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_127, c_85])).
% 7.99/2.73  tff(c_4510, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4500, c_144])).
% 7.99/2.73  tff(c_32, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.99/2.73  tff(c_87, plain, (![A_19]: (k1_relat_1(k6_partfun1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_32])).
% 7.99/2.73  tff(c_139, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_127, c_87])).
% 7.99/2.73  tff(c_4508, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4500, c_4500, c_139])).
% 7.99/2.73  tff(c_4679, plain, (![B_477, A_478]: (r1_tarski(k1_relat_1(B_477), A_478) | ~v4_relat_1(B_477, A_478) | ~v1_relat_1(B_477))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.99/2.73  tff(c_4684, plain, (![A_478]: (r1_tarski('#skF_1', A_478) | ~v4_relat_1('#skF_1', A_478) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4508, c_4679])).
% 7.99/2.73  tff(c_4690, plain, (![A_478]: (r1_tarski('#skF_1', A_478) | ~v4_relat_1('#skF_1', A_478))), inference(demodulation, [status(thm), theory('equality')], [c_4510, c_4684])).
% 7.99/2.73  tff(c_5096, plain, (![A_529]: (r1_tarski('#skF_1', A_529))), inference(demodulation, [status(thm), theory('equality')], [c_5083, c_4690])).
% 7.99/2.73  tff(c_6, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.99/2.73  tff(c_5119, plain, (![A_537]: (A_537='#skF_1' | ~r1_tarski(A_537, '#skF_1'))), inference(resolution, [status(thm)], [c_5096, c_6])).
% 7.99/2.73  tff(c_5557, plain, (![B_581]: (k1_relat_1(B_581)='#skF_1' | ~v4_relat_1(B_581, '#skF_1') | ~v1_relat_1(B_581))), inference(resolution, [status(thm)], [c_18, c_5119])).
% 7.99/2.73  tff(c_5568, plain, (k1_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_5084, c_5557])).
% 7.99/2.73  tff(c_5590, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_286, c_5568])).
% 7.99/2.73  tff(c_5592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4644, c_5590])).
% 7.99/2.73  tff(c_5593, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_4643])).
% 7.99/2.73  tff(c_271, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_262])).
% 7.99/2.73  tff(c_283, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_271])).
% 7.99/2.73  tff(c_300, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_283, c_30])).
% 7.99/2.73  tff(c_310, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_300])).
% 7.99/2.73  tff(c_4519, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4500, c_310])).
% 7.99/2.73  tff(c_5606, plain, (k1_relat_1('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5593, c_4519])).
% 7.99/2.73  tff(c_4538, plain, (![C_468, A_469, B_470]: (v4_relat_1(C_468, A_469) | ~m1_subset_1(C_468, k1_zfmisc_1(k2_zfmisc_1(A_469, B_470))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.99/2.73  tff(c_4549, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_4538])).
% 7.99/2.73  tff(c_5602, plain, (v4_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5593, c_4549])).
% 7.99/2.73  tff(c_5596, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5593, c_4607])).
% 7.99/2.73  tff(c_5726, plain, (![A_587]: (k2_zfmisc_1(A_587, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5593, c_5593, c_4505])).
% 7.99/2.73  tff(c_6143, plain, (![C_632, A_633]: (v4_relat_1(C_632, A_633) | ~m1_subset_1(C_632, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5726, c_44])).
% 7.99/2.73  tff(c_6146, plain, (![A_633]: (v4_relat_1('#skF_4', A_633))), inference(resolution, [status(thm)], [c_5596, c_6143])).
% 7.99/2.73  tff(c_5594, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_4643])).
% 7.99/2.73  tff(c_5642, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5593, c_5594])).
% 7.99/2.73  tff(c_5646, plain, (![A_9]: (r1_tarski('#skF_4', A_9) | ~v4_relat_1('#skF_4', A_9) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5642, c_18])).
% 7.99/2.73  tff(c_5650, plain, (![A_9]: (r1_tarski('#skF_4', A_9) | ~v4_relat_1('#skF_4', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_286, c_5646])).
% 7.99/2.73  tff(c_6169, plain, (![A_641]: (r1_tarski('#skF_4', A_641))), inference(demodulation, [status(thm), theory('equality')], [c_6146, c_5650])).
% 7.99/2.73  tff(c_6195, plain, (![A_646]: (A_646='#skF_4' | ~r1_tarski(A_646, '#skF_4'))), inference(resolution, [status(thm)], [c_6169, c_6])).
% 7.99/2.73  tff(c_6636, plain, (![B_692]: (k1_relat_1(B_692)='#skF_4' | ~v4_relat_1(B_692, '#skF_4') | ~v1_relat_1(B_692))), inference(resolution, [status(thm)], [c_18, c_6195])).
% 7.99/2.73  tff(c_6654, plain, (k1_relat_1('#skF_3')='#skF_4' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5602, c_6636])).
% 7.99/2.73  tff(c_6671, plain, (k1_relat_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_283, c_6654])).
% 7.99/2.73  tff(c_6673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5606, c_6671])).
% 7.99/2.73  tff(c_6674, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_300])).
% 7.99/2.73  tff(c_146, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_127, c_84])).
% 7.99/2.73  tff(c_6684, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6674, c_146])).
% 7.99/2.73  tff(c_6690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_6684])).
% 7.99/2.73  tff(c_6691, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_68])).
% 7.99/2.73  tff(c_6807, plain, (![B_704, A_705]: (v1_relat_1(B_704) | ~m1_subset_1(B_704, k1_zfmisc_1(A_705)) | ~v1_relat_1(A_705))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.99/2.73  tff(c_6819, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_6807])).
% 7.99/2.73  tff(c_6831, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_6819])).
% 7.99/2.73  tff(c_7061, plain, (![C_736, B_737, A_738]: (v5_relat_1(C_736, B_737) | ~m1_subset_1(C_736, k1_zfmisc_1(k2_zfmisc_1(A_738, B_737))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.99/2.73  tff(c_7077, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_7061])).
% 7.99/2.73  tff(c_6816, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_6807])).
% 7.99/2.73  tff(c_6828, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_6816])).
% 7.99/2.73  tff(c_7486, plain, (![D_786, F_785, B_784, A_783, C_788, E_787]: (k1_partfun1(A_783, B_784, C_788, D_786, E_787, F_785)=k5_relat_1(E_787, F_785) | ~m1_subset_1(F_785, k1_zfmisc_1(k2_zfmisc_1(C_788, D_786))) | ~v1_funct_1(F_785) | ~m1_subset_1(E_787, k1_zfmisc_1(k2_zfmisc_1(A_783, B_784))) | ~v1_funct_1(E_787))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.99/2.73  tff(c_7498, plain, (![A_783, B_784, E_787]: (k1_partfun1(A_783, B_784, '#skF_2', '#skF_1', E_787, '#skF_4')=k5_relat_1(E_787, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_787, k1_zfmisc_1(k2_zfmisc_1(A_783, B_784))) | ~v1_funct_1(E_787))), inference(resolution, [status(thm)], [c_72, c_7486])).
% 7.99/2.73  tff(c_8173, plain, (![A_847, B_848, E_849]: (k1_partfun1(A_847, B_848, '#skF_2', '#skF_1', E_849, '#skF_4')=k5_relat_1(E_849, '#skF_4') | ~m1_subset_1(E_849, k1_zfmisc_1(k2_zfmisc_1(A_847, B_848))) | ~v1_funct_1(E_849))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_7498])).
% 7.99/2.73  tff(c_8197, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_8173])).
% 7.99/2.73  tff(c_8212, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_8197])).
% 7.99/2.73  tff(c_8427, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8212, c_56])).
% 7.99/2.73  tff(c_8434, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_8427])).
% 7.99/2.73  tff(c_7263, plain, (![D_757, C_758, A_759, B_760]: (D_757=C_758 | ~r2_relset_1(A_759, B_760, C_758, D_757) | ~m1_subset_1(D_757, k1_zfmisc_1(k2_zfmisc_1(A_759, B_760))) | ~m1_subset_1(C_758, k1_zfmisc_1(k2_zfmisc_1(A_759, B_760))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.99/2.73  tff(c_7269, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_7263])).
% 7.99/2.73  tff(c_7280, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_7269])).
% 7.99/2.73  tff(c_8547, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8434, c_8212, c_8212, c_7280])).
% 7.99/2.73  tff(c_26, plain, (![A_15, B_17]: (r1_tarski(k2_relat_1(k5_relat_1(A_15, B_17)), k2_relat_1(B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.99/2.73  tff(c_8571, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8547, c_26])).
% 7.99/2.73  tff(c_8579, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6828, c_6831, c_86, c_8571])).
% 7.99/2.73  tff(c_6939, plain, (![B_720, A_721]: (r1_tarski(k2_relat_1(B_720), A_721) | ~v5_relat_1(B_720, A_721) | ~v1_relat_1(B_720))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.99/2.73  tff(c_6952, plain, (![B_720, A_721]: (k2_relat_1(B_720)=A_721 | ~r1_tarski(A_721, k2_relat_1(B_720)) | ~v5_relat_1(B_720, A_721) | ~v1_relat_1(B_720))), inference(resolution, [status(thm)], [c_6939, c_6])).
% 7.99/2.73  tff(c_8586, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8579, c_6952])).
% 7.99/2.73  tff(c_8594, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6831, c_7077, c_8586])).
% 7.99/2.73  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.99/2.73  tff(c_6884, plain, (![B_710, A_711]: (v5_relat_1(B_710, A_711) | ~r1_tarski(k2_relat_1(B_710), A_711) | ~v1_relat_1(B_710))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.99/2.73  tff(c_6899, plain, (![B_710]: (v5_relat_1(B_710, k2_relat_1(B_710)) | ~v1_relat_1(B_710))), inference(resolution, [status(thm)], [c_10, c_6884])).
% 7.99/2.73  tff(c_7082, plain, (![B_741]: (v2_funct_2(B_741, k2_relat_1(B_741)) | ~v5_relat_1(B_741, k2_relat_1(B_741)) | ~v1_relat_1(B_741))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.99/2.73  tff(c_7113, plain, (![B_710]: (v2_funct_2(B_710, k2_relat_1(B_710)) | ~v1_relat_1(B_710))), inference(resolution, [status(thm)], [c_6899, c_7082])).
% 7.99/2.73  tff(c_8612, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8594, c_7113])).
% 7.99/2.73  tff(c_8634, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6831, c_8612])).
% 7.99/2.73  tff(c_8636, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6691, c_8634])).
% 7.99/2.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.99/2.73  
% 7.99/2.73  Inference rules
% 7.99/2.73  ----------------------
% 7.99/2.73  #Ref     : 11
% 7.99/2.73  #Sup     : 1752
% 7.99/2.73  #Fact    : 0
% 7.99/2.73  #Define  : 0
% 7.99/2.73  #Split   : 32
% 7.99/2.73  #Chain   : 0
% 7.99/2.73  #Close   : 0
% 7.99/2.73  
% 7.99/2.73  Ordering : KBO
% 7.99/2.73  
% 7.99/2.73  Simplification rules
% 7.99/2.73  ----------------------
% 7.99/2.73  #Subsume      : 204
% 7.99/2.73  #Demod        : 1550
% 7.99/2.73  #Tautology    : 669
% 7.99/2.73  #SimpNegUnit  : 12
% 7.99/2.73  #BackRed      : 89
% 7.99/2.73  
% 7.99/2.73  #Partial instantiations: 0
% 7.99/2.73  #Strategies tried      : 1
% 7.99/2.73  
% 7.99/2.73  Timing (in seconds)
% 7.99/2.73  ----------------------
% 7.99/2.73  Preprocessing        : 0.37
% 7.99/2.73  Parsing              : 0.20
% 7.99/2.73  CNF conversion       : 0.02
% 7.99/2.73  Main loop            : 1.52
% 7.99/2.73  Inferencing          : 0.52
% 7.99/2.73  Reduction            : 0.54
% 7.99/2.73  Demodulation         : 0.39
% 7.99/2.73  BG Simplification    : 0.05
% 7.99/2.73  Subsumption          : 0.28
% 7.99/2.73  Abstraction          : 0.06
% 7.99/2.73  MUC search           : 0.00
% 7.99/2.73  Cooper               : 0.00
% 7.99/2.73  Total                : 1.94
% 7.99/2.73  Index Insertion      : 0.00
% 7.99/2.73  Index Deletion       : 0.00
% 7.99/2.73  Index Matching       : 0.00
% 7.99/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
