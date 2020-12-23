%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:19 EST 2020

% Result     : Theorem 8.23s
% Output     : CNFRefutation 8.44s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 614 expanded)
%              Number of leaves         :   50 ( 230 expanded)
%              Depth                    :   12
%              Number of atoms          :  372 (1769 expanded)
%              Number of equality atoms :   64 ( 176 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_179,negated_conjecture,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_137,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_135,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_125,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_105,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_159,axiom,(
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

tff(f_73,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_39,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_85,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(c_66,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_138,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_78,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_60,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_38,plain,(
    ! [A_24] : v2_funct_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_82,plain,(
    ! [A_24] : v2_funct_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_38])).

tff(c_5418,plain,(
    ! [C_353,F_355,D_354,B_356,A_352,E_351] :
      ( k1_partfun1(A_352,B_356,C_353,D_354,E_351,F_355) = k5_relat_1(E_351,F_355)
      | ~ m1_subset_1(F_355,k1_zfmisc_1(k2_zfmisc_1(C_353,D_354)))
      | ~ v1_funct_1(F_355)
      | ~ m1_subset_1(E_351,k1_zfmisc_1(k2_zfmisc_1(A_352,B_356)))
      | ~ v1_funct_1(E_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_5428,plain,(
    ! [A_352,B_356,E_351] :
      ( k1_partfun1(A_352,B_356,'#skF_2','#skF_1',E_351,'#skF_4') = k5_relat_1(E_351,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_351,k1_zfmisc_1(k2_zfmisc_1(A_352,B_356)))
      | ~ v1_funct_1(E_351) ) ),
    inference(resolution,[status(thm)],[c_70,c_5418])).

tff(c_5872,plain,(
    ! [A_375,B_376,E_377] :
      ( k1_partfun1(A_375,B_376,'#skF_2','#skF_1',E_377,'#skF_4') = k5_relat_1(E_377,'#skF_4')
      | ~ m1_subset_1(E_377,k1_zfmisc_1(k2_zfmisc_1(A_375,B_376)))
      | ~ v1_funct_1(E_377) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5428])).

tff(c_5893,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_5872])).

tff(c_5901,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5893])).

tff(c_54,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39] :
      ( m1_subset_1(k1_partfun1(A_35,B_36,C_37,D_38,E_39,F_40),k1_zfmisc_1(k2_zfmisc_1(A_35,D_38)))
      | ~ m1_subset_1(F_40,k1_zfmisc_1(k2_zfmisc_1(C_37,D_38)))
      | ~ v1_funct_1(F_40)
      | ~ m1_subset_1(E_39,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_1(E_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_6657,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5901,c_54])).

tff(c_6664,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_6657])).

tff(c_48,plain,(
    ! [A_32] : m1_subset_1(k6_relat_1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_81,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_48])).

tff(c_68,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_4880,plain,(
    ! [D_317,C_318,A_319,B_320] :
      ( D_317 = C_318
      | ~ r2_relset_1(A_319,B_320,C_318,D_317)
      | ~ m1_subset_1(D_317,k1_zfmisc_1(k2_zfmisc_1(A_319,B_320)))
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(A_319,B_320))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4890,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_4880])).

tff(c_4909,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_4890])).

tff(c_5050,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4909])).

tff(c_7270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6664,c_5901,c_5050])).

tff(c_7271,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4909])).

tff(c_8882,plain,(
    ! [E_494,A_497,C_498,D_495,B_496] :
      ( k1_xboole_0 = C_498
      | v2_funct_1(D_495)
      | ~ v2_funct_1(k1_partfun1(A_497,B_496,B_496,C_498,D_495,E_494))
      | ~ m1_subset_1(E_494,k1_zfmisc_1(k2_zfmisc_1(B_496,C_498)))
      | ~ v1_funct_2(E_494,B_496,C_498)
      | ~ v1_funct_1(E_494)
      | ~ m1_subset_1(D_495,k1_zfmisc_1(k2_zfmisc_1(A_497,B_496)))
      | ~ v1_funct_2(D_495,A_497,B_496)
      | ~ v1_funct_1(D_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_8886,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7271,c_8882])).

tff(c_8890,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_82,c_8886])).

tff(c_8891,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_8890])).

tff(c_26,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_168,plain,(
    ! [B_71,A_72] :
      ( v1_relat_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_177,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_168])).

tff(c_189,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_177])).

tff(c_293,plain,(
    ! [C_82,B_83,A_84] :
      ( v5_relat_1(C_82,B_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_307,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_293])).

tff(c_554,plain,(
    ! [B_106,A_107] :
      ( k2_relat_1(B_106) = A_107
      | ~ v2_funct_2(B_106,A_107)
      | ~ v5_relat_1(B_106,A_107)
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_572,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_307,c_554])).

tff(c_589,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_572])).

tff(c_604,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_589])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_180,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_168])).

tff(c_192,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_180])).

tff(c_32,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_84,plain,(
    ! [A_23] : k2_relat_1(k6_partfun1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_32])).

tff(c_794,plain,(
    ! [D_126,C_127,A_128,B_129] :
      ( D_126 = C_127
      | ~ r2_relset_1(A_128,B_129,C_127,D_126)
      | ~ m1_subset_1(D_126,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_804,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_794])).

tff(c_823,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_804])).

tff(c_1059,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_823])).

tff(c_3333,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1059])).

tff(c_3337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_3333])).

tff(c_3338,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_823])).

tff(c_3757,plain,(
    ! [E_266,A_267,F_270,C_268,D_269,B_271] :
      ( k1_partfun1(A_267,B_271,C_268,D_269,E_266,F_270) = k5_relat_1(E_266,F_270)
      | ~ m1_subset_1(F_270,k1_zfmisc_1(k2_zfmisc_1(C_268,D_269)))
      | ~ v1_funct_1(F_270)
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(A_267,B_271)))
      | ~ v1_funct_1(E_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3767,plain,(
    ! [A_267,B_271,E_266] :
      ( k1_partfun1(A_267,B_271,'#skF_2','#skF_1',E_266,'#skF_4') = k5_relat_1(E_266,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(A_267,B_271)))
      | ~ v1_funct_1(E_266) ) ),
    inference(resolution,[status(thm)],[c_70,c_3757])).

tff(c_4458,plain,(
    ! [A_293,B_294,E_295] :
      ( k1_partfun1(A_293,B_294,'#skF_2','#skF_1',E_295,'#skF_4') = k5_relat_1(E_295,'#skF_4')
      | ~ m1_subset_1(E_295,k1_zfmisc_1(k2_zfmisc_1(A_293,B_294)))
      | ~ v1_funct_1(E_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3767])).

tff(c_4482,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_4458])).

tff(c_4490,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3338,c_4482])).

tff(c_28,plain,(
    ! [A_20,B_22] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_20,B_22)),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4494,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4490,c_28])).

tff(c_4498,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_189,c_84,c_4494])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4502,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_4498,c_4])).

tff(c_4503,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4502])).

tff(c_4506,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_4503])).

tff(c_4510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_307,c_4506])).

tff(c_4511,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4502])).

tff(c_330,plain,(
    ! [B_87,A_88] :
      ( v5_relat_1(B_87,A_88)
      | ~ r1_tarski(k2_relat_1(B_87),A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_345,plain,(
    ! [B_87] :
      ( v5_relat_1(B_87,k2_relat_1(B_87))
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_8,c_330])).

tff(c_504,plain,(
    ! [B_103] :
      ( v2_funct_2(B_103,k2_relat_1(B_103))
      | ~ v5_relat_1(B_103,k2_relat_1(B_103))
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_525,plain,(
    ! [B_87] :
      ( v2_funct_2(B_87,k2_relat_1(B_87))
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_345,c_504])).

tff(c_4524,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4511,c_525])).

tff(c_4542,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_4524])).

tff(c_4544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_604,c_4542])).

tff(c_4545,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_589])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( v5_relat_1(B_17,A_16)
      | ~ r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4580,plain,(
    ! [A_16] :
      ( v5_relat_1('#skF_4',A_16)
      | ~ r1_tarski('#skF_1',A_16)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4545,c_22])).

tff(c_4592,plain,(
    ! [A_16] :
      ( v5_relat_1('#skF_4',A_16)
      | ~ r1_tarski('#skF_1',A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_4580])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( v1_xboole_0(k2_zfmisc_1(A_8,B_9))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_249,plain,(
    ! [B_79,A_80] :
      ( v1_xboole_0(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_80))
      | ~ v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_261,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_249])).

tff(c_309,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_261])).

tff(c_317,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_309])).

tff(c_406,plain,(
    ! [B_97,A_98] :
      ( r1_tarski(k2_relat_1(B_97),A_98)
      | ~ v5_relat_1(B_97,A_98)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_193,plain,(
    ! [B_73,A_74] :
      ( ~ r1_xboole_0(B_73,A_74)
      | ~ r1_tarski(B_73,A_74)
      | v1_xboole_0(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_197,plain,(
    ! [A_5] :
      ( ~ r1_tarski(A_5,k1_xboole_0)
      | v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_193])).

tff(c_7440,plain,(
    ! [B_430] :
      ( v1_xboole_0(k2_relat_1(B_430))
      | ~ v5_relat_1(B_430,k1_xboole_0)
      | ~ v1_relat_1(B_430) ) ),
    inference(resolution,[status(thm)],[c_406,c_197])).

tff(c_7451,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v5_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4545,c_7440])).

tff(c_7462,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_7451])).

tff(c_7463,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_317,c_7462])).

tff(c_7471,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4592,c_7463])).

tff(c_8909,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8891,c_7471])).

tff(c_8948,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8909])).

tff(c_8949,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_261])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8957,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8949,c_2])).

tff(c_98,plain,(
    ! [A_63] : k6_relat_1(A_63) = k6_partfun1(A_63) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_34,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_104,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_34])).

tff(c_117,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_82])).

tff(c_8966,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8957,c_117])).

tff(c_8975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_8966])).

tff(c_8976,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_9057,plain,(
    ! [B_510,A_511] :
      ( v1_relat_1(B_510)
      | ~ m1_subset_1(B_510,k1_zfmisc_1(A_511))
      | ~ v1_relat_1(A_511) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_9066,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_9057])).

tff(c_9078,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_9066])).

tff(c_9315,plain,(
    ! [C_533,B_534,A_535] :
      ( v5_relat_1(C_533,B_534)
      | ~ m1_subset_1(C_533,k1_zfmisc_1(k2_zfmisc_1(A_535,B_534))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_9330,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_9315])).

tff(c_9069,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_9057])).

tff(c_9081,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_9069])).

tff(c_10257,plain,(
    ! [B_601,C_598,F_600,A_597,D_599,E_596] :
      ( k1_partfun1(A_597,B_601,C_598,D_599,E_596,F_600) = k5_relat_1(E_596,F_600)
      | ~ m1_subset_1(F_600,k1_zfmisc_1(k2_zfmisc_1(C_598,D_599)))
      | ~ v1_funct_1(F_600)
      | ~ m1_subset_1(E_596,k1_zfmisc_1(k2_zfmisc_1(A_597,B_601)))
      | ~ v1_funct_1(E_596) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_10267,plain,(
    ! [A_597,B_601,E_596] :
      ( k1_partfun1(A_597,B_601,'#skF_2','#skF_1',E_596,'#skF_4') = k5_relat_1(E_596,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_596,k1_zfmisc_1(k2_zfmisc_1(A_597,B_601)))
      | ~ v1_funct_1(E_596) ) ),
    inference(resolution,[status(thm)],[c_70,c_10257])).

tff(c_10452,plain,(
    ! [A_616,B_617,E_618] :
      ( k1_partfun1(A_616,B_617,'#skF_2','#skF_1',E_618,'#skF_4') = k5_relat_1(E_618,'#skF_4')
      | ~ m1_subset_1(E_618,k1_zfmisc_1(k2_zfmisc_1(A_616,B_617)))
      | ~ v1_funct_1(E_618) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_10267])).

tff(c_10473,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_10452])).

tff(c_10481,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_10473])).

tff(c_10964,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10481,c_54])).

tff(c_10968,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_10964])).

tff(c_9604,plain,(
    ! [D_557,C_558,A_559,B_560] :
      ( D_557 = C_558
      | ~ r2_relset_1(A_559,B_560,C_558,D_557)
      | ~ m1_subset_1(D_557,k1_zfmisc_1(k2_zfmisc_1(A_559,B_560)))
      | ~ m1_subset_1(C_558,k1_zfmisc_1(k2_zfmisc_1(A_559,B_560))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_9614,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_9604])).

tff(c_9633,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_9614])).

tff(c_9790,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_9633])).

tff(c_12096,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10968,c_10481,c_9790])).

tff(c_12097,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_9633])).

tff(c_12600,plain,(
    ! [C_699,D_700,A_698,E_697,B_702,F_701] :
      ( k1_partfun1(A_698,B_702,C_699,D_700,E_697,F_701) = k5_relat_1(E_697,F_701)
      | ~ m1_subset_1(F_701,k1_zfmisc_1(k2_zfmisc_1(C_699,D_700)))
      | ~ v1_funct_1(F_701)
      | ~ m1_subset_1(E_697,k1_zfmisc_1(k2_zfmisc_1(A_698,B_702)))
      | ~ v1_funct_1(E_697) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_12610,plain,(
    ! [A_698,B_702,E_697] :
      ( k1_partfun1(A_698,B_702,'#skF_2','#skF_1',E_697,'#skF_4') = k5_relat_1(E_697,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_697,k1_zfmisc_1(k2_zfmisc_1(A_698,B_702)))
      | ~ v1_funct_1(E_697) ) ),
    inference(resolution,[status(thm)],[c_70,c_12600])).

tff(c_13942,plain,(
    ! [A_751,B_752,E_753] :
      ( k1_partfun1(A_751,B_752,'#skF_2','#skF_1',E_753,'#skF_4') = k5_relat_1(E_753,'#skF_4')
      | ~ m1_subset_1(E_753,k1_zfmisc_1(k2_zfmisc_1(A_751,B_752)))
      | ~ v1_funct_1(E_753) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_12610])).

tff(c_13972,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_13942])).

tff(c_13986,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_12097,c_13972])).

tff(c_13990,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13986,c_28])).

tff(c_13994,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9081,c_9078,c_84,c_13990])).

tff(c_13998,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_13994,c_4])).

tff(c_13999,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_13998])).

tff(c_14002,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_13999])).

tff(c_14006,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9078,c_9330,c_14002])).

tff(c_14007,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13998])).

tff(c_9231,plain,(
    ! [B_522,A_523] :
      ( v5_relat_1(B_522,A_523)
      | ~ r1_tarski(k2_relat_1(B_522),A_523)
      | ~ v1_relat_1(B_522) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_9250,plain,(
    ! [B_522] :
      ( v5_relat_1(B_522,k2_relat_1(B_522))
      | ~ v1_relat_1(B_522) ) ),
    inference(resolution,[status(thm)],[c_8,c_9231])).

tff(c_9392,plain,(
    ! [B_538] :
      ( v2_funct_2(B_538,k2_relat_1(B_538))
      | ~ v5_relat_1(B_538,k2_relat_1(B_538))
      | ~ v1_relat_1(B_538) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_9406,plain,(
    ! [B_522] :
      ( v2_funct_2(B_522,k2_relat_1(B_522))
      | ~ v1_relat_1(B_522) ) ),
    inference(resolution,[status(thm)],[c_9250,c_9392])).

tff(c_14020,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14007,c_9406])).

tff(c_14038,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9078,c_14020])).

tff(c_14040,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8976,c_14038])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:41:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.23/2.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.23/2.96  
% 8.23/2.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.23/2.96  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.23/2.96  
% 8.23/2.96  %Foreground sorts:
% 8.23/2.96  
% 8.23/2.96  
% 8.23/2.96  %Background operators:
% 8.23/2.96  
% 8.23/2.96  
% 8.23/2.96  %Foreground operators:
% 8.23/2.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.23/2.96  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.23/2.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.23/2.96  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.23/2.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.23/2.96  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.23/2.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.23/2.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.23/2.96  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.23/2.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.23/2.96  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.23/2.96  tff('#skF_2', type, '#skF_2': $i).
% 8.23/2.96  tff('#skF_3', type, '#skF_3': $i).
% 8.23/2.96  tff('#skF_1', type, '#skF_1': $i).
% 8.23/2.96  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.23/2.96  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.23/2.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.23/2.96  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.23/2.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.23/2.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.23/2.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.23/2.96  tff('#skF_4', type, '#skF_4': $i).
% 8.23/2.96  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.23/2.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.23/2.96  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.23/2.96  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.23/2.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.23/2.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.23/2.96  
% 8.44/2.99  tff(f_179, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 8.44/2.99  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.44/2.99  tff(f_137, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.44/2.99  tff(f_89, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 8.44/2.99  tff(f_135, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.44/2.99  tff(f_125, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.44/2.99  tff(f_105, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 8.44/2.99  tff(f_103, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.44/2.99  tff(f_159, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 8.44/2.99  tff(f_73, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.44/2.99  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.44/2.99  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.44/2.99  tff(f_113, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 8.44/2.99  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 8.44/2.99  tff(f_84, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.44/2.99  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 8.44/2.99  tff(f_51, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 8.44/2.99  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 8.44/2.99  tff(f_39, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.44/2.99  tff(f_47, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 8.44/2.99  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.44/2.99  tff(f_85, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 8.44/2.99  tff(c_66, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.44/2.99  tff(c_138, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 8.44/2.99  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.44/2.99  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.44/2.99  tff(c_78, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.44/2.99  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.44/2.99  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.44/2.99  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.44/2.99  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.44/2.99  tff(c_60, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.44/2.99  tff(c_38, plain, (![A_24]: (v2_funct_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.44/2.99  tff(c_82, plain, (![A_24]: (v2_funct_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_38])).
% 8.44/2.99  tff(c_5418, plain, (![C_353, F_355, D_354, B_356, A_352, E_351]: (k1_partfun1(A_352, B_356, C_353, D_354, E_351, F_355)=k5_relat_1(E_351, F_355) | ~m1_subset_1(F_355, k1_zfmisc_1(k2_zfmisc_1(C_353, D_354))) | ~v1_funct_1(F_355) | ~m1_subset_1(E_351, k1_zfmisc_1(k2_zfmisc_1(A_352, B_356))) | ~v1_funct_1(E_351))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.44/2.99  tff(c_5428, plain, (![A_352, B_356, E_351]: (k1_partfun1(A_352, B_356, '#skF_2', '#skF_1', E_351, '#skF_4')=k5_relat_1(E_351, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_351, k1_zfmisc_1(k2_zfmisc_1(A_352, B_356))) | ~v1_funct_1(E_351))), inference(resolution, [status(thm)], [c_70, c_5418])).
% 8.44/2.99  tff(c_5872, plain, (![A_375, B_376, E_377]: (k1_partfun1(A_375, B_376, '#skF_2', '#skF_1', E_377, '#skF_4')=k5_relat_1(E_377, '#skF_4') | ~m1_subset_1(E_377, k1_zfmisc_1(k2_zfmisc_1(A_375, B_376))) | ~v1_funct_1(E_377))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5428])).
% 8.44/2.99  tff(c_5893, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_5872])).
% 8.44/2.99  tff(c_5901, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_5893])).
% 8.44/2.99  tff(c_54, plain, (![A_35, F_40, B_36, C_37, D_38, E_39]: (m1_subset_1(k1_partfun1(A_35, B_36, C_37, D_38, E_39, F_40), k1_zfmisc_1(k2_zfmisc_1(A_35, D_38))) | ~m1_subset_1(F_40, k1_zfmisc_1(k2_zfmisc_1(C_37, D_38))) | ~v1_funct_1(F_40) | ~m1_subset_1(E_39, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_1(E_39))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.44/2.99  tff(c_6657, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5901, c_54])).
% 8.44/2.99  tff(c_6664, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_6657])).
% 8.44/2.99  tff(c_48, plain, (![A_32]: (m1_subset_1(k6_relat_1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.44/2.99  tff(c_81, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_48])).
% 8.44/2.99  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.44/2.99  tff(c_4880, plain, (![D_317, C_318, A_319, B_320]: (D_317=C_318 | ~r2_relset_1(A_319, B_320, C_318, D_317) | ~m1_subset_1(D_317, k1_zfmisc_1(k2_zfmisc_1(A_319, B_320))) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(A_319, B_320))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.44/2.99  tff(c_4890, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_4880])).
% 8.44/2.99  tff(c_4909, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_4890])).
% 8.44/2.99  tff(c_5050, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_4909])).
% 8.44/2.99  tff(c_7270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6664, c_5901, c_5050])).
% 8.44/2.99  tff(c_7271, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_4909])).
% 8.44/2.99  tff(c_8882, plain, (![E_494, A_497, C_498, D_495, B_496]: (k1_xboole_0=C_498 | v2_funct_1(D_495) | ~v2_funct_1(k1_partfun1(A_497, B_496, B_496, C_498, D_495, E_494)) | ~m1_subset_1(E_494, k1_zfmisc_1(k2_zfmisc_1(B_496, C_498))) | ~v1_funct_2(E_494, B_496, C_498) | ~v1_funct_1(E_494) | ~m1_subset_1(D_495, k1_zfmisc_1(k2_zfmisc_1(A_497, B_496))) | ~v1_funct_2(D_495, A_497, B_496) | ~v1_funct_1(D_495))), inference(cnfTransformation, [status(thm)], [f_159])).
% 8.44/2.99  tff(c_8886, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7271, c_8882])).
% 8.44/2.99  tff(c_8890, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_82, c_8886])).
% 8.44/2.99  tff(c_8891, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_138, c_8890])).
% 8.44/2.99  tff(c_26, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.44/2.99  tff(c_168, plain, (![B_71, A_72]: (v1_relat_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.44/2.99  tff(c_177, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_168])).
% 8.44/2.99  tff(c_189, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_177])).
% 8.44/2.99  tff(c_293, plain, (![C_82, B_83, A_84]: (v5_relat_1(C_82, B_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.44/2.99  tff(c_307, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_293])).
% 8.44/2.99  tff(c_554, plain, (![B_106, A_107]: (k2_relat_1(B_106)=A_107 | ~v2_funct_2(B_106, A_107) | ~v5_relat_1(B_106, A_107) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.44/2.99  tff(c_572, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_307, c_554])).
% 8.44/2.99  tff(c_589, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_572])).
% 8.44/2.99  tff(c_604, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_589])).
% 8.44/2.99  tff(c_24, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.44/2.99  tff(c_180, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_168])).
% 8.44/2.99  tff(c_192, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_180])).
% 8.44/2.99  tff(c_32, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.44/2.99  tff(c_84, plain, (![A_23]: (k2_relat_1(k6_partfun1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_32])).
% 8.44/2.99  tff(c_794, plain, (![D_126, C_127, A_128, B_129]: (D_126=C_127 | ~r2_relset_1(A_128, B_129, C_127, D_126) | ~m1_subset_1(D_126, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.44/2.99  tff(c_804, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_794])).
% 8.44/2.99  tff(c_823, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_804])).
% 8.44/2.99  tff(c_1059, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_823])).
% 8.44/2.99  tff(c_3333, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1059])).
% 8.44/2.99  tff(c_3337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_3333])).
% 8.44/2.99  tff(c_3338, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_823])).
% 8.44/2.99  tff(c_3757, plain, (![E_266, A_267, F_270, C_268, D_269, B_271]: (k1_partfun1(A_267, B_271, C_268, D_269, E_266, F_270)=k5_relat_1(E_266, F_270) | ~m1_subset_1(F_270, k1_zfmisc_1(k2_zfmisc_1(C_268, D_269))) | ~v1_funct_1(F_270) | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(A_267, B_271))) | ~v1_funct_1(E_266))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.44/2.99  tff(c_3767, plain, (![A_267, B_271, E_266]: (k1_partfun1(A_267, B_271, '#skF_2', '#skF_1', E_266, '#skF_4')=k5_relat_1(E_266, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(A_267, B_271))) | ~v1_funct_1(E_266))), inference(resolution, [status(thm)], [c_70, c_3757])).
% 8.44/2.99  tff(c_4458, plain, (![A_293, B_294, E_295]: (k1_partfun1(A_293, B_294, '#skF_2', '#skF_1', E_295, '#skF_4')=k5_relat_1(E_295, '#skF_4') | ~m1_subset_1(E_295, k1_zfmisc_1(k2_zfmisc_1(A_293, B_294))) | ~v1_funct_1(E_295))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3767])).
% 8.44/2.99  tff(c_4482, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_4458])).
% 8.44/2.99  tff(c_4490, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3338, c_4482])).
% 8.44/2.99  tff(c_28, plain, (![A_20, B_22]: (r1_tarski(k2_relat_1(k5_relat_1(A_20, B_22)), k2_relat_1(B_22)) | ~v1_relat_1(B_22) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.44/2.99  tff(c_4494, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4490, c_28])).
% 8.44/2.99  tff(c_4498, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_189, c_84, c_4494])).
% 8.44/2.99  tff(c_4, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.44/2.99  tff(c_4502, plain, (k2_relat_1('#skF_4')='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_4498, c_4])).
% 8.44/2.99  tff(c_4503, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_4502])).
% 8.44/2.99  tff(c_4506, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_4503])).
% 8.44/2.99  tff(c_4510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_307, c_4506])).
% 8.44/2.99  tff(c_4511, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_4502])).
% 8.44/2.99  tff(c_330, plain, (![B_87, A_88]: (v5_relat_1(B_87, A_88) | ~r1_tarski(k2_relat_1(B_87), A_88) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.44/2.99  tff(c_345, plain, (![B_87]: (v5_relat_1(B_87, k2_relat_1(B_87)) | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_8, c_330])).
% 8.44/2.99  tff(c_504, plain, (![B_103]: (v2_funct_2(B_103, k2_relat_1(B_103)) | ~v5_relat_1(B_103, k2_relat_1(B_103)) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.44/2.99  tff(c_525, plain, (![B_87]: (v2_funct_2(B_87, k2_relat_1(B_87)) | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_345, c_504])).
% 8.44/2.99  tff(c_4524, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4511, c_525])).
% 8.44/2.99  tff(c_4542, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_4524])).
% 8.44/2.99  tff(c_4544, plain, $false, inference(negUnitSimplification, [status(thm)], [c_604, c_4542])).
% 8.44/2.99  tff(c_4545, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_589])).
% 8.44/2.99  tff(c_22, plain, (![B_17, A_16]: (v5_relat_1(B_17, A_16) | ~r1_tarski(k2_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.44/2.99  tff(c_4580, plain, (![A_16]: (v5_relat_1('#skF_4', A_16) | ~r1_tarski('#skF_1', A_16) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4545, c_22])).
% 8.44/2.99  tff(c_4592, plain, (![A_16]: (v5_relat_1('#skF_4', A_16) | ~r1_tarski('#skF_1', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_4580])).
% 8.44/2.99  tff(c_16, plain, (![A_8, B_9]: (v1_xboole_0(k2_zfmisc_1(A_8, B_9)) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.44/2.99  tff(c_249, plain, (![B_79, A_80]: (v1_xboole_0(B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_80)) | ~v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.44/2.99  tff(c_261, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_249])).
% 8.44/2.99  tff(c_309, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_261])).
% 8.44/2.99  tff(c_317, plain, (~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_309])).
% 8.44/2.99  tff(c_406, plain, (![B_97, A_98]: (r1_tarski(k2_relat_1(B_97), A_98) | ~v5_relat_1(B_97, A_98) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.44/2.99  tff(c_12, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.44/2.99  tff(c_193, plain, (![B_73, A_74]: (~r1_xboole_0(B_73, A_74) | ~r1_tarski(B_73, A_74) | v1_xboole_0(B_73))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.44/2.99  tff(c_197, plain, (![A_5]: (~r1_tarski(A_5, k1_xboole_0) | v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_12, c_193])).
% 8.44/2.99  tff(c_7440, plain, (![B_430]: (v1_xboole_0(k2_relat_1(B_430)) | ~v5_relat_1(B_430, k1_xboole_0) | ~v1_relat_1(B_430))), inference(resolution, [status(thm)], [c_406, c_197])).
% 8.44/2.99  tff(c_7451, plain, (v1_xboole_0('#skF_1') | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4545, c_7440])).
% 8.44/2.99  tff(c_7462, plain, (v1_xboole_0('#skF_1') | ~v5_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_189, c_7451])).
% 8.44/2.99  tff(c_7463, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_317, c_7462])).
% 8.44/2.99  tff(c_7471, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_4592, c_7463])).
% 8.44/2.99  tff(c_8909, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8891, c_7471])).
% 8.44/2.99  tff(c_8948, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_8909])).
% 8.44/2.99  tff(c_8949, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_261])).
% 8.44/2.99  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.44/2.99  tff(c_8957, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8949, c_2])).
% 8.44/2.99  tff(c_98, plain, (![A_63]: (k6_relat_1(A_63)=k6_partfun1(A_63))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.44/2.99  tff(c_34, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.44/2.99  tff(c_104, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_98, c_34])).
% 8.44/2.99  tff(c_117, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_104, c_82])).
% 8.44/2.99  tff(c_8966, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8957, c_117])).
% 8.44/2.99  tff(c_8975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_8966])).
% 8.44/2.99  tff(c_8976, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 8.44/2.99  tff(c_9057, plain, (![B_510, A_511]: (v1_relat_1(B_510) | ~m1_subset_1(B_510, k1_zfmisc_1(A_511)) | ~v1_relat_1(A_511))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.44/2.99  tff(c_9066, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_9057])).
% 8.44/2.99  tff(c_9078, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_9066])).
% 8.44/2.99  tff(c_9315, plain, (![C_533, B_534, A_535]: (v5_relat_1(C_533, B_534) | ~m1_subset_1(C_533, k1_zfmisc_1(k2_zfmisc_1(A_535, B_534))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.44/2.99  tff(c_9330, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_9315])).
% 8.44/2.99  tff(c_9069, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_9057])).
% 8.44/2.99  tff(c_9081, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_9069])).
% 8.44/2.99  tff(c_10257, plain, (![B_601, C_598, F_600, A_597, D_599, E_596]: (k1_partfun1(A_597, B_601, C_598, D_599, E_596, F_600)=k5_relat_1(E_596, F_600) | ~m1_subset_1(F_600, k1_zfmisc_1(k2_zfmisc_1(C_598, D_599))) | ~v1_funct_1(F_600) | ~m1_subset_1(E_596, k1_zfmisc_1(k2_zfmisc_1(A_597, B_601))) | ~v1_funct_1(E_596))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.44/2.99  tff(c_10267, plain, (![A_597, B_601, E_596]: (k1_partfun1(A_597, B_601, '#skF_2', '#skF_1', E_596, '#skF_4')=k5_relat_1(E_596, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_596, k1_zfmisc_1(k2_zfmisc_1(A_597, B_601))) | ~v1_funct_1(E_596))), inference(resolution, [status(thm)], [c_70, c_10257])).
% 8.44/2.99  tff(c_10452, plain, (![A_616, B_617, E_618]: (k1_partfun1(A_616, B_617, '#skF_2', '#skF_1', E_618, '#skF_4')=k5_relat_1(E_618, '#skF_4') | ~m1_subset_1(E_618, k1_zfmisc_1(k2_zfmisc_1(A_616, B_617))) | ~v1_funct_1(E_618))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_10267])).
% 8.44/2.99  tff(c_10473, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_10452])).
% 8.44/2.99  tff(c_10481, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_10473])).
% 8.44/2.99  tff(c_10964, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10481, c_54])).
% 8.44/2.99  tff(c_10968, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_10964])).
% 8.44/2.99  tff(c_9604, plain, (![D_557, C_558, A_559, B_560]: (D_557=C_558 | ~r2_relset_1(A_559, B_560, C_558, D_557) | ~m1_subset_1(D_557, k1_zfmisc_1(k2_zfmisc_1(A_559, B_560))) | ~m1_subset_1(C_558, k1_zfmisc_1(k2_zfmisc_1(A_559, B_560))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.44/2.99  tff(c_9614, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_9604])).
% 8.44/2.99  tff(c_9633, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_9614])).
% 8.44/2.99  tff(c_9790, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_9633])).
% 8.44/2.99  tff(c_12096, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10968, c_10481, c_9790])).
% 8.44/2.99  tff(c_12097, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_9633])).
% 8.44/2.99  tff(c_12600, plain, (![C_699, D_700, A_698, E_697, B_702, F_701]: (k1_partfun1(A_698, B_702, C_699, D_700, E_697, F_701)=k5_relat_1(E_697, F_701) | ~m1_subset_1(F_701, k1_zfmisc_1(k2_zfmisc_1(C_699, D_700))) | ~v1_funct_1(F_701) | ~m1_subset_1(E_697, k1_zfmisc_1(k2_zfmisc_1(A_698, B_702))) | ~v1_funct_1(E_697))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.44/2.99  tff(c_12610, plain, (![A_698, B_702, E_697]: (k1_partfun1(A_698, B_702, '#skF_2', '#skF_1', E_697, '#skF_4')=k5_relat_1(E_697, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_697, k1_zfmisc_1(k2_zfmisc_1(A_698, B_702))) | ~v1_funct_1(E_697))), inference(resolution, [status(thm)], [c_70, c_12600])).
% 8.44/2.99  tff(c_13942, plain, (![A_751, B_752, E_753]: (k1_partfun1(A_751, B_752, '#skF_2', '#skF_1', E_753, '#skF_4')=k5_relat_1(E_753, '#skF_4') | ~m1_subset_1(E_753, k1_zfmisc_1(k2_zfmisc_1(A_751, B_752))) | ~v1_funct_1(E_753))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_12610])).
% 8.44/2.99  tff(c_13972, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_13942])).
% 8.44/2.99  tff(c_13986, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_12097, c_13972])).
% 8.44/2.99  tff(c_13990, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13986, c_28])).
% 8.44/2.99  tff(c_13994, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9081, c_9078, c_84, c_13990])).
% 8.44/2.99  tff(c_13998, plain, (k2_relat_1('#skF_4')='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_13994, c_4])).
% 8.44/2.99  tff(c_13999, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_13998])).
% 8.44/2.99  tff(c_14002, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_13999])).
% 8.44/2.99  tff(c_14006, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9078, c_9330, c_14002])).
% 8.44/2.99  tff(c_14007, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_13998])).
% 8.44/2.99  tff(c_9231, plain, (![B_522, A_523]: (v5_relat_1(B_522, A_523) | ~r1_tarski(k2_relat_1(B_522), A_523) | ~v1_relat_1(B_522))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.44/2.99  tff(c_9250, plain, (![B_522]: (v5_relat_1(B_522, k2_relat_1(B_522)) | ~v1_relat_1(B_522))), inference(resolution, [status(thm)], [c_8, c_9231])).
% 8.44/2.99  tff(c_9392, plain, (![B_538]: (v2_funct_2(B_538, k2_relat_1(B_538)) | ~v5_relat_1(B_538, k2_relat_1(B_538)) | ~v1_relat_1(B_538))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.44/2.99  tff(c_9406, plain, (![B_522]: (v2_funct_2(B_522, k2_relat_1(B_522)) | ~v1_relat_1(B_522))), inference(resolution, [status(thm)], [c_9250, c_9392])).
% 8.44/2.99  tff(c_14020, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14007, c_9406])).
% 8.44/2.99  tff(c_14038, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9078, c_14020])).
% 8.44/2.99  tff(c_14040, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8976, c_14038])).
% 8.44/2.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.44/2.99  
% 8.44/2.99  Inference rules
% 8.44/2.99  ----------------------
% 8.44/2.99  #Ref     : 0
% 8.44/2.99  #Sup     : 3275
% 8.44/2.99  #Fact    : 0
% 8.44/2.99  #Define  : 0
% 8.44/2.99  #Split   : 22
% 8.44/2.99  #Chain   : 0
% 8.44/2.99  #Close   : 0
% 8.44/2.99  
% 8.44/2.99  Ordering : KBO
% 8.44/2.99  
% 8.44/2.99  Simplification rules
% 8.44/2.99  ----------------------
% 8.44/2.99  #Subsume      : 321
% 8.44/2.99  #Demod        : 3498
% 8.44/2.99  #Tautology    : 1865
% 8.44/2.99  #SimpNegUnit  : 10
% 8.44/2.99  #BackRed      : 91
% 8.44/2.99  
% 8.44/2.99  #Partial instantiations: 0
% 8.44/2.99  #Strategies tried      : 1
% 8.44/2.99  
% 8.44/2.99  Timing (in seconds)
% 8.44/2.99  ----------------------
% 8.44/3.00  Preprocessing        : 0.36
% 8.44/3.00  Parsing              : 0.19
% 8.44/3.00  CNF conversion       : 0.03
% 8.44/3.00  Main loop            : 1.85
% 8.44/3.00  Inferencing          : 0.55
% 8.44/3.00  Reduction            : 0.72
% 8.44/3.00  Demodulation         : 0.53
% 8.44/3.00  BG Simplification    : 0.06
% 8.44/3.00  Subsumption          : 0.38
% 8.44/3.00  Abstraction          : 0.08
% 8.44/3.00  MUC search           : 0.00
% 8.44/3.00  Cooper               : 0.00
% 8.44/3.00  Total                : 2.26
% 8.44/3.00  Index Insertion      : 0.00
% 8.44/3.00  Index Deletion       : 0.00
% 8.44/3.00  Index Matching       : 0.00
% 8.44/3.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
