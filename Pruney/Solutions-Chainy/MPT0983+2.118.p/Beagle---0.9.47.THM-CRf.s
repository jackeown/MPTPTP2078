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
% DateTime   : Thu Dec  3 10:12:18 EST 2020

% Result     : Theorem 8.15s
% Output     : CNFRefutation 8.35s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 528 expanded)
%              Number of leaves         :   51 ( 202 expanded)
%              Depth                    :   15
%              Number of atoms          :  358 (1571 expanded)
%              Number of equality atoms :   60 ( 137 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_87,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_121,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_125,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_101,axiom,(
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

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_109,axiom,(
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

tff(f_135,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

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

tff(c_137,plain,(
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

tff(c_36,plain,(
    ! [A_24] : v2_funct_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_81,plain,(
    ! [A_24] : v2_funct_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_36])).

tff(c_50,plain,(
    ! [D_37,A_34,F_39,B_35,C_36,E_38] :
      ( m1_subset_1(k1_partfun1(A_34,B_35,C_36,D_37,E_38,F_39),k1_zfmisc_1(k2_zfmisc_1(A_34,D_37)))
      | ~ m1_subset_1(F_39,k1_zfmisc_1(k2_zfmisc_1(C_36,D_37)))
      | ~ v1_funct_1(F_39)
      | ~ m1_subset_1(E_38,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_1(E_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_56,plain,(
    ! [A_40] : m1_subset_1(k6_partfun1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_68,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_4752,plain,(
    ! [D_311,C_312,A_313,B_314] :
      ( D_311 = C_312
      | ~ r2_relset_1(A_313,B_314,C_312,D_311)
      | ~ m1_subset_1(D_311,k1_zfmisc_1(k2_zfmisc_1(A_313,B_314)))
      | ~ m1_subset_1(C_312,k1_zfmisc_1(k2_zfmisc_1(A_313,B_314))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4762,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_4752])).

tff(c_4781,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4762])).

tff(c_4907,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4781])).

tff(c_7271,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_4907])).

tff(c_7275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_7271])).

tff(c_7276,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4781])).

tff(c_8663,plain,(
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

tff(c_8665,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7276,c_8663])).

tff(c_8667,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_81,c_8665])).

tff(c_8668,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_8667])).

tff(c_26,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_167,plain,(
    ! [B_71,A_72] :
      ( v1_relat_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_179,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_167])).

tff(c_191,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_179])).

tff(c_391,plain,(
    ! [C_91,B_92,A_93] :
      ( v5_relat_1(C_91,B_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_406,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_391])).

tff(c_620,plain,(
    ! [B_110,A_111] :
      ( k2_relat_1(B_110) = A_111
      | ~ v2_funct_2(B_110,A_111)
      | ~ v5_relat_1(B_110,A_111)
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_632,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_406,c_620])).

tff(c_646,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_632])).

tff(c_663,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_646])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_176,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_167])).

tff(c_188,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_176])).

tff(c_32,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_82,plain,(
    ! [A_23] : k2_relat_1(k6_partfun1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_32])).

tff(c_1505,plain,(
    ! [C_171,A_170,F_173,D_172,B_174,E_169] :
      ( k1_partfun1(A_170,B_174,C_171,D_172,E_169,F_173) = k5_relat_1(E_169,F_173)
      | ~ m1_subset_1(F_173,k1_zfmisc_1(k2_zfmisc_1(C_171,D_172)))
      | ~ v1_funct_1(F_173)
      | ~ m1_subset_1(E_169,k1_zfmisc_1(k2_zfmisc_1(A_170,B_174)))
      | ~ v1_funct_1(E_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1517,plain,(
    ! [A_170,B_174,E_169] :
      ( k1_partfun1(A_170,B_174,'#skF_2','#skF_1',E_169,'#skF_4') = k5_relat_1(E_169,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_169,k1_zfmisc_1(k2_zfmisc_1(A_170,B_174)))
      | ~ v1_funct_1(E_169) ) ),
    inference(resolution,[status(thm)],[c_70,c_1505])).

tff(c_1906,plain,(
    ! [A_191,B_192,E_193] :
      ( k1_partfun1(A_191,B_192,'#skF_2','#skF_1',E_193,'#skF_4') = k5_relat_1(E_193,'#skF_4')
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192)))
      | ~ v1_funct_1(E_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1517])).

tff(c_1924,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_1906])).

tff(c_1932,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1924])).

tff(c_2532,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1932,c_50])).

tff(c_2539,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_2532])).

tff(c_954,plain,(
    ! [D_131,C_132,A_133,B_134] :
      ( D_131 = C_132
      | ~ r2_relset_1(A_133,B_134,C_132,D_131)
      | ~ m1_subset_1(D_131,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134)))
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_964,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_954])).

tff(c_983,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_964])).

tff(c_1013,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_983])).

tff(c_3311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2539,c_1932,c_1013])).

tff(c_3312,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_983])).

tff(c_3851,plain,(
    ! [E_266,A_267,F_270,C_268,D_269,B_271] :
      ( k1_partfun1(A_267,B_271,C_268,D_269,E_266,F_270) = k5_relat_1(E_266,F_270)
      | ~ m1_subset_1(F_270,k1_zfmisc_1(k2_zfmisc_1(C_268,D_269)))
      | ~ v1_funct_1(F_270)
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(A_267,B_271)))
      | ~ v1_funct_1(E_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3863,plain,(
    ! [A_267,B_271,E_266] :
      ( k1_partfun1(A_267,B_271,'#skF_2','#skF_1',E_266,'#skF_4') = k5_relat_1(E_266,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(A_267,B_271)))
      | ~ v1_funct_1(E_266) ) ),
    inference(resolution,[status(thm)],[c_70,c_3851])).

tff(c_4434,plain,(
    ! [A_290,B_291,E_292] :
      ( k1_partfun1(A_290,B_291,'#skF_2','#skF_1',E_292,'#skF_4') = k5_relat_1(E_292,'#skF_4')
      | ~ m1_subset_1(E_292,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291)))
      | ~ v1_funct_1(E_292) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3863])).

tff(c_4452,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_4434])).

tff(c_4460,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3312,c_4452])).

tff(c_28,plain,(
    ! [A_20,B_22] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_20,B_22)),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4467,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4460,c_28])).

tff(c_4471,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_191,c_82,c_4467])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4475,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_4471,c_4])).

tff(c_4476,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4475])).

tff(c_4479,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_4476])).

tff(c_4483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_406,c_4479])).

tff(c_4484,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4475])).

tff(c_524,plain,(
    ! [B_101,A_102] :
      ( v5_relat_1(B_101,A_102)
      | ~ r1_tarski(k2_relat_1(B_101),A_102)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_543,plain,(
    ! [B_101] :
      ( v5_relat_1(B_101,k2_relat_1(B_101))
      | ~ v1_relat_1(B_101) ) ),
    inference(resolution,[status(thm)],[c_8,c_524])).

tff(c_568,plain,(
    ! [B_106] :
      ( v2_funct_2(B_106,k2_relat_1(B_106))
      | ~ v5_relat_1(B_106,k2_relat_1(B_106))
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_582,plain,(
    ! [B_101] :
      ( v2_funct_2(B_101,k2_relat_1(B_101))
      | ~ v1_relat_1(B_101) ) ),
    inference(resolution,[status(thm)],[c_543,c_568])).

tff(c_4497,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4484,c_582])).

tff(c_4515,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_4497])).

tff(c_4517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_663,c_4515])).

tff(c_4518,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_646])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( v5_relat_1(B_17,A_16)
      | ~ r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4541,plain,(
    ! [A_16] :
      ( v5_relat_1('#skF_4',A_16)
      | ~ r1_tarski('#skF_1',A_16)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4518,c_22])).

tff(c_4552,plain,(
    ! [A_16] :
      ( v5_relat_1('#skF_4',A_16)
      | ~ r1_tarski('#skF_1',A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_4541])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( v1_xboole_0(k2_zfmisc_1(A_8,B_9))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_196,plain,(
    ! [B_74,A_75] :
      ( v1_xboole_0(B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75))
      | ~ v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_211,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_196])).

tff(c_213,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_217,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_213])).

tff(c_411,plain,(
    ! [B_95,A_96] :
      ( r1_tarski(k2_relat_1(B_95),A_96)
      | ~ v5_relat_1(B_95,A_96)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_263,plain,(
    ! [B_79,A_80] :
      ( ~ r1_xboole_0(B_79,A_80)
      | ~ r1_tarski(B_79,A_80)
      | v1_xboole_0(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_267,plain,(
    ! [A_5] :
      ( ~ r1_tarski(A_5,k1_xboole_0)
      | v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_263])).

tff(c_7617,plain,(
    ! [B_444] :
      ( v1_xboole_0(k2_relat_1(B_444))
      | ~ v5_relat_1(B_444,k1_xboole_0)
      | ~ v1_relat_1(B_444) ) ),
    inference(resolution,[status(thm)],[c_411,c_267])).

tff(c_7628,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v5_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4518,c_7617])).

tff(c_7639,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_7628])).

tff(c_7640,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_7639])).

tff(c_7671,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4552,c_7640])).

tff(c_8683,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8668,c_7671])).

tff(c_8725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8683])).

tff(c_8726,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8734,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8726,c_2])).

tff(c_95,plain,(
    ! [A_62] : k6_relat_1(A_62) = k6_partfun1(A_62) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_34,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_101,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_34])).

tff(c_112,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_81])).

tff(c_8741,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8734,c_112])).

tff(c_8749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_8741])).

tff(c_8750,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_8804,plain,(
    ! [B_508,A_509] :
      ( v1_relat_1(B_508)
      | ~ m1_subset_1(B_508,k1_zfmisc_1(A_509))
      | ~ v1_relat_1(A_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8816,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_8804])).

tff(c_8828,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_8816])).

tff(c_8909,plain,(
    ! [C_517,B_518,A_519] :
      ( v5_relat_1(C_517,B_518)
      | ~ m1_subset_1(C_517,k1_zfmisc_1(k2_zfmisc_1(A_519,B_518))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8924,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_8909])).

tff(c_8813,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_8804])).

tff(c_8825,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_8813])).

tff(c_9773,plain,(
    ! [C_587,B_590,A_586,E_585,F_589,D_588] :
      ( k1_partfun1(A_586,B_590,C_587,D_588,E_585,F_589) = k5_relat_1(E_585,F_589)
      | ~ m1_subset_1(F_589,k1_zfmisc_1(k2_zfmisc_1(C_587,D_588)))
      | ~ v1_funct_1(F_589)
      | ~ m1_subset_1(E_585,k1_zfmisc_1(k2_zfmisc_1(A_586,B_590)))
      | ~ v1_funct_1(E_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_9783,plain,(
    ! [A_586,B_590,E_585] :
      ( k1_partfun1(A_586,B_590,'#skF_2','#skF_1',E_585,'#skF_4') = k5_relat_1(E_585,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_585,k1_zfmisc_1(k2_zfmisc_1(A_586,B_590)))
      | ~ v1_funct_1(E_585) ) ),
    inference(resolution,[status(thm)],[c_70,c_9773])).

tff(c_11241,plain,(
    ! [A_653,B_654,E_655] :
      ( k1_partfun1(A_653,B_654,'#skF_2','#skF_1',E_655,'#skF_4') = k5_relat_1(E_655,'#skF_4')
      | ~ m1_subset_1(E_655,k1_zfmisc_1(k2_zfmisc_1(A_653,B_654)))
      | ~ v1_funct_1(E_655) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_9783])).

tff(c_11268,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_11241])).

tff(c_11282,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_11268])).

tff(c_11802,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11282,c_50])).

tff(c_11808,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_11802])).

tff(c_9324,plain,(
    ! [D_554,C_555,A_556,B_557] :
      ( D_554 = C_555
      | ~ r2_relset_1(A_556,B_557,C_555,D_554)
      | ~ m1_subset_1(D_554,k1_zfmisc_1(k2_zfmisc_1(A_556,B_557)))
      | ~ m1_subset_1(C_555,k1_zfmisc_1(k2_zfmisc_1(A_556,B_557))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_9330,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_9324])).

tff(c_9341,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_9330])).

tff(c_12341,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11808,c_11282,c_11282,c_9341])).

tff(c_12363,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12341,c_28])).

tff(c_12371,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8825,c_8828,c_82,c_12363])).

tff(c_8990,plain,(
    ! [B_529,A_530] :
      ( r1_tarski(k2_relat_1(B_529),A_530)
      | ~ v5_relat_1(B_529,A_530)
      | ~ v1_relat_1(B_529) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_9013,plain,(
    ! [B_529,A_530] :
      ( k2_relat_1(B_529) = A_530
      | ~ r1_tarski(A_530,k2_relat_1(B_529))
      | ~ v5_relat_1(B_529,A_530)
      | ~ v1_relat_1(B_529) ) ),
    inference(resolution,[status(thm)],[c_8990,c_4])).

tff(c_12375,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12371,c_9013])).

tff(c_12380,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8828,c_8924,c_12375])).

tff(c_8939,plain,(
    ! [B_521,A_522] :
      ( v5_relat_1(B_521,A_522)
      | ~ r1_tarski(k2_relat_1(B_521),A_522)
      | ~ v1_relat_1(B_521) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8954,plain,(
    ! [B_521] :
      ( v5_relat_1(B_521,k2_relat_1(B_521))
      | ~ v1_relat_1(B_521) ) ),
    inference(resolution,[status(thm)],[c_8,c_8939])).

tff(c_9058,plain,(
    ! [B_536] :
      ( v2_funct_2(B_536,k2_relat_1(B_536))
      | ~ v5_relat_1(B_536,k2_relat_1(B_536))
      | ~ v1_relat_1(B_536) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_9079,plain,(
    ! [B_521] :
      ( v2_funct_2(B_521,k2_relat_1(B_521))
      | ~ v1_relat_1(B_521) ) ),
    inference(resolution,[status(thm)],[c_8954,c_9058])).

tff(c_12399,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12380,c_9079])).

tff(c_12424,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8828,c_12399])).

tff(c_12426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8750,c_12424])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.15/2.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.15/2.86  
% 8.15/2.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.15/2.87  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.15/2.87  
% 8.15/2.87  %Foreground sorts:
% 8.15/2.87  
% 8.15/2.87  
% 8.15/2.87  %Background operators:
% 8.15/2.87  
% 8.15/2.87  
% 8.15/2.87  %Foreground operators:
% 8.15/2.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.15/2.87  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.15/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.15/2.87  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.15/2.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.15/2.87  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.15/2.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.15/2.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.15/2.87  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.15/2.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.15/2.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.15/2.87  tff('#skF_2', type, '#skF_2': $i).
% 8.15/2.87  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.15/2.87  tff('#skF_3', type, '#skF_3': $i).
% 8.15/2.87  tff('#skF_1', type, '#skF_1': $i).
% 8.15/2.87  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.15/2.87  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.15/2.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.15/2.87  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.15/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.15/2.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.15/2.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.15/2.87  tff('#skF_4', type, '#skF_4': $i).
% 8.15/2.87  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.15/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.15/2.87  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.15/2.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.15/2.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.15/2.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.15/2.87  
% 8.35/2.89  tff(f_179, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 8.35/2.89  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.35/2.89  tff(f_137, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.35/2.89  tff(f_87, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 8.35/2.89  tff(f_121, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.35/2.89  tff(f_125, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 8.35/2.89  tff(f_101, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.35/2.89  tff(f_159, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 8.35/2.89  tff(f_73, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.35/2.89  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.35/2.89  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.35/2.89  tff(f_109, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 8.35/2.89  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 8.35/2.89  tff(f_84, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.35/2.89  tff(f_135, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.35/2.89  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 8.35/2.89  tff(f_51, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 8.35/2.89  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 8.35/2.89  tff(f_39, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.35/2.89  tff(f_47, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 8.35/2.89  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.35/2.89  tff(f_85, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 8.35/2.89  tff(c_66, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.35/2.89  tff(c_137, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 8.35/2.89  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.35/2.89  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.35/2.89  tff(c_78, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.35/2.89  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.35/2.89  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.35/2.89  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.35/2.89  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.35/2.89  tff(c_60, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.35/2.89  tff(c_36, plain, (![A_24]: (v2_funct_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.35/2.89  tff(c_81, plain, (![A_24]: (v2_funct_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_36])).
% 8.35/2.89  tff(c_50, plain, (![D_37, A_34, F_39, B_35, C_36, E_38]: (m1_subset_1(k1_partfun1(A_34, B_35, C_36, D_37, E_38, F_39), k1_zfmisc_1(k2_zfmisc_1(A_34, D_37))) | ~m1_subset_1(F_39, k1_zfmisc_1(k2_zfmisc_1(C_36, D_37))) | ~v1_funct_1(F_39) | ~m1_subset_1(E_38, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_1(E_38))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.35/2.89  tff(c_56, plain, (![A_40]: (m1_subset_1(k6_partfun1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.35/2.89  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.35/2.89  tff(c_4752, plain, (![D_311, C_312, A_313, B_314]: (D_311=C_312 | ~r2_relset_1(A_313, B_314, C_312, D_311) | ~m1_subset_1(D_311, k1_zfmisc_1(k2_zfmisc_1(A_313, B_314))) | ~m1_subset_1(C_312, k1_zfmisc_1(k2_zfmisc_1(A_313, B_314))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.35/2.89  tff(c_4762, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_4752])).
% 8.35/2.89  tff(c_4781, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4762])).
% 8.35/2.89  tff(c_4907, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_4781])).
% 8.35/2.89  tff(c_7271, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_4907])).
% 8.35/2.89  tff(c_7275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_7271])).
% 8.35/2.89  tff(c_7276, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_4781])).
% 8.35/2.89  tff(c_8663, plain, (![E_494, A_497, C_498, D_495, B_496]: (k1_xboole_0=C_498 | v2_funct_1(D_495) | ~v2_funct_1(k1_partfun1(A_497, B_496, B_496, C_498, D_495, E_494)) | ~m1_subset_1(E_494, k1_zfmisc_1(k2_zfmisc_1(B_496, C_498))) | ~v1_funct_2(E_494, B_496, C_498) | ~v1_funct_1(E_494) | ~m1_subset_1(D_495, k1_zfmisc_1(k2_zfmisc_1(A_497, B_496))) | ~v1_funct_2(D_495, A_497, B_496) | ~v1_funct_1(D_495))), inference(cnfTransformation, [status(thm)], [f_159])).
% 8.35/2.89  tff(c_8665, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7276, c_8663])).
% 8.35/2.89  tff(c_8667, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_81, c_8665])).
% 8.35/2.89  tff(c_8668, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_137, c_8667])).
% 8.35/2.89  tff(c_26, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.35/2.89  tff(c_167, plain, (![B_71, A_72]: (v1_relat_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.35/2.89  tff(c_179, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_167])).
% 8.35/2.89  tff(c_191, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_179])).
% 8.35/2.89  tff(c_391, plain, (![C_91, B_92, A_93]: (v5_relat_1(C_91, B_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.35/2.89  tff(c_406, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_391])).
% 8.35/2.89  tff(c_620, plain, (![B_110, A_111]: (k2_relat_1(B_110)=A_111 | ~v2_funct_2(B_110, A_111) | ~v5_relat_1(B_110, A_111) | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.35/2.89  tff(c_632, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_406, c_620])).
% 8.35/2.89  tff(c_646, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_191, c_632])).
% 8.35/2.89  tff(c_663, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_646])).
% 8.35/2.89  tff(c_24, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.35/2.89  tff(c_176, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_167])).
% 8.35/2.89  tff(c_188, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_176])).
% 8.35/2.89  tff(c_32, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.35/2.89  tff(c_82, plain, (![A_23]: (k2_relat_1(k6_partfun1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_32])).
% 8.35/2.89  tff(c_1505, plain, (![C_171, A_170, F_173, D_172, B_174, E_169]: (k1_partfun1(A_170, B_174, C_171, D_172, E_169, F_173)=k5_relat_1(E_169, F_173) | ~m1_subset_1(F_173, k1_zfmisc_1(k2_zfmisc_1(C_171, D_172))) | ~v1_funct_1(F_173) | ~m1_subset_1(E_169, k1_zfmisc_1(k2_zfmisc_1(A_170, B_174))) | ~v1_funct_1(E_169))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.35/2.89  tff(c_1517, plain, (![A_170, B_174, E_169]: (k1_partfun1(A_170, B_174, '#skF_2', '#skF_1', E_169, '#skF_4')=k5_relat_1(E_169, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_169, k1_zfmisc_1(k2_zfmisc_1(A_170, B_174))) | ~v1_funct_1(E_169))), inference(resolution, [status(thm)], [c_70, c_1505])).
% 8.35/2.89  tff(c_1906, plain, (![A_191, B_192, E_193]: (k1_partfun1(A_191, B_192, '#skF_2', '#skF_1', E_193, '#skF_4')=k5_relat_1(E_193, '#skF_4') | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))) | ~v1_funct_1(E_193))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1517])).
% 8.35/2.89  tff(c_1924, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_1906])).
% 8.35/2.89  tff(c_1932, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1924])).
% 8.35/2.89  tff(c_2532, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1932, c_50])).
% 8.35/2.89  tff(c_2539, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_2532])).
% 8.35/2.89  tff(c_954, plain, (![D_131, C_132, A_133, B_134]: (D_131=C_132 | ~r2_relset_1(A_133, B_134, C_132, D_131) | ~m1_subset_1(D_131, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.35/2.89  tff(c_964, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_954])).
% 8.35/2.89  tff(c_983, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_964])).
% 8.35/2.89  tff(c_1013, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_983])).
% 8.35/2.89  tff(c_3311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2539, c_1932, c_1013])).
% 8.35/2.89  tff(c_3312, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_983])).
% 8.35/2.89  tff(c_3851, plain, (![E_266, A_267, F_270, C_268, D_269, B_271]: (k1_partfun1(A_267, B_271, C_268, D_269, E_266, F_270)=k5_relat_1(E_266, F_270) | ~m1_subset_1(F_270, k1_zfmisc_1(k2_zfmisc_1(C_268, D_269))) | ~v1_funct_1(F_270) | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(A_267, B_271))) | ~v1_funct_1(E_266))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.35/2.89  tff(c_3863, plain, (![A_267, B_271, E_266]: (k1_partfun1(A_267, B_271, '#skF_2', '#skF_1', E_266, '#skF_4')=k5_relat_1(E_266, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(A_267, B_271))) | ~v1_funct_1(E_266))), inference(resolution, [status(thm)], [c_70, c_3851])).
% 8.35/2.89  tff(c_4434, plain, (![A_290, B_291, E_292]: (k1_partfun1(A_290, B_291, '#skF_2', '#skF_1', E_292, '#skF_4')=k5_relat_1(E_292, '#skF_4') | ~m1_subset_1(E_292, k1_zfmisc_1(k2_zfmisc_1(A_290, B_291))) | ~v1_funct_1(E_292))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3863])).
% 8.35/2.89  tff(c_4452, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_4434])).
% 8.35/2.89  tff(c_4460, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3312, c_4452])).
% 8.35/2.89  tff(c_28, plain, (![A_20, B_22]: (r1_tarski(k2_relat_1(k5_relat_1(A_20, B_22)), k2_relat_1(B_22)) | ~v1_relat_1(B_22) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.35/2.89  tff(c_4467, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4460, c_28])).
% 8.35/2.89  tff(c_4471, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_191, c_82, c_4467])).
% 8.35/2.89  tff(c_4, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.35/2.89  tff(c_4475, plain, (k2_relat_1('#skF_4')='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_4471, c_4])).
% 8.35/2.89  tff(c_4476, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_4475])).
% 8.35/2.89  tff(c_4479, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_4476])).
% 8.35/2.89  tff(c_4483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_191, c_406, c_4479])).
% 8.35/2.89  tff(c_4484, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_4475])).
% 8.35/2.89  tff(c_524, plain, (![B_101, A_102]: (v5_relat_1(B_101, A_102) | ~r1_tarski(k2_relat_1(B_101), A_102) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.35/2.89  tff(c_543, plain, (![B_101]: (v5_relat_1(B_101, k2_relat_1(B_101)) | ~v1_relat_1(B_101))), inference(resolution, [status(thm)], [c_8, c_524])).
% 8.35/2.89  tff(c_568, plain, (![B_106]: (v2_funct_2(B_106, k2_relat_1(B_106)) | ~v5_relat_1(B_106, k2_relat_1(B_106)) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.35/2.89  tff(c_582, plain, (![B_101]: (v2_funct_2(B_101, k2_relat_1(B_101)) | ~v1_relat_1(B_101))), inference(resolution, [status(thm)], [c_543, c_568])).
% 8.35/2.89  tff(c_4497, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4484, c_582])).
% 8.35/2.89  tff(c_4515, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_191, c_4497])).
% 8.35/2.89  tff(c_4517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_663, c_4515])).
% 8.35/2.89  tff(c_4518, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_646])).
% 8.35/2.89  tff(c_22, plain, (![B_17, A_16]: (v5_relat_1(B_17, A_16) | ~r1_tarski(k2_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.35/2.89  tff(c_4541, plain, (![A_16]: (v5_relat_1('#skF_4', A_16) | ~r1_tarski('#skF_1', A_16) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4518, c_22])).
% 8.35/2.89  tff(c_4552, plain, (![A_16]: (v5_relat_1('#skF_4', A_16) | ~r1_tarski('#skF_1', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_4541])).
% 8.35/2.89  tff(c_16, plain, (![A_8, B_9]: (v1_xboole_0(k2_zfmisc_1(A_8, B_9)) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.35/2.89  tff(c_196, plain, (![B_74, A_75]: (v1_xboole_0(B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)) | ~v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.35/2.89  tff(c_211, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_196])).
% 8.35/2.89  tff(c_213, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_211])).
% 8.35/2.89  tff(c_217, plain, (~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_213])).
% 8.35/2.89  tff(c_411, plain, (![B_95, A_96]: (r1_tarski(k2_relat_1(B_95), A_96) | ~v5_relat_1(B_95, A_96) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.35/2.89  tff(c_12, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.35/2.89  tff(c_263, plain, (![B_79, A_80]: (~r1_xboole_0(B_79, A_80) | ~r1_tarski(B_79, A_80) | v1_xboole_0(B_79))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.35/2.89  tff(c_267, plain, (![A_5]: (~r1_tarski(A_5, k1_xboole_0) | v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_12, c_263])).
% 8.35/2.89  tff(c_7617, plain, (![B_444]: (v1_xboole_0(k2_relat_1(B_444)) | ~v5_relat_1(B_444, k1_xboole_0) | ~v1_relat_1(B_444))), inference(resolution, [status(thm)], [c_411, c_267])).
% 8.35/2.89  tff(c_7628, plain, (v1_xboole_0('#skF_1') | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4518, c_7617])).
% 8.35/2.89  tff(c_7639, plain, (v1_xboole_0('#skF_1') | ~v5_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_191, c_7628])).
% 8.35/2.89  tff(c_7640, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_217, c_7639])).
% 8.35/2.89  tff(c_7671, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_4552, c_7640])).
% 8.35/2.89  tff(c_8683, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8668, c_7671])).
% 8.35/2.89  tff(c_8725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_8683])).
% 8.35/2.89  tff(c_8726, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_211])).
% 8.35/2.89  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.35/2.89  tff(c_8734, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8726, c_2])).
% 8.35/2.89  tff(c_95, plain, (![A_62]: (k6_relat_1(A_62)=k6_partfun1(A_62))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.35/2.89  tff(c_34, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.35/2.89  tff(c_101, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_95, c_34])).
% 8.35/2.89  tff(c_112, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_101, c_81])).
% 8.35/2.89  tff(c_8741, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8734, c_112])).
% 8.35/2.89  tff(c_8749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_8741])).
% 8.35/2.89  tff(c_8750, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 8.35/2.89  tff(c_8804, plain, (![B_508, A_509]: (v1_relat_1(B_508) | ~m1_subset_1(B_508, k1_zfmisc_1(A_509)) | ~v1_relat_1(A_509))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.35/2.89  tff(c_8816, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_8804])).
% 8.35/2.89  tff(c_8828, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_8816])).
% 8.35/2.89  tff(c_8909, plain, (![C_517, B_518, A_519]: (v5_relat_1(C_517, B_518) | ~m1_subset_1(C_517, k1_zfmisc_1(k2_zfmisc_1(A_519, B_518))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.35/2.89  tff(c_8924, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_8909])).
% 8.35/2.89  tff(c_8813, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_8804])).
% 8.35/2.89  tff(c_8825, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_8813])).
% 8.35/2.89  tff(c_9773, plain, (![C_587, B_590, A_586, E_585, F_589, D_588]: (k1_partfun1(A_586, B_590, C_587, D_588, E_585, F_589)=k5_relat_1(E_585, F_589) | ~m1_subset_1(F_589, k1_zfmisc_1(k2_zfmisc_1(C_587, D_588))) | ~v1_funct_1(F_589) | ~m1_subset_1(E_585, k1_zfmisc_1(k2_zfmisc_1(A_586, B_590))) | ~v1_funct_1(E_585))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.35/2.89  tff(c_9783, plain, (![A_586, B_590, E_585]: (k1_partfun1(A_586, B_590, '#skF_2', '#skF_1', E_585, '#skF_4')=k5_relat_1(E_585, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_585, k1_zfmisc_1(k2_zfmisc_1(A_586, B_590))) | ~v1_funct_1(E_585))), inference(resolution, [status(thm)], [c_70, c_9773])).
% 8.35/2.89  tff(c_11241, plain, (![A_653, B_654, E_655]: (k1_partfun1(A_653, B_654, '#skF_2', '#skF_1', E_655, '#skF_4')=k5_relat_1(E_655, '#skF_4') | ~m1_subset_1(E_655, k1_zfmisc_1(k2_zfmisc_1(A_653, B_654))) | ~v1_funct_1(E_655))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_9783])).
% 8.35/2.89  tff(c_11268, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_11241])).
% 8.35/2.89  tff(c_11282, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_11268])).
% 8.35/2.89  tff(c_11802, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11282, c_50])).
% 8.35/2.89  tff(c_11808, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_11802])).
% 8.35/2.89  tff(c_9324, plain, (![D_554, C_555, A_556, B_557]: (D_554=C_555 | ~r2_relset_1(A_556, B_557, C_555, D_554) | ~m1_subset_1(D_554, k1_zfmisc_1(k2_zfmisc_1(A_556, B_557))) | ~m1_subset_1(C_555, k1_zfmisc_1(k2_zfmisc_1(A_556, B_557))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.35/2.89  tff(c_9330, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_9324])).
% 8.35/2.89  tff(c_9341, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_9330])).
% 8.35/2.89  tff(c_12341, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11808, c_11282, c_11282, c_9341])).
% 8.35/2.89  tff(c_12363, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12341, c_28])).
% 8.35/2.89  tff(c_12371, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8825, c_8828, c_82, c_12363])).
% 8.35/2.89  tff(c_8990, plain, (![B_529, A_530]: (r1_tarski(k2_relat_1(B_529), A_530) | ~v5_relat_1(B_529, A_530) | ~v1_relat_1(B_529))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.35/2.89  tff(c_9013, plain, (![B_529, A_530]: (k2_relat_1(B_529)=A_530 | ~r1_tarski(A_530, k2_relat_1(B_529)) | ~v5_relat_1(B_529, A_530) | ~v1_relat_1(B_529))), inference(resolution, [status(thm)], [c_8990, c_4])).
% 8.35/2.89  tff(c_12375, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12371, c_9013])).
% 8.35/2.89  tff(c_12380, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8828, c_8924, c_12375])).
% 8.35/2.89  tff(c_8939, plain, (![B_521, A_522]: (v5_relat_1(B_521, A_522) | ~r1_tarski(k2_relat_1(B_521), A_522) | ~v1_relat_1(B_521))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.35/2.89  tff(c_8954, plain, (![B_521]: (v5_relat_1(B_521, k2_relat_1(B_521)) | ~v1_relat_1(B_521))), inference(resolution, [status(thm)], [c_8, c_8939])).
% 8.35/2.89  tff(c_9058, plain, (![B_536]: (v2_funct_2(B_536, k2_relat_1(B_536)) | ~v5_relat_1(B_536, k2_relat_1(B_536)) | ~v1_relat_1(B_536))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.35/2.89  tff(c_9079, plain, (![B_521]: (v2_funct_2(B_521, k2_relat_1(B_521)) | ~v1_relat_1(B_521))), inference(resolution, [status(thm)], [c_8954, c_9058])).
% 8.35/2.89  tff(c_12399, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12380, c_9079])).
% 8.35/2.89  tff(c_12424, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8828, c_12399])).
% 8.35/2.89  tff(c_12426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8750, c_12424])).
% 8.35/2.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.35/2.89  
% 8.35/2.89  Inference rules
% 8.35/2.89  ----------------------
% 8.35/2.89  #Ref     : 0
% 8.35/2.89  #Sup     : 2888
% 8.35/2.89  #Fact    : 0
% 8.35/2.89  #Define  : 0
% 8.35/2.89  #Split   : 21
% 8.35/2.89  #Chain   : 0
% 8.35/2.89  #Close   : 0
% 8.35/2.89  
% 8.35/2.89  Ordering : KBO
% 8.35/2.89  
% 8.35/2.89  Simplification rules
% 8.35/2.89  ----------------------
% 8.35/2.89  #Subsume      : 253
% 8.35/2.89  #Demod        : 3144
% 8.35/2.89  #Tautology    : 1668
% 8.35/2.89  #SimpNegUnit  : 10
% 8.35/2.89  #BackRed      : 92
% 8.35/2.89  
% 8.35/2.89  #Partial instantiations: 0
% 8.35/2.89  #Strategies tried      : 1
% 8.35/2.89  
% 8.35/2.89  Timing (in seconds)
% 8.35/2.89  ----------------------
% 8.48/2.90  Preprocessing        : 0.36
% 8.48/2.90  Parsing              : 0.19
% 8.48/2.90  CNF conversion       : 0.03
% 8.48/2.90  Main loop            : 1.75
% 8.48/2.90  Inferencing          : 0.56
% 8.48/2.90  Reduction            : 0.66
% 8.48/2.90  Demodulation         : 0.49
% 8.48/2.90  BG Simplification    : 0.06
% 8.48/2.90  Subsumption          : 0.35
% 8.48/2.90  Abstraction          : 0.07
% 8.48/2.90  MUC search           : 0.00
% 8.48/2.90  Cooper               : 0.00
% 8.48/2.90  Total                : 2.17
% 8.48/2.90  Index Insertion      : 0.00
% 8.48/2.90  Index Deletion       : 0.00
% 8.48/2.90  Index Matching       : 0.00
% 8.48/2.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
