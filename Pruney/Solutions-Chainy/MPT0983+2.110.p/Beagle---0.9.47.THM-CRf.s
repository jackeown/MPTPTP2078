%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:17 EST 2020

% Result     : Theorem 8.19s
% Output     : CNFRefutation 8.48s
% Verified   : 
% Statistics : Number of formulae       :  214 ( 669 expanded)
%              Number of leaves         :   54 ( 252 expanded)
%              Depth                    :   15
%              Number of atoms          :  430 (2007 expanded)
%              Number of equality atoms :   70 ( 172 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_145,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_143,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_129,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_133,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_80,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_46,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_91,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_72,plain,
    ( ~ v2_funct_2('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_125,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_86,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_84,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_82,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_80,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_78,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_66,plain,(
    ! [A_54] : k6_relat_1(A_54) = k6_partfun1(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_42,plain,(
    ! [A_31] : v2_funct_1(k6_relat_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_87,plain,(
    ! [A_31] : v2_funct_1(k6_partfun1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_42])).

tff(c_5419,plain,(
    ! [F_423,C_427,B_425,D_424,A_426,E_428] :
      ( k1_partfun1(A_426,B_425,C_427,D_424,E_428,F_423) = k5_relat_1(E_428,F_423)
      | ~ m1_subset_1(F_423,k1_zfmisc_1(k2_zfmisc_1(C_427,D_424)))
      | ~ v1_funct_1(F_423)
      | ~ m1_subset_1(E_428,k1_zfmisc_1(k2_zfmisc_1(A_426,B_425)))
      | ~ v1_funct_1(E_428) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_5427,plain,(
    ! [A_426,B_425,E_428] :
      ( k1_partfun1(A_426,B_425,'#skF_4','#skF_3',E_428,'#skF_6') = k5_relat_1(E_428,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_428,k1_zfmisc_1(k2_zfmisc_1(A_426,B_425)))
      | ~ v1_funct_1(E_428) ) ),
    inference(resolution,[status(thm)],[c_76,c_5419])).

tff(c_6855,plain,(
    ! [A_497,B_498,E_499] :
      ( k1_partfun1(A_497,B_498,'#skF_4','#skF_3',E_499,'#skF_6') = k5_relat_1(E_499,'#skF_6')
      | ~ m1_subset_1(E_499,k1_zfmisc_1(k2_zfmisc_1(A_497,B_498)))
      | ~ v1_funct_1(E_499) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5427])).

tff(c_6885,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_6855])).

tff(c_6899,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_6885])).

tff(c_56,plain,(
    ! [D_44,F_46,C_43,A_41,B_42,E_45] :
      ( m1_subset_1(k1_partfun1(A_41,B_42,C_43,D_44,E_45,F_46),k1_zfmisc_1(k2_zfmisc_1(A_41,D_44)))
      | ~ m1_subset_1(F_46,k1_zfmisc_1(k2_zfmisc_1(C_43,D_44)))
      | ~ v1_funct_1(F_46)
      | ~ m1_subset_1(E_45,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_1(E_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_7272,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6899,c_56])).

tff(c_7279,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_7272])).

tff(c_62,plain,(
    ! [A_47] : m1_subset_1(k6_partfun1(A_47),k1_zfmisc_1(k2_zfmisc_1(A_47,A_47))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_74,plain,(
    r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_4949,plain,(
    ! [D_392,C_393,A_394,B_395] :
      ( D_392 = C_393
      | ~ r2_relset_1(A_394,B_395,C_393,D_392)
      | ~ m1_subset_1(D_392,k1_zfmisc_1(k2_zfmisc_1(A_394,B_395)))
      | ~ m1_subset_1(C_393,k1_zfmisc_1(k2_zfmisc_1(A_394,B_395))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4959,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_74,c_4949])).

tff(c_4978,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4959])).

tff(c_5023,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_4978])).

tff(c_7343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7279,c_6899,c_5023])).

tff(c_7344,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_4978])).

tff(c_8514,plain,(
    ! [C_601,A_599,D_598,E_600,B_597] :
      ( k1_xboole_0 = C_601
      | v2_funct_1(D_598)
      | ~ v2_funct_1(k1_partfun1(A_599,B_597,B_597,C_601,D_598,E_600))
      | ~ m1_subset_1(E_600,k1_zfmisc_1(k2_zfmisc_1(B_597,C_601)))
      | ~ v1_funct_2(E_600,B_597,C_601)
      | ~ v1_funct_1(E_600)
      | ~ m1_subset_1(D_598,k1_zfmisc_1(k2_zfmisc_1(A_599,B_597)))
      | ~ v1_funct_2(D_598,A_599,B_597)
      | ~ v1_funct_1(D_598) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_8518,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5')
    | ~ v2_funct_1(k6_partfun1('#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7344,c_8514])).

tff(c_8522,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_78,c_76,c_87,c_8518])).

tff(c_8523,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_8522])).

tff(c_32,plain,(
    ! [A_25,B_26] : v1_relat_1(k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_213,plain,(
    ! [B_95,A_96] :
      ( v1_relat_1(B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_96))
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_219,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_76,c_213])).

tff(c_228,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_219])).

tff(c_441,plain,(
    ! [C_117,B_118,A_119] :
      ( v5_relat_1(C_117,B_118)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_119,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_456,plain,(
    v5_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_441])).

tff(c_555,plain,(
    ! [B_125,A_126] :
      ( k2_relat_1(B_125) = A_126
      | ~ v2_funct_2(B_125,A_126)
      | ~ v5_relat_1(B_125,A_126)
      | ~ v1_relat_1(B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_561,plain,
    ( k2_relat_1('#skF_6') = '#skF_3'
    | ~ v2_funct_2('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_456,c_555])).

tff(c_576,plain,
    ( k2_relat_1('#skF_6') = '#skF_3'
    | ~ v2_funct_2('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_561])).

tff(c_586,plain,(
    ~ v2_funct_2('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_576])).

tff(c_1287,plain,(
    ! [E_184,A_182,C_183,D_180,B_181,F_179] :
      ( k1_partfun1(A_182,B_181,C_183,D_180,E_184,F_179) = k5_relat_1(E_184,F_179)
      | ~ m1_subset_1(F_179,k1_zfmisc_1(k2_zfmisc_1(C_183,D_180)))
      | ~ v1_funct_1(F_179)
      | ~ m1_subset_1(E_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_181)))
      | ~ v1_funct_1(E_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1295,plain,(
    ! [A_182,B_181,E_184] :
      ( k1_partfun1(A_182,B_181,'#skF_4','#skF_3',E_184,'#skF_6') = k5_relat_1(E_184,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_181)))
      | ~ v1_funct_1(E_184) ) ),
    inference(resolution,[status(thm)],[c_76,c_1287])).

tff(c_2390,plain,(
    ! [A_249,B_250,E_251] :
      ( k1_partfun1(A_249,B_250,'#skF_4','#skF_3',E_251,'#skF_6') = k5_relat_1(E_251,'#skF_6')
      | ~ m1_subset_1(E_251,k1_zfmisc_1(k2_zfmisc_1(A_249,B_250)))
      | ~ v1_funct_1(E_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1295])).

tff(c_2417,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_2390])).

tff(c_2431,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2417])).

tff(c_3161,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2431,c_56])).

tff(c_3168,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_3161])).

tff(c_754,plain,(
    ! [D_143,C_144,A_145,B_146] :
      ( D_143 = C_144
      | ~ r2_relset_1(A_145,B_146,C_144,D_143)
      | ~ m1_subset_1(D_143,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_764,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_74,c_754])).

tff(c_783,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_764])).

tff(c_868,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_783])).

tff(c_3232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3168,c_2431,c_868])).

tff(c_3233,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_783])).

tff(c_4432,plain,(
    ! [B_358,E_361,C_362,D_359,A_360] :
      ( k1_xboole_0 = C_362
      | v2_funct_1(D_359)
      | ~ v2_funct_1(k1_partfun1(A_360,B_358,B_358,C_362,D_359,E_361))
      | ~ m1_subset_1(E_361,k1_zfmisc_1(k2_zfmisc_1(B_358,C_362)))
      | ~ v1_funct_2(E_361,B_358,C_362)
      | ~ v1_funct_1(E_361)
      | ~ m1_subset_1(D_359,k1_zfmisc_1(k2_zfmisc_1(A_360,B_358)))
      | ~ v1_funct_2(D_359,A_360,B_358)
      | ~ v1_funct_1(D_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_4434,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5')
    | ~ v2_funct_1(k6_partfun1('#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3233,c_4432])).

tff(c_4436,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_78,c_76,c_87,c_4434])).

tff(c_4437,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_4436])).

tff(c_269,plain,(
    ! [B_101,A_102] :
      ( r1_tarski(k2_relat_1(B_101),A_102)
      | ~ v5_relat_1(B_101,A_102)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_135,plain,(
    ! [B_80,A_81] :
      ( ~ r1_xboole_0(B_80,A_81)
      | ~ r1_tarski(B_80,A_81)
      | v1_xboole_0(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_139,plain,(
    ! [A_12] :
      ( ~ r1_tarski(A_12,k1_xboole_0)
      | v1_xboole_0(A_12) ) ),
    inference(resolution,[status(thm)],[c_18,c_135])).

tff(c_284,plain,(
    ! [B_101] :
      ( v1_xboole_0(k2_relat_1(B_101))
      | ~ v5_relat_1(B_101,k1_xboole_0)
      | ~ v1_relat_1(B_101) ) ),
    inference(resolution,[status(thm)],[c_269,c_139])).

tff(c_222,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_82,c_213])).

tff(c_231,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_222])).

tff(c_38,plain,(
    ! [A_30] : k2_relat_1(k6_relat_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_89,plain,(
    ! [A_30] : k2_relat_1(k6_partfun1(A_30)) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_38])).

tff(c_3741,plain,(
    ! [D_307,C_310,F_306,A_309,B_308,E_311] :
      ( k1_partfun1(A_309,B_308,C_310,D_307,E_311,F_306) = k5_relat_1(E_311,F_306)
      | ~ m1_subset_1(F_306,k1_zfmisc_1(k2_zfmisc_1(C_310,D_307)))
      | ~ v1_funct_1(F_306)
      | ~ m1_subset_1(E_311,k1_zfmisc_1(k2_zfmisc_1(A_309,B_308)))
      | ~ v1_funct_1(E_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3749,plain,(
    ! [A_309,B_308,E_311] :
      ( k1_partfun1(A_309,B_308,'#skF_4','#skF_3',E_311,'#skF_6') = k5_relat_1(E_311,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_311,k1_zfmisc_1(k2_zfmisc_1(A_309,B_308)))
      | ~ v1_funct_1(E_311) ) ),
    inference(resolution,[status(thm)],[c_76,c_3741])).

tff(c_4379,plain,(
    ! [A_355,B_356,E_357] :
      ( k1_partfun1(A_355,B_356,'#skF_4','#skF_3',E_357,'#skF_6') = k5_relat_1(E_357,'#skF_6')
      | ~ m1_subset_1(E_357,k1_zfmisc_1(k2_zfmisc_1(A_355,B_356)))
      | ~ v1_funct_1(E_357) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3749])).

tff(c_4400,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_4379])).

tff(c_4408,plain,(
    k5_relat_1('#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_3233,c_4400])).

tff(c_34,plain,(
    ! [A_27,B_29] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_27,B_29)),k2_relat_1(B_29))
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4412,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_3')),k2_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4408,c_34])).

tff(c_4416,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_228,c_89,c_4412])).

tff(c_182,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_2'(A_88,B_89),A_88)
      | r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_193,plain,(
    ! [A_90,B_91] :
      ( ~ v1_xboole_0(A_90)
      | r1_tarski(A_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_182,c_2])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_200,plain,(
    ! [B_91,A_90] :
      ( B_91 = A_90
      | ~ r1_tarski(B_91,A_90)
      | ~ v1_xboole_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_193,c_12])).

tff(c_4423,plain,
    ( k2_relat_1('#skF_6') = '#skF_3'
    | ~ v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_4416,c_200])).

tff(c_4425,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_4423])).

tff(c_4428,plain,
    ( ~ v5_relat_1('#skF_6',k1_xboole_0)
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_284,c_4425])).

tff(c_4431,plain,(
    ~ v5_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_4428])).

tff(c_4439,plain,(
    ~ v5_relat_1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4437,c_4431])).

tff(c_4487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_4439])).

tff(c_4488,plain,(
    k2_relat_1('#skF_6') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4423])).

tff(c_368,plain,(
    ! [B_109,A_110] :
      ( v5_relat_1(B_109,A_110)
      | ~ r1_tarski(k2_relat_1(B_109),A_110)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_392,plain,(
    ! [B_109] :
      ( v5_relat_1(B_109,k2_relat_1(B_109))
      | ~ v1_relat_1(B_109) ) ),
    inference(resolution,[status(thm)],[c_16,c_368])).

tff(c_510,plain,(
    ! [B_121] :
      ( v2_funct_2(B_121,k2_relat_1(B_121))
      | ~ v5_relat_1(B_121,k2_relat_1(B_121))
      | ~ v1_relat_1(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_520,plain,(
    ! [B_109] :
      ( v2_funct_2(B_109,k2_relat_1(B_109))
      | ~ v1_relat_1(B_109) ) ),
    inference(resolution,[status(thm)],[c_392,c_510])).

tff(c_4503,plain,
    ( v2_funct_2('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4488,c_520])).

tff(c_4523,plain,(
    v2_funct_2('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_4503])).

tff(c_4525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_586,c_4523])).

tff(c_4526,plain,(
    k2_relat_1('#skF_6') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_576])).

tff(c_28,plain,(
    ! [B_24,A_23] :
      ( v5_relat_1(B_24,A_23)
      | ~ r1_tarski(k2_relat_1(B_24),A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4537,plain,(
    ! [A_23] :
      ( v5_relat_1('#skF_6',A_23)
      | ~ r1_tarski('#skF_3',A_23)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4526,c_28])).

tff(c_4548,plain,(
    ! [A_23] :
      ( v5_relat_1('#skF_6',A_23)
      | ~ r1_tarski('#skF_3',A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_4537])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( v1_xboole_0(k2_zfmisc_1(A_15,B_16))
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_153,plain,(
    ! [B_85,A_86] :
      ( v1_xboole_0(B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_86))
      | ~ v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_165,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_82,c_153])).

tff(c_167,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_175,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_167])).

tff(c_7750,plain,(
    ! [B_547] :
      ( v1_xboole_0(k2_relat_1(B_547))
      | ~ v5_relat_1(B_547,k1_xboole_0)
      | ~ v1_relat_1(B_547) ) ),
    inference(resolution,[status(thm)],[c_269,c_139])).

tff(c_7767,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v5_relat_1('#skF_6',k1_xboole_0)
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4526,c_7750])).

tff(c_7781,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v5_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_7767])).

tff(c_7782,plain,(
    ~ v5_relat_1('#skF_6',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_7781])).

tff(c_7790,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4548,c_7782])).

tff(c_8534,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8523,c_7790])).

tff(c_8575,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_8534])).

tff(c_8576,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_140,plain,(
    ! [A_82] :
      ( ~ r1_tarski(A_82,k1_xboole_0)
      | v1_xboole_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_18,c_135])).

tff(c_145,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_140])).

tff(c_8608,plain,(
    ! [A_606,B_607] :
      ( r2_hidden('#skF_2'(A_606,B_607),A_606)
      | r1_tarski(A_606,B_607) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8618,plain,(
    ! [A_606,B_607] :
      ( ~ v1_xboole_0(A_606)
      | r1_tarski(A_606,B_607) ) ),
    inference(resolution,[status(thm)],[c_8608,c_2])).

tff(c_8619,plain,(
    ! [A_608,B_609] :
      ( ~ v1_xboole_0(A_608)
      | r1_tarski(A_608,B_609) ) ),
    inference(resolution,[status(thm)],[c_8608,c_2])).

tff(c_8628,plain,(
    ! [B_610,A_611] :
      ( B_610 = A_611
      | ~ r1_tarski(B_610,A_611)
      | ~ v1_xboole_0(A_611) ) ),
    inference(resolution,[status(thm)],[c_8619,c_12])).

tff(c_8656,plain,(
    ! [B_614,A_615] :
      ( B_614 = A_615
      | ~ v1_xboole_0(B_614)
      | ~ v1_xboole_0(A_615) ) ),
    inference(resolution,[status(thm)],[c_8618,c_8628])).

tff(c_8672,plain,(
    ! [A_616] :
      ( k1_xboole_0 = A_616
      | ~ v1_xboole_0(A_616) ) ),
    inference(resolution,[status(thm)],[c_145,c_8656])).

tff(c_8690,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8576,c_8672])).

tff(c_8582,plain,(
    ! [A_602] :
      ( v1_xboole_0(k6_partfun1(A_602))
      | ~ v1_xboole_0(k2_zfmisc_1(A_602,A_602)) ) ),
    inference(resolution,[status(thm)],[c_62,c_153])).

tff(c_8587,plain,(
    ! [B_16] :
      ( v1_xboole_0(k6_partfun1(B_16))
      | ~ v1_xboole_0(B_16) ) ),
    inference(resolution,[status(thm)],[c_22,c_8582])).

tff(c_8688,plain,(
    ! [B_16] :
      ( k6_partfun1(B_16) = k1_xboole_0
      | ~ v1_xboole_0(B_16) ) ),
    inference(resolution,[status(thm)],[c_8587,c_8672])).

tff(c_8761,plain,(
    ! [B_622] :
      ( k6_partfun1(B_622) = '#skF_5'
      | ~ v1_xboole_0(B_622) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8690,c_8688])).

tff(c_8772,plain,(
    k6_partfun1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8576,c_8761])).

tff(c_8793,plain,(
    v2_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8772,c_87])).

tff(c_8800,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_8793])).

tff(c_8801,plain,(
    ~ v2_funct_2('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_8817,plain,(
    ! [B_633,A_634] :
      ( v1_relat_1(B_633)
      | ~ m1_subset_1(B_633,k1_zfmisc_1(A_634))
      | ~ v1_relat_1(A_634) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8826,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_76,c_8817])).

tff(c_8835,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8826])).

tff(c_8999,plain,(
    ! [C_656,B_657,A_658] :
      ( v5_relat_1(C_656,B_657)
      | ~ m1_subset_1(C_656,k1_zfmisc_1(k2_zfmisc_1(A_658,B_657))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_9011,plain,(
    v5_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_8999])).

tff(c_8823,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_82,c_8817])).

tff(c_8832,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8823])).

tff(c_9749,plain,(
    ! [C_724,A_723,B_722,F_720,E_725,D_721] :
      ( k1_partfun1(A_723,B_722,C_724,D_721,E_725,F_720) = k5_relat_1(E_725,F_720)
      | ~ m1_subset_1(F_720,k1_zfmisc_1(k2_zfmisc_1(C_724,D_721)))
      | ~ v1_funct_1(F_720)
      | ~ m1_subset_1(E_725,k1_zfmisc_1(k2_zfmisc_1(A_723,B_722)))
      | ~ v1_funct_1(E_725) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_9759,plain,(
    ! [A_723,B_722,E_725] :
      ( k1_partfun1(A_723,B_722,'#skF_4','#skF_3',E_725,'#skF_6') = k5_relat_1(E_725,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_725,k1_zfmisc_1(k2_zfmisc_1(A_723,B_722)))
      | ~ v1_funct_1(E_725) ) ),
    inference(resolution,[status(thm)],[c_76,c_9749])).

tff(c_10609,plain,(
    ! [A_784,B_785,E_786] :
      ( k1_partfun1(A_784,B_785,'#skF_4','#skF_3',E_786,'#skF_6') = k5_relat_1(E_786,'#skF_6')
      | ~ m1_subset_1(E_786,k1_zfmisc_1(k2_zfmisc_1(A_784,B_785)))
      | ~ v1_funct_1(E_786) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_9759])).

tff(c_10627,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_10609])).

tff(c_10635,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_10627])).

tff(c_11154,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10635,c_56])).

tff(c_11160,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_11154])).

tff(c_9386,plain,(
    ! [D_691,C_692,A_693,B_694] :
      ( D_691 = C_692
      | ~ r2_relset_1(A_693,B_694,C_692,D_691)
      | ~ m1_subset_1(D_691,k1_zfmisc_1(k2_zfmisc_1(A_693,B_694)))
      | ~ m1_subset_1(C_692,k1_zfmisc_1(k2_zfmisc_1(A_693,B_694))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_9392,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_74,c_9386])).

tff(c_9403,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_9392])).

tff(c_12035,plain,(
    k5_relat_1('#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11160,c_10635,c_10635,c_9403])).

tff(c_12057,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_3')),k2_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_12035,c_34])).

tff(c_12065,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8832,c_8835,c_89,c_12057])).

tff(c_8956,plain,(
    ! [B_654,A_655] :
      ( r1_tarski(k2_relat_1(B_654),A_655)
      | ~ v5_relat_1(B_654,A_655)
      | ~ v1_relat_1(B_654) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8971,plain,(
    ! [B_654,A_655] :
      ( k2_relat_1(B_654) = A_655
      | ~ r1_tarski(A_655,k2_relat_1(B_654))
      | ~ v5_relat_1(B_654,A_655)
      | ~ v1_relat_1(B_654) ) ),
    inference(resolution,[status(thm)],[c_8956,c_12])).

tff(c_12069,plain,
    ( k2_relat_1('#skF_6') = '#skF_3'
    | ~ v5_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_12065,c_8971])).

tff(c_12082,plain,(
    k2_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8835,c_9011,c_12069])).

tff(c_9063,plain,(
    ! [B_669,A_670] :
      ( v5_relat_1(B_669,A_670)
      | ~ r1_tarski(k2_relat_1(B_669),A_670)
      | ~ v1_relat_1(B_669) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_9087,plain,(
    ! [B_669] :
      ( v5_relat_1(B_669,k2_relat_1(B_669))
      | ~ v1_relat_1(B_669) ) ),
    inference(resolution,[status(thm)],[c_16,c_9063])).

tff(c_9143,plain,(
    ! [B_673] :
      ( v2_funct_2(B_673,k2_relat_1(B_673))
      | ~ v5_relat_1(B_673,k2_relat_1(B_673))
      | ~ v1_relat_1(B_673) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_9153,plain,(
    ! [B_669] :
      ( v2_funct_2(B_669,k2_relat_1(B_669))
      | ~ v1_relat_1(B_669) ) ),
    inference(resolution,[status(thm)],[c_9087,c_9143])).

tff(c_12111,plain,
    ( v2_funct_2('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_12082,c_9153])).

tff(c_12137,plain,(
    v2_funct_2('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8835,c_12111])).

tff(c_12139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8801,c_12137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:54:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.19/2.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.19/2.85  
% 8.19/2.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.19/2.85  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 8.19/2.85  
% 8.19/2.85  %Foreground sorts:
% 8.19/2.85  
% 8.19/2.85  
% 8.19/2.85  %Background operators:
% 8.19/2.85  
% 8.19/2.85  
% 8.19/2.85  %Foreground operators:
% 8.19/2.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.19/2.85  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.19/2.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.19/2.85  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.19/2.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.19/2.85  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.19/2.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.19/2.85  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.19/2.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.19/2.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.19/2.85  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.19/2.85  tff('#skF_5', type, '#skF_5': $i).
% 8.19/2.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.19/2.85  tff('#skF_6', type, '#skF_6': $i).
% 8.19/2.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.19/2.85  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.19/2.85  tff('#skF_3', type, '#skF_3': $i).
% 8.19/2.85  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.19/2.85  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.19/2.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.19/2.85  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.19/2.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.19/2.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.19/2.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.19/2.85  tff('#skF_4', type, '#skF_4': $i).
% 8.19/2.85  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.19/2.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.19/2.85  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.19/2.85  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.19/2.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.19/2.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.19/2.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.19/2.85  
% 8.48/2.88  tff(f_187, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 8.48/2.88  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.48/2.88  tff(f_145, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.48/2.88  tff(f_95, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 8.48/2.88  tff(f_143, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.48/2.88  tff(f_129, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.48/2.88  tff(f_133, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 8.48/2.88  tff(f_109, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.48/2.88  tff(f_167, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 8.48/2.88  tff(f_80, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.48/2.88  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.48/2.88  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.48/2.88  tff(f_117, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 8.48/2.88  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 8.48/2.88  tff(f_46, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.48/2.88  tff(f_54, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 8.48/2.88  tff(f_91, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.48/2.88  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 8.48/2.88  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.48/2.88  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.48/2.88  tff(f_58, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 8.48/2.88  tff(f_65, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 8.48/2.88  tff(c_72, plain, (~v2_funct_2('#skF_6', '#skF_3') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.48/2.88  tff(c_125, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_72])).
% 8.48/2.88  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.48/2.88  tff(c_86, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.48/2.88  tff(c_84, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.48/2.88  tff(c_82, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.48/2.88  tff(c_80, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.48/2.88  tff(c_78, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.48/2.88  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.48/2.88  tff(c_66, plain, (![A_54]: (k6_relat_1(A_54)=k6_partfun1(A_54))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.48/2.88  tff(c_42, plain, (![A_31]: (v2_funct_1(k6_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.48/2.88  tff(c_87, plain, (![A_31]: (v2_funct_1(k6_partfun1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_42])).
% 8.48/2.88  tff(c_5419, plain, (![F_423, C_427, B_425, D_424, A_426, E_428]: (k1_partfun1(A_426, B_425, C_427, D_424, E_428, F_423)=k5_relat_1(E_428, F_423) | ~m1_subset_1(F_423, k1_zfmisc_1(k2_zfmisc_1(C_427, D_424))) | ~v1_funct_1(F_423) | ~m1_subset_1(E_428, k1_zfmisc_1(k2_zfmisc_1(A_426, B_425))) | ~v1_funct_1(E_428))), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.48/2.88  tff(c_5427, plain, (![A_426, B_425, E_428]: (k1_partfun1(A_426, B_425, '#skF_4', '#skF_3', E_428, '#skF_6')=k5_relat_1(E_428, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_428, k1_zfmisc_1(k2_zfmisc_1(A_426, B_425))) | ~v1_funct_1(E_428))), inference(resolution, [status(thm)], [c_76, c_5419])).
% 8.48/2.88  tff(c_6855, plain, (![A_497, B_498, E_499]: (k1_partfun1(A_497, B_498, '#skF_4', '#skF_3', E_499, '#skF_6')=k5_relat_1(E_499, '#skF_6') | ~m1_subset_1(E_499, k1_zfmisc_1(k2_zfmisc_1(A_497, B_498))) | ~v1_funct_1(E_499))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_5427])).
% 8.48/2.88  tff(c_6885, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_6855])).
% 8.48/2.88  tff(c_6899, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_6885])).
% 8.48/2.88  tff(c_56, plain, (![D_44, F_46, C_43, A_41, B_42, E_45]: (m1_subset_1(k1_partfun1(A_41, B_42, C_43, D_44, E_45, F_46), k1_zfmisc_1(k2_zfmisc_1(A_41, D_44))) | ~m1_subset_1(F_46, k1_zfmisc_1(k2_zfmisc_1(C_43, D_44))) | ~v1_funct_1(F_46) | ~m1_subset_1(E_45, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_1(E_45))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.48/2.88  tff(c_7272, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6899, c_56])).
% 8.48/2.88  tff(c_7279, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_7272])).
% 8.48/2.88  tff(c_62, plain, (![A_47]: (m1_subset_1(k6_partfun1(A_47), k1_zfmisc_1(k2_zfmisc_1(A_47, A_47))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.48/2.88  tff(c_74, plain, (r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.48/2.88  tff(c_4949, plain, (![D_392, C_393, A_394, B_395]: (D_392=C_393 | ~r2_relset_1(A_394, B_395, C_393, D_392) | ~m1_subset_1(D_392, k1_zfmisc_1(k2_zfmisc_1(A_394, B_395))) | ~m1_subset_1(C_393, k1_zfmisc_1(k2_zfmisc_1(A_394, B_395))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.48/2.88  tff(c_4959, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_74, c_4949])).
% 8.48/2.88  tff(c_4978, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4959])).
% 8.48/2.88  tff(c_5023, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_4978])).
% 8.48/2.88  tff(c_7343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7279, c_6899, c_5023])).
% 8.48/2.88  tff(c_7344, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_4978])).
% 8.48/2.88  tff(c_8514, plain, (![C_601, A_599, D_598, E_600, B_597]: (k1_xboole_0=C_601 | v2_funct_1(D_598) | ~v2_funct_1(k1_partfun1(A_599, B_597, B_597, C_601, D_598, E_600)) | ~m1_subset_1(E_600, k1_zfmisc_1(k2_zfmisc_1(B_597, C_601))) | ~v1_funct_2(E_600, B_597, C_601) | ~v1_funct_1(E_600) | ~m1_subset_1(D_598, k1_zfmisc_1(k2_zfmisc_1(A_599, B_597))) | ~v1_funct_2(D_598, A_599, B_597) | ~v1_funct_1(D_598))), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.48/2.88  tff(c_8518, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5') | ~v2_funct_1(k6_partfun1('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7344, c_8514])).
% 8.48/2.88  tff(c_8522, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_78, c_76, c_87, c_8518])).
% 8.48/2.88  tff(c_8523, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_125, c_8522])).
% 8.48/2.88  tff(c_32, plain, (![A_25, B_26]: (v1_relat_1(k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.48/2.88  tff(c_213, plain, (![B_95, A_96]: (v1_relat_1(B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(A_96)) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.48/2.88  tff(c_219, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_76, c_213])).
% 8.48/2.88  tff(c_228, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_219])).
% 8.48/2.88  tff(c_441, plain, (![C_117, B_118, A_119]: (v5_relat_1(C_117, B_118) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_119, B_118))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.48/2.88  tff(c_456, plain, (v5_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_441])).
% 8.48/2.88  tff(c_555, plain, (![B_125, A_126]: (k2_relat_1(B_125)=A_126 | ~v2_funct_2(B_125, A_126) | ~v5_relat_1(B_125, A_126) | ~v1_relat_1(B_125))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.48/2.88  tff(c_561, plain, (k2_relat_1('#skF_6')='#skF_3' | ~v2_funct_2('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_456, c_555])).
% 8.48/2.88  tff(c_576, plain, (k2_relat_1('#skF_6')='#skF_3' | ~v2_funct_2('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_561])).
% 8.48/2.88  tff(c_586, plain, (~v2_funct_2('#skF_6', '#skF_3')), inference(splitLeft, [status(thm)], [c_576])).
% 8.48/2.88  tff(c_1287, plain, (![E_184, A_182, C_183, D_180, B_181, F_179]: (k1_partfun1(A_182, B_181, C_183, D_180, E_184, F_179)=k5_relat_1(E_184, F_179) | ~m1_subset_1(F_179, k1_zfmisc_1(k2_zfmisc_1(C_183, D_180))) | ~v1_funct_1(F_179) | ~m1_subset_1(E_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_181))) | ~v1_funct_1(E_184))), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.48/2.88  tff(c_1295, plain, (![A_182, B_181, E_184]: (k1_partfun1(A_182, B_181, '#skF_4', '#skF_3', E_184, '#skF_6')=k5_relat_1(E_184, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_181))) | ~v1_funct_1(E_184))), inference(resolution, [status(thm)], [c_76, c_1287])).
% 8.48/2.88  tff(c_2390, plain, (![A_249, B_250, E_251]: (k1_partfun1(A_249, B_250, '#skF_4', '#skF_3', E_251, '#skF_6')=k5_relat_1(E_251, '#skF_6') | ~m1_subset_1(E_251, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))) | ~v1_funct_1(E_251))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1295])).
% 8.48/2.88  tff(c_2417, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_2390])).
% 8.48/2.88  tff(c_2431, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2417])).
% 8.48/2.88  tff(c_3161, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2431, c_56])).
% 8.48/2.88  tff(c_3168, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_3161])).
% 8.48/2.88  tff(c_754, plain, (![D_143, C_144, A_145, B_146]: (D_143=C_144 | ~r2_relset_1(A_145, B_146, C_144, D_143) | ~m1_subset_1(D_143, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.48/2.88  tff(c_764, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_74, c_754])).
% 8.48/2.88  tff(c_783, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_764])).
% 8.48/2.88  tff(c_868, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_783])).
% 8.48/2.88  tff(c_3232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3168, c_2431, c_868])).
% 8.48/2.88  tff(c_3233, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_783])).
% 8.48/2.88  tff(c_4432, plain, (![B_358, E_361, C_362, D_359, A_360]: (k1_xboole_0=C_362 | v2_funct_1(D_359) | ~v2_funct_1(k1_partfun1(A_360, B_358, B_358, C_362, D_359, E_361)) | ~m1_subset_1(E_361, k1_zfmisc_1(k2_zfmisc_1(B_358, C_362))) | ~v1_funct_2(E_361, B_358, C_362) | ~v1_funct_1(E_361) | ~m1_subset_1(D_359, k1_zfmisc_1(k2_zfmisc_1(A_360, B_358))) | ~v1_funct_2(D_359, A_360, B_358) | ~v1_funct_1(D_359))), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.48/2.88  tff(c_4434, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5') | ~v2_funct_1(k6_partfun1('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3233, c_4432])).
% 8.48/2.88  tff(c_4436, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_78, c_76, c_87, c_4434])).
% 8.48/2.88  tff(c_4437, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_125, c_4436])).
% 8.48/2.88  tff(c_269, plain, (![B_101, A_102]: (r1_tarski(k2_relat_1(B_101), A_102) | ~v5_relat_1(B_101, A_102) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.48/2.88  tff(c_18, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.48/2.88  tff(c_135, plain, (![B_80, A_81]: (~r1_xboole_0(B_80, A_81) | ~r1_tarski(B_80, A_81) | v1_xboole_0(B_80))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.48/2.88  tff(c_139, plain, (![A_12]: (~r1_tarski(A_12, k1_xboole_0) | v1_xboole_0(A_12))), inference(resolution, [status(thm)], [c_18, c_135])).
% 8.48/2.88  tff(c_284, plain, (![B_101]: (v1_xboole_0(k2_relat_1(B_101)) | ~v5_relat_1(B_101, k1_xboole_0) | ~v1_relat_1(B_101))), inference(resolution, [status(thm)], [c_269, c_139])).
% 8.48/2.88  tff(c_222, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_213])).
% 8.48/2.88  tff(c_231, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_222])).
% 8.48/2.88  tff(c_38, plain, (![A_30]: (k2_relat_1(k6_relat_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.48/2.88  tff(c_89, plain, (![A_30]: (k2_relat_1(k6_partfun1(A_30))=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_38])).
% 8.48/2.88  tff(c_3741, plain, (![D_307, C_310, F_306, A_309, B_308, E_311]: (k1_partfun1(A_309, B_308, C_310, D_307, E_311, F_306)=k5_relat_1(E_311, F_306) | ~m1_subset_1(F_306, k1_zfmisc_1(k2_zfmisc_1(C_310, D_307))) | ~v1_funct_1(F_306) | ~m1_subset_1(E_311, k1_zfmisc_1(k2_zfmisc_1(A_309, B_308))) | ~v1_funct_1(E_311))), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.48/2.88  tff(c_3749, plain, (![A_309, B_308, E_311]: (k1_partfun1(A_309, B_308, '#skF_4', '#skF_3', E_311, '#skF_6')=k5_relat_1(E_311, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_311, k1_zfmisc_1(k2_zfmisc_1(A_309, B_308))) | ~v1_funct_1(E_311))), inference(resolution, [status(thm)], [c_76, c_3741])).
% 8.48/2.88  tff(c_4379, plain, (![A_355, B_356, E_357]: (k1_partfun1(A_355, B_356, '#skF_4', '#skF_3', E_357, '#skF_6')=k5_relat_1(E_357, '#skF_6') | ~m1_subset_1(E_357, k1_zfmisc_1(k2_zfmisc_1(A_355, B_356))) | ~v1_funct_1(E_357))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3749])).
% 8.48/2.88  tff(c_4400, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_4379])).
% 8.48/2.88  tff(c_4408, plain, (k5_relat_1('#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_3233, c_4400])).
% 8.48/2.88  tff(c_34, plain, (![A_27, B_29]: (r1_tarski(k2_relat_1(k5_relat_1(A_27, B_29)), k2_relat_1(B_29)) | ~v1_relat_1(B_29) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.48/2.88  tff(c_4412, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_3')), k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4408, c_34])).
% 8.48/2.88  tff(c_4416, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_228, c_89, c_4412])).
% 8.48/2.88  tff(c_182, plain, (![A_88, B_89]: (r2_hidden('#skF_2'(A_88, B_89), A_88) | r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.48/2.88  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.48/2.88  tff(c_193, plain, (![A_90, B_91]: (~v1_xboole_0(A_90) | r1_tarski(A_90, B_91))), inference(resolution, [status(thm)], [c_182, c_2])).
% 8.48/2.88  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.48/2.88  tff(c_200, plain, (![B_91, A_90]: (B_91=A_90 | ~r1_tarski(B_91, A_90) | ~v1_xboole_0(A_90))), inference(resolution, [status(thm)], [c_193, c_12])).
% 8.48/2.88  tff(c_4423, plain, (k2_relat_1('#skF_6')='#skF_3' | ~v1_xboole_0(k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_4416, c_200])).
% 8.48/2.88  tff(c_4425, plain, (~v1_xboole_0(k2_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_4423])).
% 8.48/2.88  tff(c_4428, plain, (~v5_relat_1('#skF_6', k1_xboole_0) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_284, c_4425])).
% 8.48/2.88  tff(c_4431, plain, (~v5_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_228, c_4428])).
% 8.48/2.88  tff(c_4439, plain, (~v5_relat_1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4437, c_4431])).
% 8.48/2.88  tff(c_4487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_456, c_4439])).
% 8.48/2.88  tff(c_4488, plain, (k2_relat_1('#skF_6')='#skF_3'), inference(splitRight, [status(thm)], [c_4423])).
% 8.48/2.88  tff(c_368, plain, (![B_109, A_110]: (v5_relat_1(B_109, A_110) | ~r1_tarski(k2_relat_1(B_109), A_110) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.48/2.88  tff(c_392, plain, (![B_109]: (v5_relat_1(B_109, k2_relat_1(B_109)) | ~v1_relat_1(B_109))), inference(resolution, [status(thm)], [c_16, c_368])).
% 8.48/2.88  tff(c_510, plain, (![B_121]: (v2_funct_2(B_121, k2_relat_1(B_121)) | ~v5_relat_1(B_121, k2_relat_1(B_121)) | ~v1_relat_1(B_121))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.48/2.88  tff(c_520, plain, (![B_109]: (v2_funct_2(B_109, k2_relat_1(B_109)) | ~v1_relat_1(B_109))), inference(resolution, [status(thm)], [c_392, c_510])).
% 8.48/2.88  tff(c_4503, plain, (v2_funct_2('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4488, c_520])).
% 8.48/2.88  tff(c_4523, plain, (v2_funct_2('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_4503])).
% 8.48/2.88  tff(c_4525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_586, c_4523])).
% 8.48/2.88  tff(c_4526, plain, (k2_relat_1('#skF_6')='#skF_3'), inference(splitRight, [status(thm)], [c_576])).
% 8.48/2.88  tff(c_28, plain, (![B_24, A_23]: (v5_relat_1(B_24, A_23) | ~r1_tarski(k2_relat_1(B_24), A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.48/2.88  tff(c_4537, plain, (![A_23]: (v5_relat_1('#skF_6', A_23) | ~r1_tarski('#skF_3', A_23) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4526, c_28])).
% 8.48/2.88  tff(c_4548, plain, (![A_23]: (v5_relat_1('#skF_6', A_23) | ~r1_tarski('#skF_3', A_23))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_4537])).
% 8.48/2.88  tff(c_22, plain, (![A_15, B_16]: (v1_xboole_0(k2_zfmisc_1(A_15, B_16)) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.48/2.88  tff(c_153, plain, (![B_85, A_86]: (v1_xboole_0(B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_86)) | ~v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.48/2.88  tff(c_165, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_153])).
% 8.48/2.88  tff(c_167, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_165])).
% 8.48/2.88  tff(c_175, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_167])).
% 8.48/2.88  tff(c_7750, plain, (![B_547]: (v1_xboole_0(k2_relat_1(B_547)) | ~v5_relat_1(B_547, k1_xboole_0) | ~v1_relat_1(B_547))), inference(resolution, [status(thm)], [c_269, c_139])).
% 8.48/2.88  tff(c_7767, plain, (v1_xboole_0('#skF_3') | ~v5_relat_1('#skF_6', k1_xboole_0) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4526, c_7750])).
% 8.48/2.88  tff(c_7781, plain, (v1_xboole_0('#skF_3') | ~v5_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_228, c_7767])).
% 8.48/2.88  tff(c_7782, plain, (~v5_relat_1('#skF_6', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_175, c_7781])).
% 8.48/2.88  tff(c_7790, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_4548, c_7782])).
% 8.48/2.88  tff(c_8534, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8523, c_7790])).
% 8.48/2.88  tff(c_8575, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_8534])).
% 8.48/2.88  tff(c_8576, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_165])).
% 8.48/2.88  tff(c_140, plain, (![A_82]: (~r1_tarski(A_82, k1_xboole_0) | v1_xboole_0(A_82))), inference(resolution, [status(thm)], [c_18, c_135])).
% 8.48/2.88  tff(c_145, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_140])).
% 8.48/2.88  tff(c_8608, plain, (![A_606, B_607]: (r2_hidden('#skF_2'(A_606, B_607), A_606) | r1_tarski(A_606, B_607))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.48/2.88  tff(c_8618, plain, (![A_606, B_607]: (~v1_xboole_0(A_606) | r1_tarski(A_606, B_607))), inference(resolution, [status(thm)], [c_8608, c_2])).
% 8.48/2.88  tff(c_8619, plain, (![A_608, B_609]: (~v1_xboole_0(A_608) | r1_tarski(A_608, B_609))), inference(resolution, [status(thm)], [c_8608, c_2])).
% 8.48/2.88  tff(c_8628, plain, (![B_610, A_611]: (B_610=A_611 | ~r1_tarski(B_610, A_611) | ~v1_xboole_0(A_611))), inference(resolution, [status(thm)], [c_8619, c_12])).
% 8.48/2.88  tff(c_8656, plain, (![B_614, A_615]: (B_614=A_615 | ~v1_xboole_0(B_614) | ~v1_xboole_0(A_615))), inference(resolution, [status(thm)], [c_8618, c_8628])).
% 8.48/2.88  tff(c_8672, plain, (![A_616]: (k1_xboole_0=A_616 | ~v1_xboole_0(A_616))), inference(resolution, [status(thm)], [c_145, c_8656])).
% 8.48/2.88  tff(c_8690, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_8576, c_8672])).
% 8.48/2.88  tff(c_8582, plain, (![A_602]: (v1_xboole_0(k6_partfun1(A_602)) | ~v1_xboole_0(k2_zfmisc_1(A_602, A_602)))), inference(resolution, [status(thm)], [c_62, c_153])).
% 8.48/2.88  tff(c_8587, plain, (![B_16]: (v1_xboole_0(k6_partfun1(B_16)) | ~v1_xboole_0(B_16))), inference(resolution, [status(thm)], [c_22, c_8582])).
% 8.48/2.88  tff(c_8688, plain, (![B_16]: (k6_partfun1(B_16)=k1_xboole_0 | ~v1_xboole_0(B_16))), inference(resolution, [status(thm)], [c_8587, c_8672])).
% 8.48/2.88  tff(c_8761, plain, (![B_622]: (k6_partfun1(B_622)='#skF_5' | ~v1_xboole_0(B_622))), inference(demodulation, [status(thm), theory('equality')], [c_8690, c_8688])).
% 8.48/2.88  tff(c_8772, plain, (k6_partfun1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_8576, c_8761])).
% 8.48/2.88  tff(c_8793, plain, (v2_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8772, c_87])).
% 8.48/2.88  tff(c_8800, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_8793])).
% 8.48/2.88  tff(c_8801, plain, (~v2_funct_2('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_72])).
% 8.48/2.88  tff(c_8817, plain, (![B_633, A_634]: (v1_relat_1(B_633) | ~m1_subset_1(B_633, k1_zfmisc_1(A_634)) | ~v1_relat_1(A_634))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.48/2.88  tff(c_8826, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_76, c_8817])).
% 8.48/2.88  tff(c_8835, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8826])).
% 8.48/2.88  tff(c_8999, plain, (![C_656, B_657, A_658]: (v5_relat_1(C_656, B_657) | ~m1_subset_1(C_656, k1_zfmisc_1(k2_zfmisc_1(A_658, B_657))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.48/2.88  tff(c_9011, plain, (v5_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_8999])).
% 8.48/2.88  tff(c_8823, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_8817])).
% 8.48/2.88  tff(c_8832, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8823])).
% 8.48/2.88  tff(c_9749, plain, (![C_724, A_723, B_722, F_720, E_725, D_721]: (k1_partfun1(A_723, B_722, C_724, D_721, E_725, F_720)=k5_relat_1(E_725, F_720) | ~m1_subset_1(F_720, k1_zfmisc_1(k2_zfmisc_1(C_724, D_721))) | ~v1_funct_1(F_720) | ~m1_subset_1(E_725, k1_zfmisc_1(k2_zfmisc_1(A_723, B_722))) | ~v1_funct_1(E_725))), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.48/2.88  tff(c_9759, plain, (![A_723, B_722, E_725]: (k1_partfun1(A_723, B_722, '#skF_4', '#skF_3', E_725, '#skF_6')=k5_relat_1(E_725, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_725, k1_zfmisc_1(k2_zfmisc_1(A_723, B_722))) | ~v1_funct_1(E_725))), inference(resolution, [status(thm)], [c_76, c_9749])).
% 8.48/2.88  tff(c_10609, plain, (![A_784, B_785, E_786]: (k1_partfun1(A_784, B_785, '#skF_4', '#skF_3', E_786, '#skF_6')=k5_relat_1(E_786, '#skF_6') | ~m1_subset_1(E_786, k1_zfmisc_1(k2_zfmisc_1(A_784, B_785))) | ~v1_funct_1(E_786))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_9759])).
% 8.48/2.88  tff(c_10627, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_10609])).
% 8.48/2.88  tff(c_10635, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_10627])).
% 8.48/2.88  tff(c_11154, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10635, c_56])).
% 8.48/2.88  tff(c_11160, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_11154])).
% 8.48/2.88  tff(c_9386, plain, (![D_691, C_692, A_693, B_694]: (D_691=C_692 | ~r2_relset_1(A_693, B_694, C_692, D_691) | ~m1_subset_1(D_691, k1_zfmisc_1(k2_zfmisc_1(A_693, B_694))) | ~m1_subset_1(C_692, k1_zfmisc_1(k2_zfmisc_1(A_693, B_694))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.48/2.88  tff(c_9392, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_74, c_9386])).
% 8.48/2.88  tff(c_9403, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_9392])).
% 8.48/2.88  tff(c_12035, plain, (k5_relat_1('#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11160, c_10635, c_10635, c_9403])).
% 8.48/2.88  tff(c_12057, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_3')), k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_12035, c_34])).
% 8.48/2.88  tff(c_12065, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_8832, c_8835, c_89, c_12057])).
% 8.48/2.88  tff(c_8956, plain, (![B_654, A_655]: (r1_tarski(k2_relat_1(B_654), A_655) | ~v5_relat_1(B_654, A_655) | ~v1_relat_1(B_654))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.48/2.88  tff(c_8971, plain, (![B_654, A_655]: (k2_relat_1(B_654)=A_655 | ~r1_tarski(A_655, k2_relat_1(B_654)) | ~v5_relat_1(B_654, A_655) | ~v1_relat_1(B_654))), inference(resolution, [status(thm)], [c_8956, c_12])).
% 8.48/2.88  tff(c_12069, plain, (k2_relat_1('#skF_6')='#skF_3' | ~v5_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_12065, c_8971])).
% 8.48/2.88  tff(c_12082, plain, (k2_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8835, c_9011, c_12069])).
% 8.48/2.88  tff(c_9063, plain, (![B_669, A_670]: (v5_relat_1(B_669, A_670) | ~r1_tarski(k2_relat_1(B_669), A_670) | ~v1_relat_1(B_669))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.48/2.88  tff(c_9087, plain, (![B_669]: (v5_relat_1(B_669, k2_relat_1(B_669)) | ~v1_relat_1(B_669))), inference(resolution, [status(thm)], [c_16, c_9063])).
% 8.48/2.88  tff(c_9143, plain, (![B_673]: (v2_funct_2(B_673, k2_relat_1(B_673)) | ~v5_relat_1(B_673, k2_relat_1(B_673)) | ~v1_relat_1(B_673))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.48/2.88  tff(c_9153, plain, (![B_669]: (v2_funct_2(B_669, k2_relat_1(B_669)) | ~v1_relat_1(B_669))), inference(resolution, [status(thm)], [c_9087, c_9143])).
% 8.48/2.88  tff(c_12111, plain, (v2_funct_2('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_12082, c_9153])).
% 8.48/2.88  tff(c_12137, plain, (v2_funct_2('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8835, c_12111])).
% 8.48/2.88  tff(c_12139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8801, c_12137])).
% 8.48/2.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.48/2.88  
% 8.48/2.88  Inference rules
% 8.48/2.88  ----------------------
% 8.48/2.88  #Ref     : 0
% 8.48/2.88  #Sup     : 2779
% 8.48/2.88  #Fact    : 0
% 8.48/2.88  #Define  : 0
% 8.48/2.88  #Split   : 20
% 8.48/2.88  #Chain   : 0
% 8.48/2.88  #Close   : 0
% 8.48/2.88  
% 8.48/2.88  Ordering : KBO
% 8.48/2.88  
% 8.48/2.88  Simplification rules
% 8.48/2.88  ----------------------
% 8.48/2.88  #Subsume      : 341
% 8.48/2.88  #Demod        : 2463
% 8.48/2.88  #Tautology    : 1243
% 8.48/2.88  #SimpNegUnit  : 12
% 8.48/2.88  #BackRed      : 133
% 8.48/2.88  
% 8.48/2.88  #Partial instantiations: 0
% 8.48/2.88  #Strategies tried      : 1
% 8.48/2.88  
% 8.48/2.88  Timing (in seconds)
% 8.48/2.88  ----------------------
% 8.48/2.89  Preprocessing        : 0.36
% 8.48/2.89  Parsing              : 0.18
% 8.48/2.89  CNF conversion       : 0.03
% 8.48/2.89  Main loop            : 1.73
% 8.48/2.89  Inferencing          : 0.54
% 8.48/2.89  Reduction            : 0.64
% 8.48/2.89  Demodulation         : 0.46
% 8.48/2.89  BG Simplification    : 0.06
% 8.48/2.89  Subsumption          : 0.36
% 8.48/2.89  Abstraction          : 0.07
% 8.48/2.89  MUC search           : 0.00
% 8.48/2.89  Cooper               : 0.00
% 8.48/2.89  Total                : 2.14
% 8.48/2.89  Index Insertion      : 0.00
% 8.48/2.89  Index Deletion       : 0.00
% 8.48/2.89  Index Matching       : 0.00
% 8.48/2.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
