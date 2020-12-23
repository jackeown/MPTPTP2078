%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:57 EST 2020

% Result     : Theorem 7.70s
% Output     : CNFRefutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 906 expanded)
%              Number of leaves         :   47 ( 340 expanded)
%              Depth                    :   16
%              Number of atoms          :  498 (3667 expanded)
%              Number of equality atoms :  147 (1118 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_228,negated_conjecture,(
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

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_95,axiom,(
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

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_139,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_141,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_109,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_129,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_58,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_202,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_160,axiom,(
    ! [A,B,C] :
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

tff(f_186,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
              & k2_relset_1(A,B,D) = B )
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | ( v2_funct_1(D)
                & v2_funct_1(E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

tff(c_66,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_82,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_137,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_149,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_137])).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_148,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_137])).

tff(c_88,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_151,plain,(
    ! [C_68,B_69,A_70] :
      ( v5_relat_1(C_68,B_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_162,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_151])).

tff(c_196,plain,(
    ! [B_81,A_82] :
      ( k2_relat_1(B_81) = A_82
      | ~ v2_funct_2(B_81,A_82)
      | ~ v5_relat_1(B_81,A_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_205,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_162,c_196])).

tff(c_214,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_205])).

tff(c_1978,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_76,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_2014,plain,(
    ! [A_225,B_226,C_227] :
      ( k2_relset_1(A_225,B_226,C_227) = k2_relat_1(C_227)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2020,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_2014])).

tff(c_2027,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2020])).

tff(c_38,plain,(
    ! [B_28] :
      ( v2_funct_2(B_28,k2_relat_1(B_28))
      | ~ v5_relat_1(B_28,k2_relat_1(B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2033,plain,
    ( v2_funct_2('#skF_3',k2_relat_1('#skF_3'))
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2027,c_38])).

tff(c_2037,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_162,c_2027,c_2033])).

tff(c_2039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1978,c_2037])).

tff(c_2040,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_2328,plain,(
    ! [A_266,D_270,E_269,F_267,C_268,B_271] :
      ( k1_partfun1(A_266,B_271,C_268,D_270,E_269,F_267) = k5_relat_1(E_269,F_267)
      | ~ m1_subset_1(F_267,k1_zfmisc_1(k2_zfmisc_1(C_268,D_270)))
      | ~ v1_funct_1(F_267)
      | ~ m1_subset_1(E_269,k1_zfmisc_1(k2_zfmisc_1(A_266,B_271)))
      | ~ v1_funct_1(E_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2334,plain,(
    ! [A_266,B_271,E_269] :
      ( k1_partfun1(A_266,B_271,'#skF_2','#skF_1',E_269,'#skF_4') = k5_relat_1(E_269,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_269,k1_zfmisc_1(k2_zfmisc_1(A_266,B_271)))
      | ~ v1_funct_1(E_269) ) ),
    inference(resolution,[status(thm)],[c_78,c_2328])).

tff(c_2414,plain,(
    ! [A_280,B_281,E_282] :
      ( k1_partfun1(A_280,B_281,'#skF_2','#skF_1',E_282,'#skF_4') = k5_relat_1(E_282,'#skF_4')
      | ~ m1_subset_1(E_282,k1_zfmisc_1(k2_zfmisc_1(A_280,B_281)))
      | ~ v1_funct_1(E_282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2334])).

tff(c_2420,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_2414])).

tff(c_2427,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2420])).

tff(c_48,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36,plain,(
    ! [A_26] : m1_subset_1(k6_relat_1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_89,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36])).

tff(c_74,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_2224,plain,(
    ! [D_246,C_247,A_248,B_249] :
      ( D_246 = C_247
      | ~ r2_relset_1(A_248,B_249,C_247,D_246)
      | ~ m1_subset_1(D_246,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249)))
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2232,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_74,c_2224])).

tff(c_2247,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_2232])).

tff(c_2248,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2247])).

tff(c_2432,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2427,c_2248])).

tff(c_2619,plain,(
    ! [F_289,E_290,A_288,B_287,C_291,D_286] :
      ( m1_subset_1(k1_partfun1(A_288,B_287,C_291,D_286,E_290,F_289),k1_zfmisc_1(k2_zfmisc_1(A_288,D_286)))
      | ~ m1_subset_1(F_289,k1_zfmisc_1(k2_zfmisc_1(C_291,D_286)))
      | ~ v1_funct_1(F_289)
      | ~ m1_subset_1(E_290,k1_zfmisc_1(k2_zfmisc_1(A_288,B_287)))
      | ~ v1_funct_1(E_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2659,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2427,c_2619])).

tff(c_2682,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_82,c_78,c_2659])).

tff(c_2684,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2432,c_2682])).

tff(c_2685,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2247])).

tff(c_2755,plain,(
    ! [A_304,D_308,C_306,F_305,E_307,B_309] :
      ( k1_partfun1(A_304,B_309,C_306,D_308,E_307,F_305) = k5_relat_1(E_307,F_305)
      | ~ m1_subset_1(F_305,k1_zfmisc_1(k2_zfmisc_1(C_306,D_308)))
      | ~ v1_funct_1(F_305)
      | ~ m1_subset_1(E_307,k1_zfmisc_1(k2_zfmisc_1(A_304,B_309)))
      | ~ v1_funct_1(E_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2761,plain,(
    ! [A_304,B_309,E_307] :
      ( k1_partfun1(A_304,B_309,'#skF_2','#skF_1',E_307,'#skF_4') = k5_relat_1(E_307,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_307,k1_zfmisc_1(k2_zfmisc_1(A_304,B_309)))
      | ~ v1_funct_1(E_307) ) ),
    inference(resolution,[status(thm)],[c_78,c_2755])).

tff(c_2794,plain,(
    ! [A_316,B_317,E_318] :
      ( k1_partfun1(A_316,B_317,'#skF_2','#skF_1',E_318,'#skF_4') = k5_relat_1(E_318,'#skF_4')
      | ~ m1_subset_1(E_318,k1_zfmisc_1(k2_zfmisc_1(A_316,B_317)))
      | ~ v1_funct_1(E_318) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2761])).

tff(c_2800,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_2794])).

tff(c_2807,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2685,c_2800])).

tff(c_14,plain,(
    ! [A_6,B_8] :
      ( v2_funct_1(A_6)
      | k2_relat_1(B_8) != k1_relat_1(A_6)
      | ~ v2_funct_1(k5_relat_1(B_8,A_6))
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2817,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2807,c_14])).

tff(c_2823,plain,
    ( v2_funct_1('#skF_4')
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_82,c_148,c_88,c_2040,c_2817])).

tff(c_2825,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2823])).

tff(c_2719,plain,(
    ! [A_296,F_297,C_299,D_294,E_298,B_295] :
      ( v1_funct_1(k1_partfun1(A_296,B_295,C_299,D_294,E_298,F_297))
      | ~ m1_subset_1(F_297,k1_zfmisc_1(k2_zfmisc_1(C_299,D_294)))
      | ~ v1_funct_1(F_297)
      | ~ m1_subset_1(E_298,k1_zfmisc_1(k2_zfmisc_1(A_296,B_295)))
      | ~ v1_funct_1(E_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2725,plain,(
    ! [A_296,B_295,E_298] :
      ( v1_funct_1(k1_partfun1(A_296,B_295,'#skF_2','#skF_1',E_298,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_298,k1_zfmisc_1(k2_zfmisc_1(A_296,B_295)))
      | ~ v1_funct_1(E_298) ) ),
    inference(resolution,[status(thm)],[c_78,c_2719])).

tff(c_2770,plain,(
    ! [A_311,B_312,E_313] :
      ( v1_funct_1(k1_partfun1(A_311,B_312,'#skF_2','#skF_1',E_313,'#skF_4'))
      | ~ m1_subset_1(E_313,k1_zfmisc_1(k2_zfmisc_1(A_311,B_312)))
      | ~ v1_funct_1(E_313) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2725])).

tff(c_2776,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_2770])).

tff(c_2783,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2685,c_2776])).

tff(c_72,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_86,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_2887,plain,(
    ! [A_323,C_324,B_325] :
      ( k6_partfun1(A_323) = k5_relat_1(C_324,k2_funct_1(C_324))
      | k1_xboole_0 = B_325
      | ~ v2_funct_1(C_324)
      | k2_relset_1(A_323,B_325,C_324) != B_325
      | ~ m1_subset_1(C_324,k1_zfmisc_1(k2_zfmisc_1(A_323,B_325)))
      | ~ v1_funct_2(C_324,A_323,B_325)
      | ~ v1_funct_1(C_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_2891,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_2887])).

tff(c_2899,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_76,c_72,c_2891])).

tff(c_2900,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2899])).

tff(c_20,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k2_funct_1(A_9)) = k6_relat_1(k1_relat_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_91,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k2_funct_1(A_9)) = k6_partfun1(k1_relat_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_20])).

tff(c_2916,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2900,c_91])).

tff(c_2930,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_88,c_72,c_2916])).

tff(c_147,plain,(
    ! [A_26] : v1_relat_1(k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_89,c_137])).

tff(c_10,plain,(
    ! [A_3] : k2_relat_1(k6_relat_1(A_3)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_94,plain,(
    ! [A_3] : k2_relat_1(k6_partfun1(A_3)) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( k5_relat_1(k6_relat_1(A_4),B_5) = B_5
      | ~ r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2053,plain,(
    ! [A_229,B_230] :
      ( k5_relat_1(k6_partfun1(A_229),B_230) = B_230
      | ~ r1_tarski(k1_relat_1(B_230),A_229)
      | ~ v1_relat_1(B_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_12])).

tff(c_2063,plain,(
    ! [B_230] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(B_230)),B_230) = B_230
      | ~ v1_relat_1(B_230) ) ),
    inference(resolution,[status(thm)],[c_6,c_2053])).

tff(c_2194,plain,(
    ! [B_243,A_244] :
      ( v2_funct_1(B_243)
      | k2_relat_1(B_243) != k1_relat_1(A_244)
      | ~ v2_funct_1(k5_relat_1(B_243,A_244))
      | ~ v1_funct_1(B_243)
      | ~ v1_relat_1(B_243)
      | ~ v1_funct_1(A_244)
      | ~ v1_relat_1(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2209,plain,(
    ! [B_230] :
      ( v2_funct_1(k6_partfun1(k1_relat_1(B_230)))
      | k2_relat_1(k6_partfun1(k1_relat_1(B_230))) != k1_relat_1(B_230)
      | ~ v2_funct_1(B_230)
      | ~ v1_funct_1(k6_partfun1(k1_relat_1(B_230)))
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(B_230)))
      | ~ v1_funct_1(B_230)
      | ~ v1_relat_1(B_230)
      | ~ v1_relat_1(B_230) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2063,c_2194])).

tff(c_2217,plain,(
    ! [B_230] :
      ( v2_funct_1(k6_partfun1(k1_relat_1(B_230)))
      | ~ v2_funct_1(B_230)
      | ~ v1_funct_1(k6_partfun1(k1_relat_1(B_230)))
      | ~ v1_funct_1(B_230)
      | ~ v1_relat_1(B_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_94,c_2209])).

tff(c_2953,plain,
    ( v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1(k6_partfun1(k1_relat_1('#skF_3')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2930,c_2217])).

tff(c_3013,plain,(
    v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_88,c_2783,c_2930,c_72,c_2953])).

tff(c_3015,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2825,c_3013])).

tff(c_3016,plain,
    ( k1_relat_1('#skF_4') != '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2823])).

tff(c_3029,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3016])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_80,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_163,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_151])).

tff(c_202,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_163,c_196])).

tff(c_211,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_202])).

tff(c_215,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_186,plain,(
    ! [A_78,B_79,D_80] :
      ( r2_relset_1(A_78,B_79,D_80,D_80)
      | ~ m1_subset_1(D_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_193,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_89,c_186])).

tff(c_600,plain,(
    ! [C_133,B_136,E_134,A_131,F_132,D_135] :
      ( k1_partfun1(A_131,B_136,C_133,D_135,E_134,F_132) = k5_relat_1(E_134,F_132)
      | ~ m1_subset_1(F_132,k1_zfmisc_1(k2_zfmisc_1(C_133,D_135)))
      | ~ v1_funct_1(F_132)
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_131,B_136)))
      | ~ v1_funct_1(E_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_606,plain,(
    ! [A_131,B_136,E_134] :
      ( k1_partfun1(A_131,B_136,'#skF_2','#skF_1',E_134,'#skF_4') = k5_relat_1(E_134,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_131,B_136)))
      | ~ v1_funct_1(E_134) ) ),
    inference(resolution,[status(thm)],[c_78,c_600])).

tff(c_686,plain,(
    ! [A_145,B_146,E_147] :
      ( k1_partfun1(A_145,B_146,'#skF_2','#skF_1',E_147,'#skF_4') = k5_relat_1(E_147,'#skF_4')
      | ~ m1_subset_1(E_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ v1_funct_1(E_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_606])).

tff(c_692,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_686])).

tff(c_699,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_692])).

tff(c_496,plain,(
    ! [D_111,C_112,A_113,B_114] :
      ( D_111 = C_112
      | ~ r2_relset_1(A_113,B_114,C_112,D_111)
      | ~ m1_subset_1(D_111,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114)))
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_504,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_74,c_496])).

tff(c_519,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_504])).

tff(c_520,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_519])).

tff(c_704,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_520])).

tff(c_891,plain,(
    ! [E_155,F_154,B_152,D_151,C_156,A_153] :
      ( m1_subset_1(k1_partfun1(A_153,B_152,C_156,D_151,E_155,F_154),k1_zfmisc_1(k2_zfmisc_1(A_153,D_151)))
      | ~ m1_subset_1(F_154,k1_zfmisc_1(k2_zfmisc_1(C_156,D_151)))
      | ~ v1_funct_1(F_154)
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_152)))
      | ~ v1_funct_1(E_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_931,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_699,c_891])).

tff(c_954,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_82,c_78,c_931])).

tff(c_956,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_704,c_954])).

tff(c_957,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_519])).

tff(c_1953,plain,(
    ! [D_216,A_217,B_218,C_219] :
      ( v2_funct_2(D_216,A_217)
      | ~ r2_relset_1(A_217,A_217,k1_partfun1(A_217,B_218,B_218,A_217,C_219,D_216),k6_partfun1(A_217))
      | ~ m1_subset_1(D_216,k1_zfmisc_1(k2_zfmisc_1(B_218,A_217)))
      | ~ v1_funct_2(D_216,B_218,A_217)
      | ~ v1_funct_1(D_216)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218)))
      | ~ v1_funct_2(C_219,A_217,B_218)
      | ~ v1_funct_1(C_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1959,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_957,c_1953])).

tff(c_1963,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_82,c_80,c_78,c_193,c_1959])).

tff(c_1965,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_215,c_1963])).

tff(c_1966,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_2123,plain,(
    ! [A_235,B_236,C_237] :
      ( k2_relset_1(A_235,B_236,C_237) = k2_relat_1(C_237)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2132,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_2123])).

tff(c_2138,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1966,c_2132])).

tff(c_3048,plain,(
    ! [B_327,C_328,A_329] :
      ( k6_partfun1(B_327) = k5_relat_1(k2_funct_1(C_328),C_328)
      | k1_xboole_0 = B_327
      | ~ v2_funct_1(C_328)
      | k2_relset_1(A_329,B_327,C_328) != B_327
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_329,B_327)))
      | ~ v1_funct_2(C_328,A_329,B_327)
      | ~ v1_funct_1(C_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_3054,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_3048])).

tff(c_3064,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_2138,c_3054])).

tff(c_3065,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3064])).

tff(c_3090,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3065])).

tff(c_3017,plain,(
    v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2823])).

tff(c_3795,plain,(
    ! [D_365,A_364,C_368,B_367,E_366] :
      ( k1_xboole_0 = C_368
      | v2_funct_1(E_366)
      | k2_relset_1(A_364,B_367,D_365) != B_367
      | ~ v2_funct_1(k1_partfun1(A_364,B_367,B_367,C_368,D_365,E_366))
      | ~ m1_subset_1(E_366,k1_zfmisc_1(k2_zfmisc_1(B_367,C_368)))
      | ~ v1_funct_2(E_366,B_367,C_368)
      | ~ v1_funct_1(E_366)
      | ~ m1_subset_1(D_365,k1_zfmisc_1(k2_zfmisc_1(A_364,B_367)))
      | ~ v1_funct_2(D_365,A_364,B_367)
      | ~ v1_funct_1(D_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_3799,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2685,c_3795])).

tff(c_3804,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_82,c_80,c_78,c_3017,c_76,c_3799])).

tff(c_3806,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3090,c_70,c_3804])).

tff(c_3808,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3065])).

tff(c_3869,plain,(
    ! [A_372,C_373,B_374] :
      ( k6_partfun1(A_372) = k5_relat_1(C_373,k2_funct_1(C_373))
      | k1_xboole_0 = B_374
      | ~ v2_funct_1(C_373)
      | k2_relset_1(A_372,B_374,C_373) != B_374
      | ~ m1_subset_1(C_373,k1_zfmisc_1(k2_zfmisc_1(A_372,B_374)))
      | ~ v1_funct_2(C_373,A_372,B_374)
      | ~ v1_funct_1(C_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_3875,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_3869])).

tff(c_3885,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_2138,c_3808,c_3875])).

tff(c_3886,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3885])).

tff(c_4051,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_3886])).

tff(c_4064,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_82,c_3808,c_4051])).

tff(c_4217,plain,(
    k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4064,c_94])).

tff(c_4241,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_4217])).

tff(c_4243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3029,c_4241])).

tff(c_4245,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3016])).

tff(c_4441,plain,(
    ! [A_388,C_389,B_390] :
      ( k6_partfun1(A_388) = k5_relat_1(C_389,k2_funct_1(C_389))
      | k1_xboole_0 = B_390
      | ~ v2_funct_1(C_389)
      | k2_relset_1(A_388,B_390,C_389) != B_390
      | ~ m1_subset_1(C_389,k1_zfmisc_1(k2_zfmisc_1(A_388,B_390)))
      | ~ v1_funct_2(C_389,A_388,B_390)
      | ~ v1_funct_1(C_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_4445,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_4441])).

tff(c_4453,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_76,c_72,c_4445])).

tff(c_4454,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4453])).

tff(c_4470,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4454,c_91])).

tff(c_4484,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_88,c_72,c_4470])).

tff(c_22,plain,(
    ! [A_10,B_12] :
      ( k2_funct_1(A_10) = B_12
      | k6_relat_1(k1_relat_1(A_10)) != k5_relat_1(A_10,B_12)
      | k2_relat_1(A_10) != k1_relat_1(B_12)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_90,plain,(
    ! [A_10,B_12] :
      ( k2_funct_1(A_10) = B_12
      | k6_partfun1(k1_relat_1(A_10)) != k5_relat_1(A_10,B_12)
      | k2_relat_1(A_10) != k1_relat_1(B_12)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_22])).

tff(c_4505,plain,(
    ! [B_12] :
      ( k2_funct_1('#skF_3') = B_12
      | k5_relat_1('#skF_3',B_12) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_12)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4484,c_90])).

tff(c_6461,plain,(
    ! [B_480] :
      ( k2_funct_1('#skF_3') = B_480
      | k5_relat_1('#skF_3',B_480) != k6_partfun1('#skF_1')
      | k1_relat_1(B_480) != '#skF_2'
      | ~ v1_funct_1(B_480)
      | ~ v1_relat_1(B_480) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_88,c_72,c_2040,c_4505])).

tff(c_6497,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_149,c_6461])).

tff(c_6535,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4245,c_2807,c_6497])).

tff(c_6537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_6535])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:11:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.70/2.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.70/2.75  
% 7.70/2.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.70/2.75  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.70/2.75  
% 7.70/2.75  %Foreground sorts:
% 7.70/2.75  
% 7.70/2.75  
% 7.70/2.75  %Background operators:
% 7.70/2.75  
% 7.70/2.75  
% 7.70/2.75  %Foreground operators:
% 7.70/2.75  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.70/2.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.70/2.75  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.70/2.75  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.70/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.70/2.75  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.70/2.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.70/2.75  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.70/2.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.70/2.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.70/2.75  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.70/2.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.70/2.75  tff('#skF_2', type, '#skF_2': $i).
% 7.70/2.75  tff('#skF_3', type, '#skF_3': $i).
% 7.70/2.75  tff('#skF_1', type, '#skF_1': $i).
% 7.70/2.75  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.70/2.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.70/2.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.70/2.75  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.70/2.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.70/2.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.70/2.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.70/2.75  tff('#skF_4', type, '#skF_4': $i).
% 7.70/2.75  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.70/2.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.70/2.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.70/2.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.70/2.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.70/2.75  
% 7.87/2.78  tff(f_228, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 7.87/2.78  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.87/2.78  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.87/2.78  tff(f_117, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 7.87/2.78  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.87/2.78  tff(f_139, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.87/2.78  tff(f_141, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.87/2.78  tff(f_109, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 7.87/2.78  tff(f_107, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.87/2.78  tff(f_129, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.87/2.78  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 7.87/2.78  tff(f_202, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 7.87/2.78  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 7.87/2.78  tff(f_35, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.87/2.78  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.87/2.78  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 7.87/2.78  tff(f_160, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 7.87/2.78  tff(f_186, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 7.87/2.78  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 7.87/2.78  tff(c_66, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_228])).
% 7.87/2.78  tff(c_82, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_228])).
% 7.87/2.78  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_228])).
% 7.87/2.78  tff(c_137, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.87/2.78  tff(c_149, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_137])).
% 7.87/2.78  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_228])).
% 7.87/2.78  tff(c_148, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_137])).
% 7.87/2.78  tff(c_88, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_228])).
% 7.87/2.78  tff(c_151, plain, (![C_68, B_69, A_70]: (v5_relat_1(C_68, B_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.87/2.78  tff(c_162, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_84, c_151])).
% 7.87/2.78  tff(c_196, plain, (![B_81, A_82]: (k2_relat_1(B_81)=A_82 | ~v2_funct_2(B_81, A_82) | ~v5_relat_1(B_81, A_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.87/2.78  tff(c_205, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_162, c_196])).
% 7.87/2.78  tff(c_214, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_205])).
% 7.87/2.78  tff(c_1978, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_214])).
% 7.87/2.78  tff(c_76, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_228])).
% 7.87/2.78  tff(c_2014, plain, (![A_225, B_226, C_227]: (k2_relset_1(A_225, B_226, C_227)=k2_relat_1(C_227) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.87/2.78  tff(c_2020, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_2014])).
% 7.87/2.78  tff(c_2027, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2020])).
% 7.87/2.78  tff(c_38, plain, (![B_28]: (v2_funct_2(B_28, k2_relat_1(B_28)) | ~v5_relat_1(B_28, k2_relat_1(B_28)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.87/2.78  tff(c_2033, plain, (v2_funct_2('#skF_3', k2_relat_1('#skF_3')) | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2027, c_38])).
% 7.87/2.78  tff(c_2037, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_162, c_2027, c_2033])).
% 7.87/2.78  tff(c_2039, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1978, c_2037])).
% 7.87/2.78  tff(c_2040, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_214])).
% 7.87/2.78  tff(c_2328, plain, (![A_266, D_270, E_269, F_267, C_268, B_271]: (k1_partfun1(A_266, B_271, C_268, D_270, E_269, F_267)=k5_relat_1(E_269, F_267) | ~m1_subset_1(F_267, k1_zfmisc_1(k2_zfmisc_1(C_268, D_270))) | ~v1_funct_1(F_267) | ~m1_subset_1(E_269, k1_zfmisc_1(k2_zfmisc_1(A_266, B_271))) | ~v1_funct_1(E_269))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.87/2.78  tff(c_2334, plain, (![A_266, B_271, E_269]: (k1_partfun1(A_266, B_271, '#skF_2', '#skF_1', E_269, '#skF_4')=k5_relat_1(E_269, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_269, k1_zfmisc_1(k2_zfmisc_1(A_266, B_271))) | ~v1_funct_1(E_269))), inference(resolution, [status(thm)], [c_78, c_2328])).
% 7.87/2.78  tff(c_2414, plain, (![A_280, B_281, E_282]: (k1_partfun1(A_280, B_281, '#skF_2', '#skF_1', E_282, '#skF_4')=k5_relat_1(E_282, '#skF_4') | ~m1_subset_1(E_282, k1_zfmisc_1(k2_zfmisc_1(A_280, B_281))) | ~v1_funct_1(E_282))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2334])).
% 7.87/2.78  tff(c_2420, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_2414])).
% 7.87/2.78  tff(c_2427, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2420])).
% 7.87/2.78  tff(c_48, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.87/2.78  tff(c_36, plain, (![A_26]: (m1_subset_1(k6_relat_1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.87/2.78  tff(c_89, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36])).
% 7.87/2.78  tff(c_74, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_228])).
% 7.87/2.78  tff(c_2224, plain, (![D_246, C_247, A_248, B_249]: (D_246=C_247 | ~r2_relset_1(A_248, B_249, C_247, D_246) | ~m1_subset_1(D_246, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.87/2.78  tff(c_2232, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_74, c_2224])).
% 7.87/2.78  tff(c_2247, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_2232])).
% 7.87/2.78  tff(c_2248, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2247])).
% 7.87/2.78  tff(c_2432, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2427, c_2248])).
% 7.87/2.78  tff(c_2619, plain, (![F_289, E_290, A_288, B_287, C_291, D_286]: (m1_subset_1(k1_partfun1(A_288, B_287, C_291, D_286, E_290, F_289), k1_zfmisc_1(k2_zfmisc_1(A_288, D_286))) | ~m1_subset_1(F_289, k1_zfmisc_1(k2_zfmisc_1(C_291, D_286))) | ~v1_funct_1(F_289) | ~m1_subset_1(E_290, k1_zfmisc_1(k2_zfmisc_1(A_288, B_287))) | ~v1_funct_1(E_290))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.87/2.78  tff(c_2659, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2427, c_2619])).
% 7.87/2.78  tff(c_2682, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_82, c_78, c_2659])).
% 7.87/2.78  tff(c_2684, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2432, c_2682])).
% 7.87/2.78  tff(c_2685, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2247])).
% 7.87/2.78  tff(c_2755, plain, (![A_304, D_308, C_306, F_305, E_307, B_309]: (k1_partfun1(A_304, B_309, C_306, D_308, E_307, F_305)=k5_relat_1(E_307, F_305) | ~m1_subset_1(F_305, k1_zfmisc_1(k2_zfmisc_1(C_306, D_308))) | ~v1_funct_1(F_305) | ~m1_subset_1(E_307, k1_zfmisc_1(k2_zfmisc_1(A_304, B_309))) | ~v1_funct_1(E_307))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.87/2.78  tff(c_2761, plain, (![A_304, B_309, E_307]: (k1_partfun1(A_304, B_309, '#skF_2', '#skF_1', E_307, '#skF_4')=k5_relat_1(E_307, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_307, k1_zfmisc_1(k2_zfmisc_1(A_304, B_309))) | ~v1_funct_1(E_307))), inference(resolution, [status(thm)], [c_78, c_2755])).
% 7.87/2.78  tff(c_2794, plain, (![A_316, B_317, E_318]: (k1_partfun1(A_316, B_317, '#skF_2', '#skF_1', E_318, '#skF_4')=k5_relat_1(E_318, '#skF_4') | ~m1_subset_1(E_318, k1_zfmisc_1(k2_zfmisc_1(A_316, B_317))) | ~v1_funct_1(E_318))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2761])).
% 7.87/2.78  tff(c_2800, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_2794])).
% 7.87/2.78  tff(c_2807, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2685, c_2800])).
% 7.87/2.78  tff(c_14, plain, (![A_6, B_8]: (v2_funct_1(A_6) | k2_relat_1(B_8)!=k1_relat_1(A_6) | ~v2_funct_1(k5_relat_1(B_8, A_6)) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.87/2.78  tff(c_2817, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2807, c_14])).
% 7.87/2.78  tff(c_2823, plain, (v2_funct_1('#skF_4') | k1_relat_1('#skF_4')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_82, c_148, c_88, c_2040, c_2817])).
% 7.87/2.78  tff(c_2825, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_2823])).
% 7.87/2.78  tff(c_2719, plain, (![A_296, F_297, C_299, D_294, E_298, B_295]: (v1_funct_1(k1_partfun1(A_296, B_295, C_299, D_294, E_298, F_297)) | ~m1_subset_1(F_297, k1_zfmisc_1(k2_zfmisc_1(C_299, D_294))) | ~v1_funct_1(F_297) | ~m1_subset_1(E_298, k1_zfmisc_1(k2_zfmisc_1(A_296, B_295))) | ~v1_funct_1(E_298))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.87/2.78  tff(c_2725, plain, (![A_296, B_295, E_298]: (v1_funct_1(k1_partfun1(A_296, B_295, '#skF_2', '#skF_1', E_298, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_298, k1_zfmisc_1(k2_zfmisc_1(A_296, B_295))) | ~v1_funct_1(E_298))), inference(resolution, [status(thm)], [c_78, c_2719])).
% 7.87/2.78  tff(c_2770, plain, (![A_311, B_312, E_313]: (v1_funct_1(k1_partfun1(A_311, B_312, '#skF_2', '#skF_1', E_313, '#skF_4')) | ~m1_subset_1(E_313, k1_zfmisc_1(k2_zfmisc_1(A_311, B_312))) | ~v1_funct_1(E_313))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2725])).
% 7.87/2.78  tff(c_2776, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_2770])).
% 7.87/2.78  tff(c_2783, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2685, c_2776])).
% 7.87/2.78  tff(c_72, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_228])).
% 7.87/2.78  tff(c_68, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_228])).
% 7.87/2.78  tff(c_86, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_228])).
% 7.87/2.78  tff(c_2887, plain, (![A_323, C_324, B_325]: (k6_partfun1(A_323)=k5_relat_1(C_324, k2_funct_1(C_324)) | k1_xboole_0=B_325 | ~v2_funct_1(C_324) | k2_relset_1(A_323, B_325, C_324)!=B_325 | ~m1_subset_1(C_324, k1_zfmisc_1(k2_zfmisc_1(A_323, B_325))) | ~v1_funct_2(C_324, A_323, B_325) | ~v1_funct_1(C_324))), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.87/2.78  tff(c_2891, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_2887])).
% 7.87/2.78  tff(c_2899, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_76, c_72, c_2891])).
% 7.87/2.78  tff(c_2900, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_2899])).
% 7.87/2.78  tff(c_20, plain, (![A_9]: (k5_relat_1(A_9, k2_funct_1(A_9))=k6_relat_1(k1_relat_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.87/2.78  tff(c_91, plain, (![A_9]: (k5_relat_1(A_9, k2_funct_1(A_9))=k6_partfun1(k1_relat_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_20])).
% 7.87/2.78  tff(c_2916, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2900, c_91])).
% 7.87/2.78  tff(c_2930, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_88, c_72, c_2916])).
% 7.87/2.78  tff(c_147, plain, (![A_26]: (v1_relat_1(k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_89, c_137])).
% 7.87/2.78  tff(c_10, plain, (![A_3]: (k2_relat_1(k6_relat_1(A_3))=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.87/2.78  tff(c_94, plain, (![A_3]: (k2_relat_1(k6_partfun1(A_3))=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10])).
% 7.87/2.78  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.87/2.78  tff(c_12, plain, (![A_4, B_5]: (k5_relat_1(k6_relat_1(A_4), B_5)=B_5 | ~r1_tarski(k1_relat_1(B_5), A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.87/2.78  tff(c_2053, plain, (![A_229, B_230]: (k5_relat_1(k6_partfun1(A_229), B_230)=B_230 | ~r1_tarski(k1_relat_1(B_230), A_229) | ~v1_relat_1(B_230))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_12])).
% 7.87/2.78  tff(c_2063, plain, (![B_230]: (k5_relat_1(k6_partfun1(k1_relat_1(B_230)), B_230)=B_230 | ~v1_relat_1(B_230))), inference(resolution, [status(thm)], [c_6, c_2053])).
% 7.87/2.78  tff(c_2194, plain, (![B_243, A_244]: (v2_funct_1(B_243) | k2_relat_1(B_243)!=k1_relat_1(A_244) | ~v2_funct_1(k5_relat_1(B_243, A_244)) | ~v1_funct_1(B_243) | ~v1_relat_1(B_243) | ~v1_funct_1(A_244) | ~v1_relat_1(A_244))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.87/2.78  tff(c_2209, plain, (![B_230]: (v2_funct_1(k6_partfun1(k1_relat_1(B_230))) | k2_relat_1(k6_partfun1(k1_relat_1(B_230)))!=k1_relat_1(B_230) | ~v2_funct_1(B_230) | ~v1_funct_1(k6_partfun1(k1_relat_1(B_230))) | ~v1_relat_1(k6_partfun1(k1_relat_1(B_230))) | ~v1_funct_1(B_230) | ~v1_relat_1(B_230) | ~v1_relat_1(B_230))), inference(superposition, [status(thm), theory('equality')], [c_2063, c_2194])).
% 7.87/2.78  tff(c_2217, plain, (![B_230]: (v2_funct_1(k6_partfun1(k1_relat_1(B_230))) | ~v2_funct_1(B_230) | ~v1_funct_1(k6_partfun1(k1_relat_1(B_230))) | ~v1_funct_1(B_230) | ~v1_relat_1(B_230))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_94, c_2209])).
% 7.87/2.78  tff(c_2953, plain, (v2_funct_1(k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_3') | ~v1_funct_1(k6_partfun1(k1_relat_1('#skF_3'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2930, c_2217])).
% 7.87/2.78  tff(c_3013, plain, (v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_88, c_2783, c_2930, c_72, c_2953])).
% 7.87/2.78  tff(c_3015, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2825, c_3013])).
% 7.87/2.78  tff(c_3016, plain, (k1_relat_1('#skF_4')!='#skF_2' | v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2823])).
% 7.87/2.78  tff(c_3029, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_3016])).
% 7.87/2.78  tff(c_70, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_228])).
% 7.87/2.78  tff(c_80, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_228])).
% 7.87/2.78  tff(c_163, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_151])).
% 7.87/2.78  tff(c_202, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_163, c_196])).
% 7.87/2.78  tff(c_211, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_202])).
% 7.87/2.78  tff(c_215, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_211])).
% 7.87/2.78  tff(c_186, plain, (![A_78, B_79, D_80]: (r2_relset_1(A_78, B_79, D_80, D_80) | ~m1_subset_1(D_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.87/2.78  tff(c_193, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_89, c_186])).
% 7.87/2.78  tff(c_600, plain, (![C_133, B_136, E_134, A_131, F_132, D_135]: (k1_partfun1(A_131, B_136, C_133, D_135, E_134, F_132)=k5_relat_1(E_134, F_132) | ~m1_subset_1(F_132, k1_zfmisc_1(k2_zfmisc_1(C_133, D_135))) | ~v1_funct_1(F_132) | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_131, B_136))) | ~v1_funct_1(E_134))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.87/2.78  tff(c_606, plain, (![A_131, B_136, E_134]: (k1_partfun1(A_131, B_136, '#skF_2', '#skF_1', E_134, '#skF_4')=k5_relat_1(E_134, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_131, B_136))) | ~v1_funct_1(E_134))), inference(resolution, [status(thm)], [c_78, c_600])).
% 7.87/2.78  tff(c_686, plain, (![A_145, B_146, E_147]: (k1_partfun1(A_145, B_146, '#skF_2', '#skF_1', E_147, '#skF_4')=k5_relat_1(E_147, '#skF_4') | ~m1_subset_1(E_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~v1_funct_1(E_147))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_606])).
% 7.87/2.78  tff(c_692, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_686])).
% 7.87/2.78  tff(c_699, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_692])).
% 7.87/2.78  tff(c_496, plain, (![D_111, C_112, A_113, B_114]: (D_111=C_112 | ~r2_relset_1(A_113, B_114, C_112, D_111) | ~m1_subset_1(D_111, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.87/2.78  tff(c_504, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_74, c_496])).
% 7.87/2.78  tff(c_519, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_504])).
% 7.87/2.78  tff(c_520, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_519])).
% 7.87/2.78  tff(c_704, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_699, c_520])).
% 7.87/2.78  tff(c_891, plain, (![E_155, F_154, B_152, D_151, C_156, A_153]: (m1_subset_1(k1_partfun1(A_153, B_152, C_156, D_151, E_155, F_154), k1_zfmisc_1(k2_zfmisc_1(A_153, D_151))) | ~m1_subset_1(F_154, k1_zfmisc_1(k2_zfmisc_1(C_156, D_151))) | ~v1_funct_1(F_154) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_152))) | ~v1_funct_1(E_155))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.87/2.78  tff(c_931, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_699, c_891])).
% 7.87/2.78  tff(c_954, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_82, c_78, c_931])).
% 7.87/2.78  tff(c_956, plain, $false, inference(negUnitSimplification, [status(thm)], [c_704, c_954])).
% 7.87/2.78  tff(c_957, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_519])).
% 7.87/2.78  tff(c_1953, plain, (![D_216, A_217, B_218, C_219]: (v2_funct_2(D_216, A_217) | ~r2_relset_1(A_217, A_217, k1_partfun1(A_217, B_218, B_218, A_217, C_219, D_216), k6_partfun1(A_217)) | ~m1_subset_1(D_216, k1_zfmisc_1(k2_zfmisc_1(B_218, A_217))) | ~v1_funct_2(D_216, B_218, A_217) | ~v1_funct_1(D_216) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))) | ~v1_funct_2(C_219, A_217, B_218) | ~v1_funct_1(C_219))), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.87/2.78  tff(c_1959, plain, (v2_funct_2('#skF_4', '#skF_1') | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_957, c_1953])).
% 7.87/2.78  tff(c_1963, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_82, c_80, c_78, c_193, c_1959])).
% 7.87/2.78  tff(c_1965, plain, $false, inference(negUnitSimplification, [status(thm)], [c_215, c_1963])).
% 7.87/2.78  tff(c_1966, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_211])).
% 7.87/2.78  tff(c_2123, plain, (![A_235, B_236, C_237]: (k2_relset_1(A_235, B_236, C_237)=k2_relat_1(C_237) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.87/2.78  tff(c_2132, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_2123])).
% 7.87/2.78  tff(c_2138, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1966, c_2132])).
% 7.87/2.78  tff(c_3048, plain, (![B_327, C_328, A_329]: (k6_partfun1(B_327)=k5_relat_1(k2_funct_1(C_328), C_328) | k1_xboole_0=B_327 | ~v2_funct_1(C_328) | k2_relset_1(A_329, B_327, C_328)!=B_327 | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_329, B_327))) | ~v1_funct_2(C_328, A_329, B_327) | ~v1_funct_1(C_328))), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.87/2.78  tff(c_3054, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_3048])).
% 7.87/2.78  tff(c_3064, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_2138, c_3054])).
% 7.87/2.78  tff(c_3065, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_70, c_3064])).
% 7.87/2.78  tff(c_3090, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_3065])).
% 7.87/2.78  tff(c_3017, plain, (v2_funct_1(k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_2823])).
% 7.87/2.78  tff(c_3795, plain, (![D_365, A_364, C_368, B_367, E_366]: (k1_xboole_0=C_368 | v2_funct_1(E_366) | k2_relset_1(A_364, B_367, D_365)!=B_367 | ~v2_funct_1(k1_partfun1(A_364, B_367, B_367, C_368, D_365, E_366)) | ~m1_subset_1(E_366, k1_zfmisc_1(k2_zfmisc_1(B_367, C_368))) | ~v1_funct_2(E_366, B_367, C_368) | ~v1_funct_1(E_366) | ~m1_subset_1(D_365, k1_zfmisc_1(k2_zfmisc_1(A_364, B_367))) | ~v1_funct_2(D_365, A_364, B_367) | ~v1_funct_1(D_365))), inference(cnfTransformation, [status(thm)], [f_186])).
% 7.87/2.78  tff(c_3799, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2685, c_3795])).
% 7.87/2.78  tff(c_3804, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_82, c_80, c_78, c_3017, c_76, c_3799])).
% 7.87/2.78  tff(c_3806, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3090, c_70, c_3804])).
% 7.87/2.78  tff(c_3808, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_3065])).
% 7.87/2.78  tff(c_3869, plain, (![A_372, C_373, B_374]: (k6_partfun1(A_372)=k5_relat_1(C_373, k2_funct_1(C_373)) | k1_xboole_0=B_374 | ~v2_funct_1(C_373) | k2_relset_1(A_372, B_374, C_373)!=B_374 | ~m1_subset_1(C_373, k1_zfmisc_1(k2_zfmisc_1(A_372, B_374))) | ~v1_funct_2(C_373, A_372, B_374) | ~v1_funct_1(C_373))), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.87/2.78  tff(c_3875, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_3869])).
% 7.87/2.78  tff(c_3885, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_2138, c_3808, c_3875])).
% 7.87/2.78  tff(c_3886, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_70, c_3885])).
% 7.87/2.78  tff(c_4051, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_91, c_3886])).
% 7.87/2.78  tff(c_4064, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_82, c_3808, c_4051])).
% 7.87/2.78  tff(c_4217, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4064, c_94])).
% 7.87/2.78  tff(c_4241, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_4217])).
% 7.87/2.78  tff(c_4243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3029, c_4241])).
% 7.87/2.78  tff(c_4245, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_3016])).
% 7.87/2.78  tff(c_4441, plain, (![A_388, C_389, B_390]: (k6_partfun1(A_388)=k5_relat_1(C_389, k2_funct_1(C_389)) | k1_xboole_0=B_390 | ~v2_funct_1(C_389) | k2_relset_1(A_388, B_390, C_389)!=B_390 | ~m1_subset_1(C_389, k1_zfmisc_1(k2_zfmisc_1(A_388, B_390))) | ~v1_funct_2(C_389, A_388, B_390) | ~v1_funct_1(C_389))), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.87/2.78  tff(c_4445, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_4441])).
% 7.87/2.78  tff(c_4453, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_76, c_72, c_4445])).
% 7.87/2.78  tff(c_4454, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_4453])).
% 7.87/2.78  tff(c_4470, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4454, c_91])).
% 7.87/2.78  tff(c_4484, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_88, c_72, c_4470])).
% 7.87/2.78  tff(c_22, plain, (![A_10, B_12]: (k2_funct_1(A_10)=B_12 | k6_relat_1(k1_relat_1(A_10))!=k5_relat_1(A_10, B_12) | k2_relat_1(A_10)!=k1_relat_1(B_12) | ~v2_funct_1(A_10) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.87/2.78  tff(c_90, plain, (![A_10, B_12]: (k2_funct_1(A_10)=B_12 | k6_partfun1(k1_relat_1(A_10))!=k5_relat_1(A_10, B_12) | k2_relat_1(A_10)!=k1_relat_1(B_12) | ~v2_funct_1(A_10) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_22])).
% 7.87/2.78  tff(c_4505, plain, (![B_12]: (k2_funct_1('#skF_3')=B_12 | k5_relat_1('#skF_3', B_12)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_12) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4484, c_90])).
% 7.87/2.78  tff(c_6461, plain, (![B_480]: (k2_funct_1('#skF_3')=B_480 | k5_relat_1('#skF_3', B_480)!=k6_partfun1('#skF_1') | k1_relat_1(B_480)!='#skF_2' | ~v1_funct_1(B_480) | ~v1_relat_1(B_480))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_88, c_72, c_2040, c_4505])).
% 7.87/2.78  tff(c_6497, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_149, c_6461])).
% 7.87/2.78  tff(c_6535, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_4245, c_2807, c_6497])).
% 7.87/2.78  tff(c_6537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_6535])).
% 7.87/2.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.87/2.78  
% 7.87/2.78  Inference rules
% 7.87/2.78  ----------------------
% 7.87/2.78  #Ref     : 0
% 7.87/2.78  #Sup     : 1419
% 7.87/2.78  #Fact    : 0
% 7.87/2.78  #Define  : 0
% 7.87/2.78  #Split   : 47
% 7.87/2.78  #Chain   : 0
% 7.87/2.78  #Close   : 0
% 7.87/2.78  
% 7.87/2.78  Ordering : KBO
% 7.87/2.78  
% 7.87/2.78  Simplification rules
% 7.87/2.78  ----------------------
% 7.87/2.78  #Subsume      : 67
% 7.87/2.78  #Demod        : 2336
% 7.87/2.78  #Tautology    : 547
% 7.87/2.78  #SimpNegUnit  : 90
% 7.87/2.78  #BackRed      : 34
% 7.87/2.78  
% 7.87/2.78  #Partial instantiations: 0
% 7.87/2.78  #Strategies tried      : 1
% 7.87/2.78  
% 7.87/2.78  Timing (in seconds)
% 7.87/2.78  ----------------------
% 7.87/2.78  Preprocessing        : 0.39
% 7.87/2.78  Parsing              : 0.21
% 7.87/2.78  CNF conversion       : 0.03
% 7.87/2.78  Main loop            : 1.58
% 7.87/2.78  Inferencing          : 0.49
% 7.87/2.78  Reduction            : 0.65
% 7.87/2.78  Demodulation         : 0.49
% 7.87/2.78  BG Simplification    : 0.05
% 7.87/2.78  Subsumption          : 0.29
% 7.87/2.78  Abstraction          : 0.07
% 7.87/2.78  MUC search           : 0.00
% 7.87/2.78  Cooper               : 0.00
% 7.87/2.78  Total                : 2.03
% 7.87/2.78  Index Insertion      : 0.00
% 7.87/2.78  Index Deletion       : 0.00
% 7.87/2.78  Index Matching       : 0.00
% 7.87/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
