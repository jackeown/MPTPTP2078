%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:57 EST 2020

% Result     : Theorem 7.44s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :  216 (1406 expanded)
%              Number of leaves         :   45 ( 473 expanded)
%              Depth                    :   16
%              Number of atoms          :  422 (4064 expanded)
%              Number of equality atoms :  141 ( 736 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_230,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_126,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_114,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_164,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C
              & v2_funct_1(E) )
           => ( C = k1_xboole_0
              | k2_relset_1(A,B,D) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_208,axiom,(
    ! [A,B,C] :
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

tff(f_124,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_47,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_3304,plain,(
    ! [C_225,A_226,B_227] :
      ( v1_xboole_0(C_225)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227)))
      | ~ v1_xboole_0(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3317,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_3304])).

tff(c_3353,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3317])).

tff(c_74,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_222,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_xboole_0(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_239,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_222])).

tff(c_241,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_301,plain,(
    ! [A_76,B_77,D_78] :
      ( r2_relset_1(A_76,B_77,D_78,D_78)
      | ~ m1_subset_1(D_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_313,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_301])).

tff(c_50,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_10,plain,(
    ! [A_4] : k1_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_82,plain,(
    ! [A_4] : k1_relat_1(k6_partfun1(A_4)) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_10])).

tff(c_46,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_159,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_206,plain,(
    ! [A_69] : v1_relat_1(k6_partfun1(A_69)) ),
    inference(resolution,[status(thm)],[c_46,c_159])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_relat_1(A_3) != k1_xboole_0
      | k1_xboole_0 = A_3
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_209,plain,(
    ! [A_69] :
      ( k1_relat_1(k6_partfun1(A_69)) != k1_xboole_0
      | k6_partfun1(A_69) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_206,c_8])).

tff(c_268,plain,(
    ! [A_75] :
      ( k1_xboole_0 != A_75
      | k6_partfun1(A_75) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_209])).

tff(c_64,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_279,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_64])).

tff(c_314,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_80,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_78,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_12,plain,(
    ! [A_4] : k2_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_81,plain,(
    ! [A_4] : k2_relat_1(k6_partfun1(A_4)) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_12])).

tff(c_319,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_relset_1(A_80,B_81,C_82) = k2_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_325,plain,(
    ! [A_30] : k2_relset_1(A_30,A_30,k6_partfun1(A_30)) = k2_relat_1(k6_partfun1(A_30)) ),
    inference(resolution,[status(thm)],[c_46,c_319])).

tff(c_335,plain,(
    ! [A_30] : k2_relset_1(A_30,A_30,k6_partfun1(A_30)) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_325])).

tff(c_68,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_455,plain,(
    ! [C_90,A_91,B_92] :
      ( v2_funct_1(C_90)
      | ~ v3_funct_2(C_90,A_91,B_92)
      | ~ v1_funct_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_467,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_455])).

tff(c_475,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_467])).

tff(c_336,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_319])).

tff(c_1589,plain,(
    ! [B_148,F_146,A_143,C_144,D_147,E_145] :
      ( m1_subset_1(k1_partfun1(A_143,B_148,C_144,D_147,E_145,F_146),k1_zfmisc_1(k2_zfmisc_1(A_143,D_147)))
      | ~ m1_subset_1(F_146,k1_zfmisc_1(k2_zfmisc_1(C_144,D_147)))
      | ~ v1_funct_1(F_146)
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_148)))
      | ~ v1_funct_1(E_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_553,plain,(
    ! [D_101,C_102,A_103,B_104] :
      ( D_101 = C_102
      | ~ r2_relset_1(A_103,B_104,C_102,D_101)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_563,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_64,c_553])).

tff(c_580,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_563])).

tff(c_608,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_580])).

tff(c_1607,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1589,c_608])).

tff(c_1637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_74,c_72,c_66,c_1607])).

tff(c_1638,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_580])).

tff(c_2950,plain,(
    ! [B_212,E_211,C_213,A_210,D_214] :
      ( k2_relset_1(A_210,B_212,D_214) = B_212
      | k1_xboole_0 = C_213
      | ~ v2_funct_1(E_211)
      | k2_relset_1(A_210,C_213,k1_partfun1(A_210,B_212,B_212,C_213,D_214,E_211)) != C_213
      | ~ m1_subset_1(E_211,k1_zfmisc_1(k2_zfmisc_1(B_212,C_213)))
      | ~ v1_funct_2(E_211,B_212,C_213)
      | ~ v1_funct_1(E_211)
      | ~ m1_subset_1(D_214,k1_zfmisc_1(k2_zfmisc_1(A_210,B_212)))
      | ~ v1_funct_2(D_214,A_210,B_212)
      | ~ v1_funct_1(D_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_2952,plain,
    ( k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1')) != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1638,c_2950])).

tff(c_2954,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_70,c_66,c_335,c_475,c_336,c_2952])).

tff(c_2955,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_2954])).

tff(c_2956,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2955,c_336])).

tff(c_311,plain,(
    ! [A_30] : r2_relset_1(A_30,A_30,k6_partfun1(A_30),k6_partfun1(A_30)) ),
    inference(resolution,[status(thm)],[c_46,c_301])).

tff(c_76,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_464,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_455])).

tff(c_472,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_464])).

tff(c_3045,plain,(
    ! [C_215,D_216,B_217,A_218] :
      ( k2_funct_1(C_215) = D_216
      | k1_xboole_0 = B_217
      | k1_xboole_0 = A_218
      | ~ v2_funct_1(C_215)
      | ~ r2_relset_1(A_218,A_218,k1_partfun1(A_218,B_217,B_217,A_218,C_215,D_216),k6_partfun1(A_218))
      | k2_relset_1(A_218,B_217,C_215) != B_217
      | ~ m1_subset_1(D_216,k1_zfmisc_1(k2_zfmisc_1(B_217,A_218)))
      | ~ v1_funct_2(D_216,B_217,A_218)
      | ~ v1_funct_1(D_216)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_218,B_217)))
      | ~ v1_funct_2(C_215,A_218,B_217)
      | ~ v1_funct_1(C_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_3054,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1638,c_3045])).

tff(c_3062,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_70,c_66,c_2956,c_311,c_472,c_3054])).

tff(c_3063,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_3062])).

tff(c_1810,plain,(
    ! [A_157,B_158] :
      ( k2_funct_2(A_157,B_158) = k2_funct_1(B_158)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(k2_zfmisc_1(A_157,A_157)))
      | ~ v3_funct_2(B_158,A_157,A_157)
      | ~ v1_funct_2(B_158,A_157,A_157)
      | ~ v1_funct_1(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1822,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_1810])).

tff(c_1831,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_1822])).

tff(c_62,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_1836,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1831,c_62])).

tff(c_3084,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3063,c_1836])).

tff(c_3108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_3084])).

tff(c_3110,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_3125,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3110,c_2])).

tff(c_3127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_3125])).

tff(c_3129,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_143,plain,(
    ! [B_60,A_61] :
      ( ~ v1_xboole_0(B_60)
      | B_60 = A_61
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_146,plain,(
    ! [A_61] :
      ( k1_xboole_0 = A_61
      | ~ v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_2,c_143])).

tff(c_3154,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3129,c_146])).

tff(c_240,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_222])).

tff(c_3137,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_240])).

tff(c_3146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3129,c_3137])).

tff(c_3147,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_3161,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3147,c_146])).

tff(c_3201,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3154,c_3161])).

tff(c_3128,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_3135,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_3128,c_146])).

tff(c_3196,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3161,c_3135])).

tff(c_3225,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3201,c_3196])).

tff(c_87,plain,(
    ! [A_56] : k6_relat_1(A_56) = k6_partfun1(A_56) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_93,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_14])).

tff(c_114,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_81])).

tff(c_3186,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3135,c_3135,c_114])).

tff(c_3247,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3225,c_3225,c_3186])).

tff(c_174,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_159])).

tff(c_6,plain,(
    ! [A_3] :
      ( k2_relat_1(A_3) != k1_xboole_0
      | k1_xboole_0 = A_3
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_183,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_174,c_6])).

tff(c_220,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_3178,plain,(
    k2_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3135,c_220])).

tff(c_3282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3247,c_3225,c_3225,c_3178])).

tff(c_3283,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_212,plain,(
    ! [A_69] :
      ( k2_relat_1(k6_partfun1(A_69)) != k1_xboole_0
      | k6_partfun1(A_69) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_206,c_6])).

tff(c_218,plain,(
    ! [A_69] :
      ( k1_xboole_0 != A_69
      | k6_partfun1(A_69) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_212])).

tff(c_3424,plain,(
    ! [A_236] :
      ( A_236 != '#skF_2'
      | k6_partfun1(A_236) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3283,c_3283,c_218])).

tff(c_3435,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),'#skF_2')
    | '#skF_2' != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_3424,c_64])).

tff(c_3488,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3435])).

tff(c_3394,plain,(
    ! [A_233,B_234,C_235] :
      ( k2_relset_1(A_233,B_234,C_235) = k2_relat_1(C_235)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3397,plain,(
    ! [A_30] : k2_relset_1(A_30,A_30,k6_partfun1(A_30)) = k2_relat_1(k6_partfun1(A_30)) ),
    inference(resolution,[status(thm)],[c_46,c_3394])).

tff(c_3405,plain,(
    ! [A_30] : k2_relset_1(A_30,A_30,k6_partfun1(A_30)) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_3397])).

tff(c_3468,plain,(
    ! [C_238,A_239,B_240] :
      ( v2_funct_1(C_238)
      | ~ v3_funct_2(C_238,A_239,B_240)
      | ~ v1_funct_1(C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3477,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_3468])).

tff(c_3484,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_3477])).

tff(c_3284,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_3318,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3283,c_3284])).

tff(c_3400,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_3394])).

tff(c_3407,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3318,c_3400])).

tff(c_4659,plain,(
    ! [C_299,F_301,A_298,E_300,D_302,B_303] :
      ( m1_subset_1(k1_partfun1(A_298,B_303,C_299,D_302,E_300,F_301),k1_zfmisc_1(k2_zfmisc_1(A_298,D_302)))
      | ~ m1_subset_1(F_301,k1_zfmisc_1(k2_zfmisc_1(C_299,D_302)))
      | ~ v1_funct_1(F_301)
      | ~ m1_subset_1(E_300,k1_zfmisc_1(k2_zfmisc_1(A_298,B_303)))
      | ~ v1_funct_1(E_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3554,plain,(
    ! [D_246,C_247,A_248,B_249] :
      ( D_246 = C_247
      | ~ r2_relset_1(A_248,B_249,C_247,D_246)
      | ~ m1_subset_1(D_246,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249)))
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3562,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_64,c_3554])).

tff(c_3577,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3562])).

tff(c_3723,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3577])).

tff(c_4670,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4659,c_3723])).

tff(c_4705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_74,c_72,c_66,c_4670])).

tff(c_4706,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3577])).

tff(c_54,plain,(
    ! [E_44,D_42,A_39,C_41,B_40] :
      ( k2_relset_1(A_39,B_40,D_42) = B_40
      | k1_xboole_0 = C_41
      | ~ v2_funct_1(E_44)
      | k2_relset_1(A_39,C_41,k1_partfun1(A_39,B_40,B_40,C_41,D_42,E_44)) != C_41
      | ~ m1_subset_1(E_44,k1_zfmisc_1(k2_zfmisc_1(B_40,C_41)))
      | ~ v1_funct_2(E_44,B_40,C_41)
      | ~ v1_funct_1(E_44)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_2(D_42,A_39,B_40)
      | ~ v1_funct_1(D_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_5979,plain,(
    ! [E_364,A_363,C_366,D_367,B_365] :
      ( k2_relset_1(A_363,B_365,D_367) = B_365
      | C_366 = '#skF_2'
      | ~ v2_funct_1(E_364)
      | k2_relset_1(A_363,C_366,k1_partfun1(A_363,B_365,B_365,C_366,D_367,E_364)) != C_366
      | ~ m1_subset_1(E_364,k1_zfmisc_1(k2_zfmisc_1(B_365,C_366)))
      | ~ v1_funct_2(E_364,B_365,C_366)
      | ~ v1_funct_1(E_364)
      | ~ m1_subset_1(D_367,k1_zfmisc_1(k2_zfmisc_1(A_363,B_365)))
      | ~ v1_funct_2(D_367,A_363,B_365)
      | ~ v1_funct_1(D_367) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3283,c_54])).

tff(c_5981,plain,
    ( k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1')) != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4706,c_5979])).

tff(c_5983,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_70,c_66,c_3405,c_3484,c_3407,c_5981])).

tff(c_5985,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3488,c_5983])).

tff(c_5987,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3435])).

tff(c_3295,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3283,c_2])).

tff(c_6000,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5987,c_3295])).

tff(c_6010,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3353,c_6000])).

tff(c_6011,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3317])).

tff(c_6012,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3317])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6242,plain,(
    ! [A_384] :
      ( A_384 = '#skF_1'
      | ~ v1_xboole_0(A_384) ) ),
    inference(resolution,[status(thm)],[c_6012,c_4])).

tff(c_6251,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6011,c_6242])).

tff(c_6040,plain,(
    ! [A_371] :
      ( A_371 = '#skF_1'
      | ~ v1_xboole_0(A_371) ) ),
    inference(resolution,[status(thm)],[c_6012,c_4])).

tff(c_6053,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3295,c_6040])).

tff(c_6073,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6053,c_6053,c_3318])).

tff(c_6052,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6011,c_6040])).

tff(c_175,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_159])).

tff(c_191,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_175,c_6])).

tff(c_6019,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3283,c_3283,c_191])).

tff(c_6020,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_6019])).

tff(c_6054,plain,(
    k2_relat_1('#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6052,c_6020])).

tff(c_6144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6073,c_6053,c_6054])).

tff(c_6145,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6019])).

tff(c_6151,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6145,c_3283])).

tff(c_6259,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6251,c_6151])).

tff(c_216,plain,(
    ! [A_69] :
      ( k1_xboole_0 != A_69
      | k6_partfun1(A_69) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_209])).

tff(c_6389,plain,(
    ! [A_392] :
      ( A_392 != '#skF_1'
      | k6_partfun1(A_392) = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6259,c_6259,c_216])).

tff(c_6632,plain,(
    ! [A_414] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_414,A_414)))
      | A_414 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6389,c_46])).

tff(c_22,plain,(
    ! [A_15,B_16,D_18] :
      ( r2_relset_1(A_15,B_16,D_18,D_18)
      | ~ m1_subset_1(D_18,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6700,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_6632,c_22])).

tff(c_6266,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6251,c_72])).

tff(c_6264,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6251,c_70])).

tff(c_6265,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6251,c_68])).

tff(c_6630,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6389,c_46])).

tff(c_6263,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6251,c_66])).

tff(c_6572,plain,(
    ! [A_406,B_407] :
      ( k2_funct_2(A_406,B_407) = k2_funct_1(B_407)
      | ~ m1_subset_1(B_407,k1_zfmisc_1(k2_zfmisc_1(A_406,A_406)))
      | ~ v3_funct_2(B_407,A_406,A_406)
      | ~ v1_funct_2(B_407,A_406,A_406)
      | ~ v1_funct_1(B_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_6575,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6263,c_6572])).

tff(c_6581,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6266,c_6264,c_6265,c_6575])).

tff(c_7291,plain,(
    ! [A_438,B_439] :
      ( m1_subset_1(k2_funct_2(A_438,B_439),k1_zfmisc_1(k2_zfmisc_1(A_438,A_438)))
      | ~ m1_subset_1(B_439,k1_zfmisc_1(k2_zfmisc_1(A_438,A_438)))
      | ~ v3_funct_2(B_439,A_438,A_438)
      | ~ v1_funct_2(B_439,A_438,A_438)
      | ~ v1_funct_1(B_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_7321,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6581,c_7291])).

tff(c_7333,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6266,c_6264,c_6265,c_6630,c_7321])).

tff(c_18,plain,(
    ! [C_11,A_8,B_9] :
      ( v1_xboole_0(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_7357,plain,
    ( v1_xboole_0(k2_funct_1('#skF_1'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_7333,c_18])).

tff(c_7383,plain,(
    v1_xboole_0(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6012,c_7357])).

tff(c_6018,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_6012,c_4])).

tff(c_7403,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_7383,c_6018])).

tff(c_6154,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6145,c_62])).

tff(c_6258,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6251,c_6251,c_6154])).

tff(c_6583,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6581,c_6258])).

tff(c_7416,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7403,c_6583])).

tff(c_7424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6700,c_7416])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:33:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.44/2.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.44/2.48  
% 7.44/2.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.44/2.48  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.44/2.48  
% 7.44/2.48  %Foreground sorts:
% 7.44/2.48  
% 7.44/2.48  
% 7.44/2.48  %Background operators:
% 7.44/2.48  
% 7.44/2.48  
% 7.44/2.48  %Foreground operators:
% 7.44/2.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.44/2.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.44/2.48  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.44/2.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.44/2.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.44/2.48  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.44/2.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.44/2.48  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 7.44/2.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.44/2.48  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.44/2.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.44/2.48  tff('#skF_2', type, '#skF_2': $i).
% 7.44/2.48  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.44/2.48  tff('#skF_3', type, '#skF_3': $i).
% 7.44/2.48  tff('#skF_1', type, '#skF_1': $i).
% 7.44/2.48  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.44/2.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.44/2.48  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.44/2.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.44/2.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.44/2.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.44/2.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.44/2.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.44/2.48  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 7.44/2.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.44/2.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.44/2.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.44/2.48  
% 7.80/2.51  tff(f_230, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 7.80/2.51  tff(f_58, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 7.80/2.51  tff(f_70, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.80/2.51  tff(f_126, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.80/2.51  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.80/2.51  tff(f_114, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.80/2.51  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.80/2.51  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 7.80/2.51  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.80/2.51  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 7.80/2.51  tff(f_94, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.80/2.51  tff(f_164, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 7.80/2.51  tff(f_208, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 7.80/2.51  tff(f_124, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 7.80/2.51  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.80/2.51  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 7.80/2.51  tff(f_47, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 7.80/2.51  tff(f_110, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 7.80/2.51  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_230])).
% 7.80/2.51  tff(c_3304, plain, (![C_225, A_226, B_227]: (v1_xboole_0(C_225) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))) | ~v1_xboole_0(A_226))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.80/2.51  tff(c_3317, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_3304])).
% 7.80/2.51  tff(c_3353, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_3317])).
% 7.80/2.51  tff(c_74, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_230])).
% 7.80/2.51  tff(c_222, plain, (![C_70, A_71, B_72]: (v1_xboole_0(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | ~v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.80/2.51  tff(c_239, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_74, c_222])).
% 7.80/2.51  tff(c_241, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_239])).
% 7.80/2.51  tff(c_301, plain, (![A_76, B_77, D_78]: (r2_relset_1(A_76, B_77, D_78, D_78) | ~m1_subset_1(D_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.80/2.51  tff(c_313, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_301])).
% 7.80/2.51  tff(c_50, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.80/2.51  tff(c_10, plain, (![A_4]: (k1_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.80/2.51  tff(c_82, plain, (![A_4]: (k1_relat_1(k6_partfun1(A_4))=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_10])).
% 7.80/2.51  tff(c_46, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.80/2.51  tff(c_159, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.80/2.51  tff(c_206, plain, (![A_69]: (v1_relat_1(k6_partfun1(A_69)))), inference(resolution, [status(thm)], [c_46, c_159])).
% 7.80/2.51  tff(c_8, plain, (![A_3]: (k1_relat_1(A_3)!=k1_xboole_0 | k1_xboole_0=A_3 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.80/2.51  tff(c_209, plain, (![A_69]: (k1_relat_1(k6_partfun1(A_69))!=k1_xboole_0 | k6_partfun1(A_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_206, c_8])).
% 7.80/2.51  tff(c_268, plain, (![A_75]: (k1_xboole_0!=A_75 | k6_partfun1(A_75)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_209])).
% 7.80/2.51  tff(c_64, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 7.80/2.51  tff(c_279, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_268, c_64])).
% 7.80/2.51  tff(c_314, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_279])).
% 7.80/2.51  tff(c_80, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 7.80/2.51  tff(c_78, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_230])).
% 7.80/2.51  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_230])).
% 7.80/2.51  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_230])).
% 7.80/2.51  tff(c_12, plain, (![A_4]: (k2_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.80/2.51  tff(c_81, plain, (![A_4]: (k2_relat_1(k6_partfun1(A_4))=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_12])).
% 7.80/2.51  tff(c_319, plain, (![A_80, B_81, C_82]: (k2_relset_1(A_80, B_81, C_82)=k2_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.80/2.51  tff(c_325, plain, (![A_30]: (k2_relset_1(A_30, A_30, k6_partfun1(A_30))=k2_relat_1(k6_partfun1(A_30)))), inference(resolution, [status(thm)], [c_46, c_319])).
% 7.80/2.51  tff(c_335, plain, (![A_30]: (k2_relset_1(A_30, A_30, k6_partfun1(A_30))=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_81, c_325])).
% 7.80/2.51  tff(c_68, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_230])).
% 7.80/2.51  tff(c_455, plain, (![C_90, A_91, B_92]: (v2_funct_1(C_90) | ~v3_funct_2(C_90, A_91, B_92) | ~v1_funct_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.80/2.51  tff(c_467, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_455])).
% 7.80/2.51  tff(c_475, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_467])).
% 7.80/2.51  tff(c_336, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_319])).
% 7.80/2.51  tff(c_1589, plain, (![B_148, F_146, A_143, C_144, D_147, E_145]: (m1_subset_1(k1_partfun1(A_143, B_148, C_144, D_147, E_145, F_146), k1_zfmisc_1(k2_zfmisc_1(A_143, D_147))) | ~m1_subset_1(F_146, k1_zfmisc_1(k2_zfmisc_1(C_144, D_147))) | ~v1_funct_1(F_146) | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_148))) | ~v1_funct_1(E_145))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.80/2.51  tff(c_553, plain, (![D_101, C_102, A_103, B_104]: (D_101=C_102 | ~r2_relset_1(A_103, B_104, C_102, D_101) | ~m1_subset_1(D_101, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.80/2.51  tff(c_563, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_64, c_553])).
% 7.80/2.51  tff(c_580, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_563])).
% 7.80/2.51  tff(c_608, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_580])).
% 7.80/2.51  tff(c_1607, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_1589, c_608])).
% 7.80/2.51  tff(c_1637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_74, c_72, c_66, c_1607])).
% 7.80/2.51  tff(c_1638, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_580])).
% 7.80/2.51  tff(c_2950, plain, (![B_212, E_211, C_213, A_210, D_214]: (k2_relset_1(A_210, B_212, D_214)=B_212 | k1_xboole_0=C_213 | ~v2_funct_1(E_211) | k2_relset_1(A_210, C_213, k1_partfun1(A_210, B_212, B_212, C_213, D_214, E_211))!=C_213 | ~m1_subset_1(E_211, k1_zfmisc_1(k2_zfmisc_1(B_212, C_213))) | ~v1_funct_2(E_211, B_212, C_213) | ~v1_funct_1(E_211) | ~m1_subset_1(D_214, k1_zfmisc_1(k2_zfmisc_1(A_210, B_212))) | ~v1_funct_2(D_214, A_210, B_212) | ~v1_funct_1(D_214))), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.80/2.51  tff(c_2952, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'))!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1638, c_2950])).
% 7.80/2.51  tff(c_2954, plain, (k2_relat_1('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_70, c_66, c_335, c_475, c_336, c_2952])).
% 7.80/2.51  tff(c_2955, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_314, c_2954])).
% 7.80/2.51  tff(c_2956, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2955, c_336])).
% 7.80/2.51  tff(c_311, plain, (![A_30]: (r2_relset_1(A_30, A_30, k6_partfun1(A_30), k6_partfun1(A_30)))), inference(resolution, [status(thm)], [c_46, c_301])).
% 7.80/2.51  tff(c_76, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_230])).
% 7.80/2.51  tff(c_464, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_455])).
% 7.80/2.51  tff(c_472, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_464])).
% 7.80/2.51  tff(c_3045, plain, (![C_215, D_216, B_217, A_218]: (k2_funct_1(C_215)=D_216 | k1_xboole_0=B_217 | k1_xboole_0=A_218 | ~v2_funct_1(C_215) | ~r2_relset_1(A_218, A_218, k1_partfun1(A_218, B_217, B_217, A_218, C_215, D_216), k6_partfun1(A_218)) | k2_relset_1(A_218, B_217, C_215)!=B_217 | ~m1_subset_1(D_216, k1_zfmisc_1(k2_zfmisc_1(B_217, A_218))) | ~v1_funct_2(D_216, B_217, A_218) | ~v1_funct_1(D_216) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_218, B_217))) | ~v1_funct_2(C_215, A_218, B_217) | ~v1_funct_1(C_215))), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.80/2.51  tff(c_3054, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1638, c_3045])).
% 7.80/2.51  tff(c_3062, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_70, c_66, c_2956, c_311, c_472, c_3054])).
% 7.80/2.51  tff(c_3063, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_314, c_3062])).
% 7.80/2.51  tff(c_1810, plain, (![A_157, B_158]: (k2_funct_2(A_157, B_158)=k2_funct_1(B_158) | ~m1_subset_1(B_158, k1_zfmisc_1(k2_zfmisc_1(A_157, A_157))) | ~v3_funct_2(B_158, A_157, A_157) | ~v1_funct_2(B_158, A_157, A_157) | ~v1_funct_1(B_158))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.80/2.51  tff(c_1822, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_1810])).
% 7.80/2.51  tff(c_1831, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_1822])).
% 7.80/2.51  tff(c_62, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 7.80/2.51  tff(c_1836, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1831, c_62])).
% 7.80/2.51  tff(c_3084, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3063, c_1836])).
% 7.80/2.51  tff(c_3108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_313, c_3084])).
% 7.80/2.51  tff(c_3110, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_279])).
% 7.80/2.51  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.80/2.51  tff(c_3125, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3110, c_2])).
% 7.80/2.51  tff(c_3127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_241, c_3125])).
% 7.80/2.51  tff(c_3129, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_239])).
% 7.80/2.51  tff(c_143, plain, (![B_60, A_61]: (~v1_xboole_0(B_60) | B_60=A_61 | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.80/2.51  tff(c_146, plain, (![A_61]: (k1_xboole_0=A_61 | ~v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_2, c_143])).
% 7.80/2.51  tff(c_3154, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_3129, c_146])).
% 7.80/2.51  tff(c_240, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_222])).
% 7.80/2.51  tff(c_3137, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_240])).
% 7.80/2.51  tff(c_3146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3129, c_3137])).
% 7.80/2.51  tff(c_3147, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_240])).
% 7.80/2.51  tff(c_3161, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3147, c_146])).
% 7.80/2.51  tff(c_3201, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3154, c_3161])).
% 7.80/2.51  tff(c_3128, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_239])).
% 7.80/2.51  tff(c_3135, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_3128, c_146])).
% 7.80/2.51  tff(c_3196, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3161, c_3135])).
% 7.80/2.51  tff(c_3225, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3201, c_3196])).
% 7.80/2.51  tff(c_87, plain, (![A_56]: (k6_relat_1(A_56)=k6_partfun1(A_56))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.80/2.51  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.80/2.51  tff(c_93, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_87, c_14])).
% 7.80/2.51  tff(c_114, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_93, c_81])).
% 7.80/2.51  tff(c_3186, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3135, c_3135, c_114])).
% 7.80/2.51  tff(c_3247, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3225, c_3225, c_3186])).
% 7.80/2.51  tff(c_174, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_159])).
% 7.80/2.51  tff(c_6, plain, (![A_3]: (k2_relat_1(A_3)!=k1_xboole_0 | k1_xboole_0=A_3 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.80/2.51  tff(c_183, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_174, c_6])).
% 7.80/2.51  tff(c_220, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_183])).
% 7.80/2.51  tff(c_3178, plain, (k2_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3135, c_220])).
% 7.80/2.51  tff(c_3282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3247, c_3225, c_3225, c_3178])).
% 7.80/2.51  tff(c_3283, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_183])).
% 7.80/2.51  tff(c_212, plain, (![A_69]: (k2_relat_1(k6_partfun1(A_69))!=k1_xboole_0 | k6_partfun1(A_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_206, c_6])).
% 7.80/2.51  tff(c_218, plain, (![A_69]: (k1_xboole_0!=A_69 | k6_partfun1(A_69)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_81, c_212])).
% 7.80/2.51  tff(c_3424, plain, (![A_236]: (A_236!='#skF_2' | k6_partfun1(A_236)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3283, c_3283, c_218])).
% 7.80/2.51  tff(c_3435, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), '#skF_2') | '#skF_2'!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_3424, c_64])).
% 7.80/2.51  tff(c_3488, plain, ('#skF_2'!='#skF_1'), inference(splitLeft, [status(thm)], [c_3435])).
% 7.80/2.51  tff(c_3394, plain, (![A_233, B_234, C_235]: (k2_relset_1(A_233, B_234, C_235)=k2_relat_1(C_235) | ~m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.80/2.51  tff(c_3397, plain, (![A_30]: (k2_relset_1(A_30, A_30, k6_partfun1(A_30))=k2_relat_1(k6_partfun1(A_30)))), inference(resolution, [status(thm)], [c_46, c_3394])).
% 7.80/2.51  tff(c_3405, plain, (![A_30]: (k2_relset_1(A_30, A_30, k6_partfun1(A_30))=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_81, c_3397])).
% 7.80/2.51  tff(c_3468, plain, (![C_238, A_239, B_240]: (v2_funct_1(C_238) | ~v3_funct_2(C_238, A_239, B_240) | ~v1_funct_1(C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.80/2.51  tff(c_3477, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_3468])).
% 7.80/2.51  tff(c_3484, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_3477])).
% 7.80/2.51  tff(c_3284, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_183])).
% 7.80/2.51  tff(c_3318, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3283, c_3284])).
% 7.80/2.51  tff(c_3400, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_3394])).
% 7.80/2.51  tff(c_3407, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3318, c_3400])).
% 7.80/2.51  tff(c_4659, plain, (![C_299, F_301, A_298, E_300, D_302, B_303]: (m1_subset_1(k1_partfun1(A_298, B_303, C_299, D_302, E_300, F_301), k1_zfmisc_1(k2_zfmisc_1(A_298, D_302))) | ~m1_subset_1(F_301, k1_zfmisc_1(k2_zfmisc_1(C_299, D_302))) | ~v1_funct_1(F_301) | ~m1_subset_1(E_300, k1_zfmisc_1(k2_zfmisc_1(A_298, B_303))) | ~v1_funct_1(E_300))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.80/2.51  tff(c_3554, plain, (![D_246, C_247, A_248, B_249]: (D_246=C_247 | ~r2_relset_1(A_248, B_249, C_247, D_246) | ~m1_subset_1(D_246, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.80/2.51  tff(c_3562, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_64, c_3554])).
% 7.80/2.51  tff(c_3577, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3562])).
% 7.80/2.51  tff(c_3723, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_3577])).
% 7.80/2.51  tff(c_4670, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_4659, c_3723])).
% 7.80/2.51  tff(c_4705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_74, c_72, c_66, c_4670])).
% 7.80/2.51  tff(c_4706, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_3577])).
% 7.80/2.51  tff(c_54, plain, (![E_44, D_42, A_39, C_41, B_40]: (k2_relset_1(A_39, B_40, D_42)=B_40 | k1_xboole_0=C_41 | ~v2_funct_1(E_44) | k2_relset_1(A_39, C_41, k1_partfun1(A_39, B_40, B_40, C_41, D_42, E_44))!=C_41 | ~m1_subset_1(E_44, k1_zfmisc_1(k2_zfmisc_1(B_40, C_41))) | ~v1_funct_2(E_44, B_40, C_41) | ~v1_funct_1(E_44) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_2(D_42, A_39, B_40) | ~v1_funct_1(D_42))), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.80/2.51  tff(c_5979, plain, (![E_364, A_363, C_366, D_367, B_365]: (k2_relset_1(A_363, B_365, D_367)=B_365 | C_366='#skF_2' | ~v2_funct_1(E_364) | k2_relset_1(A_363, C_366, k1_partfun1(A_363, B_365, B_365, C_366, D_367, E_364))!=C_366 | ~m1_subset_1(E_364, k1_zfmisc_1(k2_zfmisc_1(B_365, C_366))) | ~v1_funct_2(E_364, B_365, C_366) | ~v1_funct_1(E_364) | ~m1_subset_1(D_367, k1_zfmisc_1(k2_zfmisc_1(A_363, B_365))) | ~v1_funct_2(D_367, A_363, B_365) | ~v1_funct_1(D_367))), inference(demodulation, [status(thm), theory('equality')], [c_3283, c_54])).
% 7.80/2.51  tff(c_5981, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'))!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4706, c_5979])).
% 7.80/2.51  tff(c_5983, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_70, c_66, c_3405, c_3484, c_3407, c_5981])).
% 7.80/2.51  tff(c_5985, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3488, c_5983])).
% 7.80/2.51  tff(c_5987, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_3435])).
% 7.80/2.51  tff(c_3295, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3283, c_2])).
% 7.80/2.51  tff(c_6000, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5987, c_3295])).
% 7.80/2.51  tff(c_6010, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3353, c_6000])).
% 7.80/2.51  tff(c_6011, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_3317])).
% 7.80/2.51  tff(c_6012, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_3317])).
% 7.80/2.51  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.80/2.51  tff(c_6242, plain, (![A_384]: (A_384='#skF_1' | ~v1_xboole_0(A_384))), inference(resolution, [status(thm)], [c_6012, c_4])).
% 7.80/2.51  tff(c_6251, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_6011, c_6242])).
% 7.80/2.51  tff(c_6040, plain, (![A_371]: (A_371='#skF_1' | ~v1_xboole_0(A_371))), inference(resolution, [status(thm)], [c_6012, c_4])).
% 7.80/2.51  tff(c_6053, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_3295, c_6040])).
% 7.80/2.51  tff(c_6073, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6053, c_6053, c_3318])).
% 7.80/2.51  tff(c_6052, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_6011, c_6040])).
% 7.80/2.51  tff(c_175, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_159])).
% 7.80/2.51  tff(c_191, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_175, c_6])).
% 7.80/2.51  tff(c_6019, plain, (k2_relat_1('#skF_3')!='#skF_2' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3283, c_3283, c_191])).
% 7.80/2.51  tff(c_6020, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_6019])).
% 7.80/2.51  tff(c_6054, plain, (k2_relat_1('#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6052, c_6020])).
% 7.80/2.51  tff(c_6144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6073, c_6053, c_6054])).
% 7.80/2.51  tff(c_6145, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_6019])).
% 7.80/2.51  tff(c_6151, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6145, c_3283])).
% 7.80/2.51  tff(c_6259, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6251, c_6151])).
% 7.80/2.51  tff(c_216, plain, (![A_69]: (k1_xboole_0!=A_69 | k6_partfun1(A_69)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_209])).
% 7.80/2.51  tff(c_6389, plain, (![A_392]: (A_392!='#skF_1' | k6_partfun1(A_392)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6259, c_6259, c_216])).
% 7.80/2.51  tff(c_6632, plain, (![A_414]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_414, A_414))) | A_414!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6389, c_46])).
% 7.80/2.51  tff(c_22, plain, (![A_15, B_16, D_18]: (r2_relset_1(A_15, B_16, D_18, D_18) | ~m1_subset_1(D_18, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.80/2.51  tff(c_6700, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_6632, c_22])).
% 7.80/2.51  tff(c_6266, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6251, c_72])).
% 7.80/2.51  tff(c_6264, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6251, c_70])).
% 7.80/2.51  tff(c_6265, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6251, c_68])).
% 7.80/2.51  tff(c_6630, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_6389, c_46])).
% 7.80/2.51  tff(c_6263, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_6251, c_66])).
% 7.80/2.51  tff(c_6572, plain, (![A_406, B_407]: (k2_funct_2(A_406, B_407)=k2_funct_1(B_407) | ~m1_subset_1(B_407, k1_zfmisc_1(k2_zfmisc_1(A_406, A_406))) | ~v3_funct_2(B_407, A_406, A_406) | ~v1_funct_2(B_407, A_406, A_406) | ~v1_funct_1(B_407))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.80/2.51  tff(c_6575, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_6263, c_6572])).
% 7.80/2.51  tff(c_6581, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6266, c_6264, c_6265, c_6575])).
% 7.80/2.51  tff(c_7291, plain, (![A_438, B_439]: (m1_subset_1(k2_funct_2(A_438, B_439), k1_zfmisc_1(k2_zfmisc_1(A_438, A_438))) | ~m1_subset_1(B_439, k1_zfmisc_1(k2_zfmisc_1(A_438, A_438))) | ~v3_funct_2(B_439, A_438, A_438) | ~v1_funct_2(B_439, A_438, A_438) | ~v1_funct_1(B_439))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.80/2.51  tff(c_7321, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6581, c_7291])).
% 7.80/2.51  tff(c_7333, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_6266, c_6264, c_6265, c_6630, c_7321])).
% 7.80/2.51  tff(c_18, plain, (![C_11, A_8, B_9]: (v1_xboole_0(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.80/2.51  tff(c_7357, plain, (v1_xboole_0(k2_funct_1('#skF_1')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_7333, c_18])).
% 7.80/2.51  tff(c_7383, plain, (v1_xboole_0(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6012, c_7357])).
% 7.80/2.51  tff(c_6018, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_6012, c_4])).
% 7.80/2.51  tff(c_7403, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_7383, c_6018])).
% 7.80/2.51  tff(c_6154, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6145, c_62])).
% 7.80/2.51  tff(c_6258, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6251, c_6251, c_6154])).
% 7.80/2.51  tff(c_6583, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6581, c_6258])).
% 7.80/2.51  tff(c_7416, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7403, c_6583])).
% 7.80/2.51  tff(c_7424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6700, c_7416])).
% 7.80/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.80/2.51  
% 7.80/2.51  Inference rules
% 7.80/2.51  ----------------------
% 7.80/2.51  #Ref     : 0
% 7.80/2.51  #Sup     : 1832
% 7.80/2.51  #Fact    : 0
% 7.80/2.51  #Define  : 0
% 7.80/2.51  #Split   : 26
% 7.80/2.51  #Chain   : 0
% 7.80/2.51  #Close   : 0
% 7.80/2.51  
% 7.80/2.51  Ordering : KBO
% 7.80/2.51  
% 7.80/2.51  Simplification rules
% 7.80/2.51  ----------------------
% 7.80/2.51  #Subsume      : 345
% 7.80/2.51  #Demod        : 1326
% 7.80/2.51  #Tautology    : 520
% 7.80/2.51  #SimpNegUnit  : 10
% 7.80/2.51  #BackRed      : 190
% 7.80/2.51  
% 7.80/2.51  #Partial instantiations: 0
% 7.80/2.51  #Strategies tried      : 1
% 7.80/2.51  
% 7.80/2.51  Timing (in seconds)
% 7.80/2.51  ----------------------
% 7.80/2.51  Preprocessing        : 0.36
% 7.80/2.51  Parsing              : 0.19
% 7.80/2.51  CNF conversion       : 0.03
% 7.80/2.51  Main loop            : 1.36
% 7.80/2.51  Inferencing          : 0.44
% 7.80/2.51  Reduction            : 0.49
% 7.80/2.51  Demodulation         : 0.35
% 7.80/2.51  BG Simplification    : 0.05
% 7.80/2.51  Subsumption          : 0.29
% 7.80/2.51  Abstraction          : 0.06
% 7.80/2.51  MUC search           : 0.00
% 7.80/2.51  Cooper               : 0.00
% 7.80/2.51  Total                : 1.79
% 7.80/2.51  Index Insertion      : 0.00
% 7.80/2.51  Index Deletion       : 0.00
% 7.80/2.51  Index Matching       : 0.00
% 7.80/2.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
