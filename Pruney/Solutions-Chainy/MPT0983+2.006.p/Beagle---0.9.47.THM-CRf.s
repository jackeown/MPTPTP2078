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
% DateTime   : Thu Dec  3 10:12:01 EST 2020

% Result     : Theorem 4.73s
% Output     : CNFRefutation 5.09s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 287 expanded)
%              Number of leaves         :   47 ( 119 expanded)
%              Depth                    :   10
%              Number of atoms          :  262 ( 853 expanded)
%              Number of equality atoms :   39 (  85 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_183,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_141,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_129,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_109,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_163,axiom,(
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

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_139,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( v1_xboole_0(k2_zfmisc_1(A_3,B_4))
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_143,plain,(
    ! [B_68,A_69] :
      ( v1_relat_1(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_149,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_143])).

tff(c_158,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_149])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_169,plain,(
    ! [A_72] :
      ( v2_funct_1(A_72)
      | ~ v1_funct_1(A_72)
      | ~ v1_relat_1(A_72)
      | ~ v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_68,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_130,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_172,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_169,c_130])).

tff(c_175,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_82,c_172])).

tff(c_176,plain,(
    ! [B_73,A_74] :
      ( v1_xboole_0(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_182,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_176])).

tff(c_189,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_182])).

tff(c_194,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_189])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_62,plain,(
    ! [A_45] : k6_relat_1(A_45) = k6_partfun1(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_40,plain,(
    ! [A_22] : v2_funct_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_84,plain,(
    ! [A_22] : v2_funct_1(k6_partfun1(A_22)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_40])).

tff(c_1520,plain,(
    ! [E_260,F_262,C_261,B_264,A_259,D_263] :
      ( m1_subset_1(k1_partfun1(A_259,B_264,C_261,D_263,E_260,F_262),k1_zfmisc_1(k2_zfmisc_1(A_259,D_263)))
      | ~ m1_subset_1(F_262,k1_zfmisc_1(k2_zfmisc_1(C_261,D_263)))
      | ~ v1_funct_1(F_262)
      | ~ m1_subset_1(E_260,k1_zfmisc_1(k2_zfmisc_1(A_259,B_264)))
      | ~ v1_funct_1(E_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_50,plain,(
    ! [A_30] : m1_subset_1(k6_relat_1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_83,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1207,plain,(
    ! [D_213,C_214,A_215,B_216] :
      ( D_213 = C_214
      | ~ r2_relset_1(A_215,B_216,C_214,D_213)
      | ~ m1_subset_1(D_213,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216)))
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1215,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_1207])).

tff(c_1230,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1215])).

tff(c_1245,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1230])).

tff(c_1528,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1520,c_1245])).

tff(c_1553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_1528])).

tff(c_1554,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1230])).

tff(c_2120,plain,(
    ! [C_323,E_320,D_322,B_321,A_324] :
      ( k1_xboole_0 = C_323
      | v2_funct_1(D_322)
      | ~ v2_funct_1(k1_partfun1(A_324,B_321,B_321,C_323,D_322,E_320))
      | ~ m1_subset_1(E_320,k1_zfmisc_1(k2_zfmisc_1(B_321,C_323)))
      | ~ v1_funct_2(E_320,B_321,C_323)
      | ~ v1_funct_1(E_320)
      | ~ m1_subset_1(D_322,k1_zfmisc_1(k2_zfmisc_1(A_324,B_321)))
      | ~ v1_funct_2(D_322,A_324,B_321)
      | ~ v1_funct_1(D_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2124,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1554,c_2120])).

tff(c_2131,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_72,c_84,c_2124])).

tff(c_2132,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_2131])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2138,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2132,c_2])).

tff(c_2140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_2138])).

tff(c_2141,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_2203,plain,(
    ! [B_338,A_339] :
      ( v1_relat_1(B_338)
      | ~ m1_subset_1(B_338,k1_zfmisc_1(A_339))
      | ~ v1_relat_1(A_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2212,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_2203])).

tff(c_2221,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2212])).

tff(c_2209,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_2203])).

tff(c_2218,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2209])).

tff(c_2245,plain,(
    ! [C_347,B_348,A_349] :
      ( v5_relat_1(C_347,B_348)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(A_349,B_348))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2257,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_2245])).

tff(c_28,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_86,plain,(
    ! [A_19] : k2_relat_1(k6_partfun1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_28])).

tff(c_2570,plain,(
    ! [D_405,B_403,F_406,A_402,E_407,C_404] :
      ( k1_partfun1(A_402,B_403,C_404,D_405,E_407,F_406) = k5_relat_1(E_407,F_406)
      | ~ m1_subset_1(F_406,k1_zfmisc_1(k2_zfmisc_1(C_404,D_405)))
      | ~ v1_funct_1(F_406)
      | ~ m1_subset_1(E_407,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403)))
      | ~ v1_funct_1(E_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2576,plain,(
    ! [A_402,B_403,E_407] :
      ( k1_partfun1(A_402,B_403,'#skF_2','#skF_1',E_407,'#skF_4') = k5_relat_1(E_407,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_407,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403)))
      | ~ v1_funct_1(E_407) ) ),
    inference(resolution,[status(thm)],[c_72,c_2570])).

tff(c_2632,plain,(
    ! [A_414,B_415,E_416] :
      ( k1_partfun1(A_414,B_415,'#skF_2','#skF_1',E_416,'#skF_4') = k5_relat_1(E_416,'#skF_4')
      | ~ m1_subset_1(E_416,k1_zfmisc_1(k2_zfmisc_1(A_414,B_415)))
      | ~ v1_funct_1(E_416) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2576])).

tff(c_2638,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_2632])).

tff(c_2645,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2638])).

tff(c_2400,plain,(
    ! [D_371,C_372,A_373,B_374] :
      ( D_371 = C_372
      | ~ r2_relset_1(A_373,B_374,C_372,D_371)
      | ~ m1_subset_1(D_371,k1_zfmisc_1(k2_zfmisc_1(A_373,B_374)))
      | ~ m1_subset_1(C_372,k1_zfmisc_1(k2_zfmisc_1(A_373,B_374))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2404,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_2400])).

tff(c_2411,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_2404])).

tff(c_2451,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2411])).

tff(c_2650,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2645,c_2451])).

tff(c_2666,plain,(
    ! [F_420,C_419,D_421,B_422,E_418,A_417] :
      ( m1_subset_1(k1_partfun1(A_417,B_422,C_419,D_421,E_418,F_420),k1_zfmisc_1(k2_zfmisc_1(A_417,D_421)))
      | ~ m1_subset_1(F_420,k1_zfmisc_1(k2_zfmisc_1(C_419,D_421)))
      | ~ v1_funct_1(F_420)
      | ~ m1_subset_1(E_418,k1_zfmisc_1(k2_zfmisc_1(A_417,B_422)))
      | ~ v1_funct_1(E_418) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2699,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2645,c_2666])).

tff(c_2715,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_2699])).

tff(c_2717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2650,c_2715])).

tff(c_2718,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2411])).

tff(c_2798,plain,(
    ! [C_442,A_440,D_443,F_444,E_445,B_441] :
      ( k1_partfun1(A_440,B_441,C_442,D_443,E_445,F_444) = k5_relat_1(E_445,F_444)
      | ~ m1_subset_1(F_444,k1_zfmisc_1(k2_zfmisc_1(C_442,D_443)))
      | ~ v1_funct_1(F_444)
      | ~ m1_subset_1(E_445,k1_zfmisc_1(k2_zfmisc_1(A_440,B_441)))
      | ~ v1_funct_1(E_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2804,plain,(
    ! [A_440,B_441,E_445] :
      ( k1_partfun1(A_440,B_441,'#skF_2','#skF_1',E_445,'#skF_4') = k5_relat_1(E_445,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_445,k1_zfmisc_1(k2_zfmisc_1(A_440,B_441)))
      | ~ v1_funct_1(E_445) ) ),
    inference(resolution,[status(thm)],[c_72,c_2798])).

tff(c_2959,plain,(
    ! [A_467,B_468,E_469] :
      ( k1_partfun1(A_467,B_468,'#skF_2','#skF_1',E_469,'#skF_4') = k5_relat_1(E_469,'#skF_4')
      | ~ m1_subset_1(E_469,k1_zfmisc_1(k2_zfmisc_1(A_467,B_468)))
      | ~ v1_funct_1(E_469) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2804])).

tff(c_2968,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_2959])).

tff(c_2976,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2718,c_2968])).

tff(c_24,plain,(
    ! [A_16,B_18] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_16,B_18)),k2_relat_1(B_18))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2222,plain,(
    ! [B_340,A_341] :
      ( r1_tarski(k2_relat_1(B_340),A_341)
      | ~ v5_relat_1(B_340,A_341)
      | ~ v1_relat_1(B_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2425,plain,(
    ! [B_376,A_377] :
      ( k2_relat_1(B_376) = A_377
      | ~ r1_tarski(A_377,k2_relat_1(B_376))
      | ~ v5_relat_1(B_376,A_377)
      | ~ v1_relat_1(B_376) ) ),
    inference(resolution,[status(thm)],[c_2222,c_4])).

tff(c_2445,plain,(
    ! [A_16,B_18] :
      ( k2_relat_1(k5_relat_1(A_16,B_18)) = k2_relat_1(B_18)
      | ~ v5_relat_1(B_18,k2_relat_1(k5_relat_1(A_16,B_18)))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(resolution,[status(thm)],[c_24,c_2425])).

tff(c_2986,plain,
    ( k2_relat_1(k5_relat_1('#skF_3','#skF_4')) = k2_relat_1('#skF_4')
    | ~ v5_relat_1('#skF_4',k2_relat_1(k6_partfun1('#skF_1')))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2976,c_2445])).

tff(c_2998,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2218,c_2221,c_2257,c_86,c_86,c_2976,c_2986])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2259,plain,(
    ! [B_351,A_352] :
      ( v5_relat_1(B_351,A_352)
      | ~ r1_tarski(k2_relat_1(B_351),A_352)
      | ~ v1_relat_1(B_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2273,plain,(
    ! [B_351] :
      ( v5_relat_1(B_351,k2_relat_1(B_351))
      | ~ v1_relat_1(B_351) ) ),
    inference(resolution,[status(thm)],[c_8,c_2259])).

tff(c_2298,plain,(
    ! [B_357] :
      ( v2_funct_2(B_357,k2_relat_1(B_357))
      | ~ v5_relat_1(B_357,k2_relat_1(B_357))
      | ~ v1_relat_1(B_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2312,plain,(
    ! [B_351] :
      ( v2_funct_2(B_351,k2_relat_1(B_351))
      | ~ v1_relat_1(B_351) ) ),
    inference(resolution,[status(thm)],[c_2273,c_2298])).

tff(c_3024,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2998,c_2312])).

tff(c_3049,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2221,c_3024])).

tff(c_3051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2141,c_3049])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.06/0.26  % Computer   : n007.cluster.edu
% 0.06/0.26  % Model      : x86_64 x86_64
% 0.06/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.26  % Memory     : 8042.1875MB
% 0.06/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.26  % CPULimit   : 60
% 0.06/0.26  % DateTime   : Tue Dec  1 20:09:21 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.10/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.73/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.78  
% 4.73/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.78  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.73/1.78  
% 4.73/1.78  %Foreground sorts:
% 4.73/1.78  
% 4.73/1.78  
% 4.73/1.78  %Background operators:
% 4.73/1.78  
% 4.73/1.78  
% 4.73/1.78  %Foreground operators:
% 4.73/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.73/1.78  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.73/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.73/1.78  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.73/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.73/1.78  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.73/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.73/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.73/1.78  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.73/1.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.73/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.73/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.73/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.73/1.78  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.73/1.78  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.73/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.73/1.78  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.73/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.73/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.73/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.73/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.73/1.78  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.73/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.73/1.78  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.73/1.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.73/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.73/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.73/1.78  
% 5.09/1.81  tff(f_36, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 5.09/1.81  tff(f_62, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.09/1.81  tff(f_183, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 5.09/1.81  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.09/1.81  tff(f_89, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_1)).
% 5.09/1.81  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.09/1.81  tff(f_141, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.09/1.81  tff(f_93, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.09/1.81  tff(f_129, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.09/1.81  tff(f_109, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.09/1.81  tff(f_107, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.09/1.81  tff(f_163, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 5.09/1.81  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.09/1.81  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.09/1.81  tff(f_73, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.09/1.81  tff(f_139, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.09/1.81  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 5.09/1.81  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.09/1.81  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.09/1.81  tff(f_117, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.09/1.81  tff(c_10, plain, (![A_3, B_4]: (v1_xboole_0(k2_zfmisc_1(A_3, B_4)) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.09/1.81  tff(c_22, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.09/1.81  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 5.09/1.81  tff(c_143, plain, (![B_68, A_69]: (v1_relat_1(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.09/1.81  tff(c_149, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_143])).
% 5.09/1.81  tff(c_158, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_149])).
% 5.09/1.81  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 5.09/1.81  tff(c_169, plain, (![A_72]: (v2_funct_1(A_72) | ~v1_funct_1(A_72) | ~v1_relat_1(A_72) | ~v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.09/1.81  tff(c_68, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 5.09/1.81  tff(c_130, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 5.09/1.81  tff(c_172, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_169, c_130])).
% 5.09/1.81  tff(c_175, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_82, c_172])).
% 5.09/1.81  tff(c_176, plain, (![B_73, A_74]: (v1_xboole_0(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.09/1.81  tff(c_182, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_176])).
% 5.09/1.81  tff(c_189, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_175, c_182])).
% 5.09/1.81  tff(c_194, plain, (~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_10, c_189])).
% 5.09/1.81  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 5.09/1.81  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 5.09/1.81  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_183])).
% 5.09/1.81  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 5.09/1.81  tff(c_62, plain, (![A_45]: (k6_relat_1(A_45)=k6_partfun1(A_45))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.09/1.81  tff(c_40, plain, (![A_22]: (v2_funct_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.09/1.81  tff(c_84, plain, (![A_22]: (v2_funct_1(k6_partfun1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_40])).
% 5.09/1.81  tff(c_1520, plain, (![E_260, F_262, C_261, B_264, A_259, D_263]: (m1_subset_1(k1_partfun1(A_259, B_264, C_261, D_263, E_260, F_262), k1_zfmisc_1(k2_zfmisc_1(A_259, D_263))) | ~m1_subset_1(F_262, k1_zfmisc_1(k2_zfmisc_1(C_261, D_263))) | ~v1_funct_1(F_262) | ~m1_subset_1(E_260, k1_zfmisc_1(k2_zfmisc_1(A_259, B_264))) | ~v1_funct_1(E_260))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.09/1.81  tff(c_50, plain, (![A_30]: (m1_subset_1(k6_relat_1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.09/1.81  tff(c_83, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50])).
% 5.09/1.81  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 5.09/1.81  tff(c_1207, plain, (![D_213, C_214, A_215, B_216]: (D_213=C_214 | ~r2_relset_1(A_215, B_216, C_214, D_213) | ~m1_subset_1(D_213, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.09/1.81  tff(c_1215, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_1207])).
% 5.09/1.81  tff(c_1230, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_1215])).
% 5.09/1.81  tff(c_1245, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1230])).
% 5.09/1.81  tff(c_1528, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1520, c_1245])).
% 5.09/1.81  tff(c_1553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_1528])).
% 5.09/1.81  tff(c_1554, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1230])).
% 5.09/1.81  tff(c_2120, plain, (![C_323, E_320, D_322, B_321, A_324]: (k1_xboole_0=C_323 | v2_funct_1(D_322) | ~v2_funct_1(k1_partfun1(A_324, B_321, B_321, C_323, D_322, E_320)) | ~m1_subset_1(E_320, k1_zfmisc_1(k2_zfmisc_1(B_321, C_323))) | ~v1_funct_2(E_320, B_321, C_323) | ~v1_funct_1(E_320) | ~m1_subset_1(D_322, k1_zfmisc_1(k2_zfmisc_1(A_324, B_321))) | ~v1_funct_2(D_322, A_324, B_321) | ~v1_funct_1(D_322))), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.09/1.81  tff(c_2124, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1554, c_2120])).
% 5.09/1.81  tff(c_2131, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_72, c_84, c_2124])).
% 5.09/1.81  tff(c_2132, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_130, c_2131])).
% 5.09/1.81  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.09/1.81  tff(c_2138, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2132, c_2])).
% 5.09/1.81  tff(c_2140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_2138])).
% 5.09/1.81  tff(c_2141, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_68])).
% 5.09/1.81  tff(c_2203, plain, (![B_338, A_339]: (v1_relat_1(B_338) | ~m1_subset_1(B_338, k1_zfmisc_1(A_339)) | ~v1_relat_1(A_339))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.09/1.81  tff(c_2212, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_2203])).
% 5.09/1.81  tff(c_2221, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2212])).
% 5.09/1.81  tff(c_2209, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_2203])).
% 5.09/1.81  tff(c_2218, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2209])).
% 5.09/1.81  tff(c_2245, plain, (![C_347, B_348, A_349]: (v5_relat_1(C_347, B_348) | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(A_349, B_348))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.09/1.81  tff(c_2257, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_2245])).
% 5.09/1.81  tff(c_28, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.09/1.81  tff(c_86, plain, (![A_19]: (k2_relat_1(k6_partfun1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_28])).
% 5.09/1.81  tff(c_2570, plain, (![D_405, B_403, F_406, A_402, E_407, C_404]: (k1_partfun1(A_402, B_403, C_404, D_405, E_407, F_406)=k5_relat_1(E_407, F_406) | ~m1_subset_1(F_406, k1_zfmisc_1(k2_zfmisc_1(C_404, D_405))) | ~v1_funct_1(F_406) | ~m1_subset_1(E_407, k1_zfmisc_1(k2_zfmisc_1(A_402, B_403))) | ~v1_funct_1(E_407))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.09/1.81  tff(c_2576, plain, (![A_402, B_403, E_407]: (k1_partfun1(A_402, B_403, '#skF_2', '#skF_1', E_407, '#skF_4')=k5_relat_1(E_407, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_407, k1_zfmisc_1(k2_zfmisc_1(A_402, B_403))) | ~v1_funct_1(E_407))), inference(resolution, [status(thm)], [c_72, c_2570])).
% 5.09/1.81  tff(c_2632, plain, (![A_414, B_415, E_416]: (k1_partfun1(A_414, B_415, '#skF_2', '#skF_1', E_416, '#skF_4')=k5_relat_1(E_416, '#skF_4') | ~m1_subset_1(E_416, k1_zfmisc_1(k2_zfmisc_1(A_414, B_415))) | ~v1_funct_1(E_416))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2576])).
% 5.09/1.81  tff(c_2638, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_2632])).
% 5.09/1.81  tff(c_2645, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2638])).
% 5.09/1.81  tff(c_2400, plain, (![D_371, C_372, A_373, B_374]: (D_371=C_372 | ~r2_relset_1(A_373, B_374, C_372, D_371) | ~m1_subset_1(D_371, k1_zfmisc_1(k2_zfmisc_1(A_373, B_374))) | ~m1_subset_1(C_372, k1_zfmisc_1(k2_zfmisc_1(A_373, B_374))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.09/1.81  tff(c_2404, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_2400])).
% 5.09/1.81  tff(c_2411, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_2404])).
% 5.09/1.81  tff(c_2451, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2411])).
% 5.09/1.81  tff(c_2650, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2645, c_2451])).
% 5.09/1.81  tff(c_2666, plain, (![F_420, C_419, D_421, B_422, E_418, A_417]: (m1_subset_1(k1_partfun1(A_417, B_422, C_419, D_421, E_418, F_420), k1_zfmisc_1(k2_zfmisc_1(A_417, D_421))) | ~m1_subset_1(F_420, k1_zfmisc_1(k2_zfmisc_1(C_419, D_421))) | ~v1_funct_1(F_420) | ~m1_subset_1(E_418, k1_zfmisc_1(k2_zfmisc_1(A_417, B_422))) | ~v1_funct_1(E_418))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.09/1.81  tff(c_2699, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2645, c_2666])).
% 5.09/1.81  tff(c_2715, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_2699])).
% 5.09/1.81  tff(c_2717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2650, c_2715])).
% 5.09/1.81  tff(c_2718, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2411])).
% 5.09/1.81  tff(c_2798, plain, (![C_442, A_440, D_443, F_444, E_445, B_441]: (k1_partfun1(A_440, B_441, C_442, D_443, E_445, F_444)=k5_relat_1(E_445, F_444) | ~m1_subset_1(F_444, k1_zfmisc_1(k2_zfmisc_1(C_442, D_443))) | ~v1_funct_1(F_444) | ~m1_subset_1(E_445, k1_zfmisc_1(k2_zfmisc_1(A_440, B_441))) | ~v1_funct_1(E_445))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.09/1.81  tff(c_2804, plain, (![A_440, B_441, E_445]: (k1_partfun1(A_440, B_441, '#skF_2', '#skF_1', E_445, '#skF_4')=k5_relat_1(E_445, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_445, k1_zfmisc_1(k2_zfmisc_1(A_440, B_441))) | ~v1_funct_1(E_445))), inference(resolution, [status(thm)], [c_72, c_2798])).
% 5.09/1.81  tff(c_2959, plain, (![A_467, B_468, E_469]: (k1_partfun1(A_467, B_468, '#skF_2', '#skF_1', E_469, '#skF_4')=k5_relat_1(E_469, '#skF_4') | ~m1_subset_1(E_469, k1_zfmisc_1(k2_zfmisc_1(A_467, B_468))) | ~v1_funct_1(E_469))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2804])).
% 5.09/1.81  tff(c_2968, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_2959])).
% 5.09/1.81  tff(c_2976, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2718, c_2968])).
% 5.09/1.81  tff(c_24, plain, (![A_16, B_18]: (r1_tarski(k2_relat_1(k5_relat_1(A_16, B_18)), k2_relat_1(B_18)) | ~v1_relat_1(B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.09/1.81  tff(c_2222, plain, (![B_340, A_341]: (r1_tarski(k2_relat_1(B_340), A_341) | ~v5_relat_1(B_340, A_341) | ~v1_relat_1(B_340))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.09/1.81  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/1.81  tff(c_2425, plain, (![B_376, A_377]: (k2_relat_1(B_376)=A_377 | ~r1_tarski(A_377, k2_relat_1(B_376)) | ~v5_relat_1(B_376, A_377) | ~v1_relat_1(B_376))), inference(resolution, [status(thm)], [c_2222, c_4])).
% 5.09/1.81  tff(c_2445, plain, (![A_16, B_18]: (k2_relat_1(k5_relat_1(A_16, B_18))=k2_relat_1(B_18) | ~v5_relat_1(B_18, k2_relat_1(k5_relat_1(A_16, B_18))) | ~v1_relat_1(B_18) | ~v1_relat_1(A_16))), inference(resolution, [status(thm)], [c_24, c_2425])).
% 5.09/1.81  tff(c_2986, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_4'))=k2_relat_1('#skF_4') | ~v5_relat_1('#skF_4', k2_relat_1(k6_partfun1('#skF_1'))) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2976, c_2445])).
% 5.09/1.81  tff(c_2998, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2218, c_2221, c_2257, c_86, c_86, c_2976, c_2986])).
% 5.09/1.81  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/1.81  tff(c_2259, plain, (![B_351, A_352]: (v5_relat_1(B_351, A_352) | ~r1_tarski(k2_relat_1(B_351), A_352) | ~v1_relat_1(B_351))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.09/1.81  tff(c_2273, plain, (![B_351]: (v5_relat_1(B_351, k2_relat_1(B_351)) | ~v1_relat_1(B_351))), inference(resolution, [status(thm)], [c_8, c_2259])).
% 5.09/1.81  tff(c_2298, plain, (![B_357]: (v2_funct_2(B_357, k2_relat_1(B_357)) | ~v5_relat_1(B_357, k2_relat_1(B_357)) | ~v1_relat_1(B_357))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.09/1.81  tff(c_2312, plain, (![B_351]: (v2_funct_2(B_351, k2_relat_1(B_351)) | ~v1_relat_1(B_351))), inference(resolution, [status(thm)], [c_2273, c_2298])).
% 5.09/1.81  tff(c_3024, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2998, c_2312])).
% 5.09/1.81  tff(c_3049, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2221, c_3024])).
% 5.09/1.81  tff(c_3051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2141, c_3049])).
% 5.09/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.09/1.81  
% 5.09/1.81  Inference rules
% 5.09/1.81  ----------------------
% 5.09/1.81  #Ref     : 0
% 5.09/1.81  #Sup     : 589
% 5.09/1.81  #Fact    : 0
% 5.09/1.81  #Define  : 0
% 5.09/1.81  #Split   : 11
% 5.09/1.81  #Chain   : 0
% 5.09/1.81  #Close   : 0
% 5.09/1.81  
% 5.09/1.81  Ordering : KBO
% 5.09/1.81  
% 5.09/1.81  Simplification rules
% 5.09/1.81  ----------------------
% 5.09/1.81  #Subsume      : 44
% 5.09/1.81  #Demod        : 585
% 5.09/1.81  #Tautology    : 162
% 5.09/1.81  #SimpNegUnit  : 6
% 5.09/1.81  #BackRed      : 19
% 5.09/1.81  
% 5.09/1.81  #Partial instantiations: 0
% 5.09/1.81  #Strategies tried      : 1
% 5.09/1.81  
% 5.09/1.81  Timing (in seconds)
% 5.09/1.81  ----------------------
% 5.14/1.81  Preprocessing        : 0.37
% 5.14/1.81  Parsing              : 0.20
% 5.14/1.81  CNF conversion       : 0.02
% 5.14/1.81  Main loop            : 0.81
% 5.14/1.81  Inferencing          : 0.30
% 5.14/1.81  Reduction            : 0.26
% 5.14/1.81  Demodulation         : 0.19
% 5.14/1.81  BG Simplification    : 0.03
% 5.14/1.81  Subsumption          : 0.15
% 5.14/1.81  Abstraction          : 0.04
% 5.14/1.81  MUC search           : 0.00
% 5.14/1.81  Cooper               : 0.00
% 5.14/1.81  Total                : 1.22
% 5.14/1.81  Index Insertion      : 0.00
% 5.14/1.81  Index Deletion       : 0.00
% 5.14/1.81  Index Matching       : 0.00
% 5.14/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
