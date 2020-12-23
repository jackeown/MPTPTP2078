%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0983+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:11 EST 2020

% Result     : Theorem 8.56s
% Output     : CNFRefutation 8.79s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 345 expanded)
%              Number of leaves         :   53 ( 140 expanded)
%              Depth                    :   10
%              Number of atoms          :  286 (1085 expanded)
%              Number of equality atoms :   67 ( 122 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_186,negated_conjecture,(
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

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_126,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_158,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_116,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_97,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_134,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_106,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_162,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_138,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_166,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_145,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_86,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_160,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_176,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_160])).

tff(c_90,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_218,plain,(
    ! [A_80] :
      ( v2_funct_1(A_80)
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80)
      | ~ v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_76,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_139,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_221,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_218,c_139])).

tff(c_224,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_90,c_221])).

tff(c_285,plain,(
    ! [C_93,B_94,A_95] :
      ( v1_xboole_0(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(B_94,A_95)))
      | ~ v1_xboole_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_295,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_285])).

tff(c_303,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_295])).

tff(c_84,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_177,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_160])).

tff(c_88,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_510,plain,(
    ! [A_110,B_111,C_112] :
      ( k1_relset_1(A_110,B_111,C_112) = k1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_527,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_510])).

tff(c_1674,plain,(
    ! [B_180,A_181,C_182] :
      ( k1_xboole_0 = B_180
      | k1_relset_1(A_181,B_180,C_182) = A_181
      | ~ v1_funct_2(C_182,A_181,B_180)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_181,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1698,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_1674])).

tff(c_1710,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_527,c_1698])).

tff(c_1714,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1710])).

tff(c_56,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_68,plain,(
    ! [A_51,B_53] :
      ( v2_funct_1(A_51)
      | k6_relat_1(k1_relat_1(A_51)) != k5_relat_1(A_51,B_53)
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_93,plain,(
    ! [A_51,B_53] :
      ( v2_funct_1(A_51)
      | k6_partfun1(k1_relat_1(A_51)) != k5_relat_1(A_51,B_53)
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_68])).

tff(c_1718,plain,(
    ! [B_53] :
      ( v2_funct_1('#skF_3')
      | k5_relat_1('#skF_3',B_53) != k6_partfun1('#skF_1')
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1714,c_93])).

tff(c_1722,plain,(
    ! [B_53] :
      ( v2_funct_1('#skF_3')
      | k5_relat_1('#skF_3',B_53) != k6_partfun1('#skF_1')
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_90,c_1718])).

tff(c_1904,plain,(
    ! [B_191] :
      ( k5_relat_1('#skF_3',B_191) != k6_partfun1('#skF_1')
      | ~ v1_funct_1(B_191)
      | ~ v1_relat_1(B_191) ) ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_1722])).

tff(c_1919,plain,
    ( k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_177,c_1904])).

tff(c_1929,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1919])).

tff(c_2463,plain,(
    ! [E_216,C_217,D_212,A_214,B_213,F_215] :
      ( k1_partfun1(A_214,B_213,C_217,D_212,E_216,F_215) = k5_relat_1(E_216,F_215)
      | ~ m1_subset_1(F_215,k1_zfmisc_1(k2_zfmisc_1(C_217,D_212)))
      | ~ v1_funct_1(F_215)
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1(A_214,B_213)))
      | ~ v1_funct_1(E_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2484,plain,(
    ! [A_214,B_213,E_216] :
      ( k1_partfun1(A_214,B_213,'#skF_2','#skF_1',E_216,'#skF_4') = k5_relat_1(E_216,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1(A_214,B_213)))
      | ~ v1_funct_1(E_216) ) ),
    inference(resolution,[status(thm)],[c_80,c_2463])).

tff(c_3897,plain,(
    ! [A_261,B_262,E_263] :
      ( k1_partfun1(A_261,B_262,'#skF_2','#skF_1',E_263,'#skF_4') = k5_relat_1(E_263,'#skF_4')
      | ~ m1_subset_1(E_263,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262)))
      | ~ v1_funct_1(E_263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2484])).

tff(c_3936,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_3897])).

tff(c_3953,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_3936])).

tff(c_38,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23] :
      ( m1_subset_1(k1_partfun1(A_19,B_20,C_21,D_22,E_23,F_24),k1_zfmisc_1(k2_zfmisc_1(A_19,D_22)))
      | ~ m1_subset_1(F_24,k1_zfmisc_1(k2_zfmisc_1(C_21,D_22)))
      | ~ v1_funct_1(F_24)
      | ~ m1_subset_1(E_23,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_1(E_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4414,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3953,c_38])).

tff(c_4418,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_84,c_80,c_4414])).

tff(c_46,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_78,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_1739,plain,(
    ! [D_183,C_184,A_185,B_186] :
      ( D_183 = C_184
      | ~ r2_relset_1(A_185,B_186,C_184,D_183)
      | ~ m1_subset_1(D_183,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186)))
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1749,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_78,c_1739])).

tff(c_1768,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1749])).

tff(c_4593,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4418,c_3953,c_3953,c_1768])).

tff(c_4594,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1929,c_4593])).

tff(c_4595,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1710])).

tff(c_48,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_124,plain,(
    ! [A_62] :
      ( k1_xboole_0 = A_62
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_128,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_124])).

tff(c_129,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_48])).

tff(c_4644,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4595,c_129])).

tff(c_4648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_303,c_4644])).

tff(c_4649,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_4671,plain,(
    ! [C_282,A_283,B_284] :
      ( v1_relat_1(C_282)
      | ~ m1_subset_1(C_282,k1_zfmisc_1(k2_zfmisc_1(A_283,B_284))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_4688,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_4671])).

tff(c_4769,plain,(
    ! [C_301,B_302,A_303] :
      ( v5_relat_1(C_301,B_302)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_303,B_302))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4786,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_4769])).

tff(c_5235,plain,(
    ! [A_345,B_346,C_347] :
      ( k2_relset_1(A_345,B_346,C_347) = k2_relat_1(C_347)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(A_345,B_346))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_5258,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_5235])).

tff(c_42,plain,(
    ! [A_25,B_26,C_27] :
      ( m1_subset_1(k2_relset_1(A_25,B_26,C_27),k1_zfmisc_1(B_26))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5411,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5258,c_42])).

tff(c_5415,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5411])).

tff(c_62,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_5429,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_5415,c_62])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5432,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_5429,c_16])).

tff(c_5526,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5432])).

tff(c_4687,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_4671])).

tff(c_74,plain,(
    ! [A_55] : k2_relat_1(k6_relat_1(A_55)) = A_55 ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_91,plain,(
    ! [A_55] : k2_relat_1(k6_partfun1(A_55)) = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_74])).

tff(c_7298,plain,(
    ! [E_439,D_435,F_438,A_437,B_436,C_440] :
      ( k1_partfun1(A_437,B_436,C_440,D_435,E_439,F_438) = k5_relat_1(E_439,F_438)
      | ~ m1_subset_1(F_438,k1_zfmisc_1(k2_zfmisc_1(C_440,D_435)))
      | ~ v1_funct_1(F_438)
      | ~ m1_subset_1(E_439,k1_zfmisc_1(k2_zfmisc_1(A_437,B_436)))
      | ~ v1_funct_1(E_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_7321,plain,(
    ! [A_437,B_436,E_439] :
      ( k1_partfun1(A_437,B_436,'#skF_2','#skF_1',E_439,'#skF_4') = k5_relat_1(E_439,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_439,k1_zfmisc_1(k2_zfmisc_1(A_437,B_436)))
      | ~ v1_funct_1(E_439) ) ),
    inference(resolution,[status(thm)],[c_80,c_7298])).

tff(c_8463,plain,(
    ! [A_477,B_478,E_479] :
      ( k1_partfun1(A_477,B_478,'#skF_2','#skF_1',E_479,'#skF_4') = k5_relat_1(E_479,'#skF_4')
      | ~ m1_subset_1(E_479,k1_zfmisc_1(k2_zfmisc_1(A_477,B_478)))
      | ~ v1_funct_1(E_479) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_7321])).

tff(c_8502,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_8463])).

tff(c_8519,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_8502])).

tff(c_8790,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8519,c_38])).

tff(c_8794,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_84,c_80,c_8790])).

tff(c_6302,plain,(
    ! [D_399,C_400,A_401,B_402] :
      ( D_399 = C_400
      | ~ r2_relset_1(A_401,B_402,C_400,D_399)
      | ~ m1_subset_1(D_399,k1_zfmisc_1(k2_zfmisc_1(A_401,B_402)))
      | ~ m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(A_401,B_402))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_6312,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_78,c_6302])).

tff(c_6331,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6312])).

tff(c_6518,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_6331])).

tff(c_9082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8794,c_8519,c_6518])).

tff(c_9083,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_6331])).

tff(c_9908,plain,(
    ! [B_530,D_529,F_532,E_533,C_534,A_531] :
      ( k1_partfun1(A_531,B_530,C_534,D_529,E_533,F_532) = k5_relat_1(E_533,F_532)
      | ~ m1_subset_1(F_532,k1_zfmisc_1(k2_zfmisc_1(C_534,D_529)))
      | ~ v1_funct_1(F_532)
      | ~ m1_subset_1(E_533,k1_zfmisc_1(k2_zfmisc_1(A_531,B_530)))
      | ~ v1_funct_1(E_533) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_9931,plain,(
    ! [A_531,B_530,E_533] :
      ( k1_partfun1(A_531,B_530,'#skF_2','#skF_1',E_533,'#skF_4') = k5_relat_1(E_533,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_533,k1_zfmisc_1(k2_zfmisc_1(A_531,B_530)))
      | ~ v1_funct_1(E_533) ) ),
    inference(resolution,[status(thm)],[c_80,c_9908])).

tff(c_11185,plain,(
    ! [A_570,B_571,E_572] :
      ( k1_partfun1(A_570,B_571,'#skF_2','#skF_1',E_572,'#skF_4') = k5_relat_1(E_572,'#skF_4')
      | ~ m1_subset_1(E_572,k1_zfmisc_1(k2_zfmisc_1(A_570,B_571)))
      | ~ v1_funct_1(E_572) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_9931])).

tff(c_11224,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_11185])).

tff(c_11241,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_9083,c_11224])).

tff(c_66,plain,(
    ! [A_48,B_50] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_48,B_50)),k2_relat_1(B_50))
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_11248,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11241,c_66])).

tff(c_11252,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4687,c_4688,c_91,c_11248])).

tff(c_11254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5526,c_11252])).

tff(c_11255,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5432])).

tff(c_34,plain,(
    ! [B_18] :
      ( v2_funct_2(B_18,k2_relat_1(B_18))
      | ~ v5_relat_1(B_18,k2_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_11268,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11255,c_34])).

tff(c_11274,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4688,c_4786,c_11255,c_11268])).

tff(c_11276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4649,c_11274])).

%------------------------------------------------------------------------------
