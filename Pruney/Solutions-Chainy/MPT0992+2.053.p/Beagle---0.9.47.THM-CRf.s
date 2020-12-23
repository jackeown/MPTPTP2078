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
% DateTime   : Thu Dec  3 10:13:39 EST 2020

% Result     : Theorem 6.41s
% Output     : CNFRefutation 6.41s
% Verified   : 
% Statistics : Number of formulae       :  187 (2879 expanded)
%              Number of leaves         :   38 ( 834 expanded)
%              Depth                    :   15
%              Number of atoms          :  291 (8848 expanded)
%              Number of equality atoms :   89 (3442 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_100,axiom,(
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

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_62,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_773,plain,(
    ! [C_139,A_140,B_141] :
      ( v1_relat_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_786,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_773])).

tff(c_60,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_98,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3717,plain,(
    ! [A_496,B_497,C_498] :
      ( k1_relset_1(A_496,B_497,C_498) = k1_relat_1(C_498)
      | ~ m1_subset_1(C_498,k1_zfmisc_1(k2_zfmisc_1(A_496,B_497))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3736,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_3717])).

tff(c_4230,plain,(
    ! [B_556,A_557,C_558] :
      ( k1_xboole_0 = B_556
      | k1_relset_1(A_557,B_556,C_558) = A_557
      | ~ v1_funct_2(C_558,A_557,B_556)
      | ~ m1_subset_1(C_558,k1_zfmisc_1(k2_zfmisc_1(A_557,B_556))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4243,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_4230])).

tff(c_4258,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3736,c_4243])).

tff(c_4259,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_4258])).

tff(c_32,plain,(
    ! [B_19,A_18] :
      ( k1_relat_1(k7_relat_1(B_19,A_18)) = A_18
      | ~ r1_tarski(A_18,k1_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4275,plain,(
    ! [A_18] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_18)) = A_18
      | ~ r1_tarski(A_18,'#skF_2')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4259,c_32])).

tff(c_4281,plain,(
    ! [A_18] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_18)) = A_18
      | ~ r1_tarski(A_18,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_4275])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_4045,plain,(
    ! [A_543,B_544,C_545,D_546] :
      ( k2_partfun1(A_543,B_544,C_545,D_546) = k7_relat_1(C_545,D_546)
      | ~ m1_subset_1(C_545,k1_zfmisc_1(k2_zfmisc_1(A_543,B_544)))
      | ~ v1_funct_1(C_545) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4052,plain,(
    ! [D_546] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_546) = k7_relat_1('#skF_5',D_546)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_4045])).

tff(c_4063,plain,(
    ! [D_546] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_546) = k7_relat_1('#skF_5',D_546) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4052])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1128,plain,(
    ! [A_184,B_185,C_186] :
      ( k1_relset_1(A_184,B_185,C_186) = k1_relat_1(C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1143,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_1128])).

tff(c_1679,plain,(
    ! [B_258,A_259,C_260] :
      ( k1_xboole_0 = B_258
      | k1_relset_1(A_259,B_258,C_260) = A_259
      | ~ v1_funct_2(C_260,A_259,B_258)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_259,B_258))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1689,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1679])).

tff(c_1702,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1143,c_1689])).

tff(c_1703,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_1702])).

tff(c_1725,plain,(
    ! [A_18] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_18)) = A_18
      | ~ r1_tarski(A_18,'#skF_2')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1703,c_32])).

tff(c_1731,plain,(
    ! [A_18] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_18)) = A_18
      | ~ r1_tarski(A_18,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_1725])).

tff(c_1311,plain,(
    ! [A_210,B_211,C_212,D_213] :
      ( k2_partfun1(A_210,B_211,C_212,D_213) = k7_relat_1(C_212,D_213)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211)))
      | ~ v1_funct_1(C_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1316,plain,(
    ! [D_213] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_213) = k7_relat_1('#skF_5',D_213)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_1311])).

tff(c_1324,plain,(
    ! [D_213] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_213) = k7_relat_1('#skF_5',D_213) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1316])).

tff(c_1896,plain,(
    ! [A_265,B_266,C_267,D_268] :
      ( m1_subset_1(k2_partfun1(A_265,B_266,C_267,D_268),k1_zfmisc_1(k2_zfmisc_1(A_265,B_266)))
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266)))
      | ~ v1_funct_1(C_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1922,plain,(
    ! [D_213] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_213),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1324,c_1896])).

tff(c_1942,plain,(
    ! [D_269] : m1_subset_1(k7_relat_1('#skF_5',D_269),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_1922])).

tff(c_38,plain,(
    ! [D_29,B_27,C_28,A_26] :
      ( m1_subset_1(D_29,k1_zfmisc_1(k2_zfmisc_1(B_27,C_28)))
      | ~ r1_tarski(k1_relat_1(D_29),B_27)
      | ~ m1_subset_1(D_29,k1_zfmisc_1(k2_zfmisc_1(A_26,C_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3169,plain,(
    ! [D_436,B_437] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_436),k1_zfmisc_1(k2_zfmisc_1(B_437,'#skF_3')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5',D_436)),B_437) ) ),
    inference(resolution,[status(thm)],[c_1942,c_38])).

tff(c_681,plain,(
    ! [A_126,B_127,C_128,D_129] :
      ( v1_funct_1(k2_partfun1(A_126,B_127,C_128,D_129))
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ v1_funct_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_686,plain,(
    ! [D_129] :
      ( v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5',D_129))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_681])).

tff(c_694,plain,(
    ! [D_129] : v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5',D_129)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_686])).

tff(c_58,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_155,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_694,c_155])).

tff(c_706,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_817,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_706])).

tff(c_1328,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1324,c_817])).

tff(c_3212,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_4')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_3169,c_1328])).

tff(c_3226,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1731,c_3212])).

tff(c_3235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_14,c_3226])).

tff(c_3237,plain,(
    m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_706])).

tff(c_3734,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) = k1_relat_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_3237,c_3717])).

tff(c_4067,plain,(
    k1_relset_1('#skF_4','#skF_3',k7_relat_1('#skF_5','#skF_4')) = k1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4063,c_4063,c_3734])).

tff(c_3236,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_706])).

tff(c_4071,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_4'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4063,c_3236])).

tff(c_4070,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4063,c_3237])).

tff(c_4450,plain,(
    ! [B_562,C_563,A_564] :
      ( k1_xboole_0 = B_562
      | v1_funct_2(C_563,A_564,B_562)
      | k1_relset_1(A_564,B_562,C_563) != A_564
      | ~ m1_subset_1(C_563,k1_zfmisc_1(k2_zfmisc_1(A_564,B_562))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4456,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_4'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_4070,c_4450])).

tff(c_4475,plain,(
    k1_relset_1('#skF_4','#skF_3',k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_4071,c_98,c_4456])).

tff(c_4501,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4067,c_4475])).

tff(c_4508,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4281,c_4501])).

tff(c_4515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4508])).

tff(c_4517,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_4516,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_4526,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4517,c_4516])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4520,plain,(
    ! [A_8] : r1_tarski('#skF_2',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4516,c_16])).

tff(c_4539,plain,(
    ! [A_8] : r1_tarski('#skF_3',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4526,c_4520])).

tff(c_4533,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4526,c_62])).

tff(c_5440,plain,(
    ! [B_707,A_708] :
      ( B_707 = A_708
      | ~ r1_tarski(B_707,A_708)
      | ~ r1_tarski(A_708,B_707) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5448,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_4533,c_5440])).

tff(c_5458,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4539,c_5448])).

tff(c_22,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4518,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_2',B_10) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4516,c_4516,c_22])).

tff(c_4541,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_3',B_10) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4526,c_4526,c_4518])).

tff(c_4538,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4526,c_64])).

tff(c_4542,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4541,c_4538])).

tff(c_4566,plain,(
    ! [A_571,B_572] :
      ( r1_tarski(A_571,B_572)
      | ~ m1_subset_1(A_571,k1_zfmisc_1(B_572)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4570,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_4542,c_4566])).

tff(c_5444,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_4570,c_5440])).

tff(c_5454,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4539,c_5444])).

tff(c_5487,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5458,c_5454])).

tff(c_4532,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4526,c_66])).

tff(c_5468,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5458,c_5458,c_4532])).

tff(c_5488,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5487,c_5468])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4521,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4516,c_8])).

tff(c_4531,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4526,c_4521])).

tff(c_5471,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5458,c_4531])).

tff(c_5489,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5487,c_68])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k7_relat_1(B_17,A_16),B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_5455,plain,(
    ! [A_8] :
      ( A_8 = '#skF_3'
      | ~ r1_tarski(A_8,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4539,c_5440])).

tff(c_5531,plain,(
    ! [A_714] :
      ( A_714 = '#skF_4'
      | ~ r1_tarski(A_714,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5458,c_5458,c_5455])).

tff(c_5546,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_4',A_16) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_5531])).

tff(c_5550,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5546])).

tff(c_5465,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5458,c_4542])).

tff(c_5507,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5487,c_5465])).

tff(c_20,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4519,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4516,c_4516,c_20])).

tff(c_4550,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4526,c_4526,c_4519])).

tff(c_5466,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5458,c_5458,c_4550])).

tff(c_5570,plain,(
    ! [C_719,A_720,B_721] :
      ( v1_relat_1(C_719)
      | ~ m1_subset_1(C_719,k1_zfmisc_1(k2_zfmisc_1(A_720,B_721))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5584,plain,(
    ! [C_722] :
      ( v1_relat_1(C_722)
      | ~ m1_subset_1(C_722,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5466,c_5570])).

tff(c_5587,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5507,c_5584])).

tff(c_5595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5550,c_5587])).

tff(c_5596,plain,(
    ! [A_16] : k7_relat_1('#skF_4',A_16) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5546])).

tff(c_5467,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_4',B_10) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5458,c_5458,c_4541])).

tff(c_6334,plain,(
    ! [A_843,B_844,C_845,D_846] :
      ( k2_partfun1(A_843,B_844,C_845,D_846) = k7_relat_1(C_845,D_846)
      | ~ m1_subset_1(C_845,k1_zfmisc_1(k2_zfmisc_1(A_843,B_844)))
      | ~ v1_funct_1(C_845) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_6471,plain,(
    ! [B_880,C_881,D_882] :
      ( k2_partfun1('#skF_4',B_880,C_881,D_882) = k7_relat_1(C_881,D_882)
      | ~ m1_subset_1(C_881,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_881) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5467,c_6334])).

tff(c_6473,plain,(
    ! [B_880,D_882] :
      ( k2_partfun1('#skF_4',B_880,'#skF_4',D_882) = k7_relat_1('#skF_4',D_882)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5507,c_6471])).

tff(c_6479,plain,(
    ! [B_880,D_882] : k2_partfun1('#skF_4',B_880,'#skF_4',D_882) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5489,c_5596,c_6473])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5702,plain,(
    ! [C_738,B_739,A_740] :
      ( ~ v1_xboole_0(C_738)
      | ~ m1_subset_1(B_739,k1_zfmisc_1(C_738))
      | ~ r2_hidden(A_740,B_739) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5722,plain,(
    ! [B_745,A_746,A_747] :
      ( ~ v1_xboole_0(B_745)
      | ~ r2_hidden(A_746,A_747)
      | ~ r1_tarski(A_747,B_745) ) ),
    inference(resolution,[status(thm)],[c_26,c_5702])).

tff(c_5726,plain,(
    ! [B_748,A_749,B_750] :
      ( ~ v1_xboole_0(B_748)
      | ~ r1_tarski(A_749,B_748)
      | r1_tarski(A_749,B_750) ) ),
    inference(resolution,[status(thm)],[c_6,c_5722])).

tff(c_5737,plain,(
    ! [B_751,B_752] :
      ( ~ v1_xboole_0(B_751)
      | r1_tarski(B_751,B_752) ) ),
    inference(resolution,[status(thm)],[c_14,c_5726])).

tff(c_4579,plain,(
    ! [B_577,A_578] :
      ( B_577 = A_578
      | ~ r1_tarski(B_577,A_578)
      | ~ r1_tarski(A_578,B_577) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4587,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_4533,c_4579])).

tff(c_4597,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4539,c_4587])).

tff(c_4583,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_4570,c_4579])).

tff(c_4593,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4539,c_4583])).

tff(c_4628,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4597,c_4593])).

tff(c_4629,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4628,c_68])).

tff(c_4604,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4597,c_4542])).

tff(c_4646,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4628,c_4604])).

tff(c_4606,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_4',B_10) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4597,c_4597,c_4541])).

tff(c_5116,plain,(
    ! [A_651,B_652,C_653,D_654] :
      ( v1_funct_1(k2_partfun1(A_651,B_652,C_653,D_654))
      | ~ m1_subset_1(C_653,k1_zfmisc_1(k2_zfmisc_1(A_651,B_652)))
      | ~ v1_funct_1(C_653) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5420,plain,(
    ! [B_702,C_703,D_704] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_702,C_703,D_704))
      | ~ m1_subset_1(C_703,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_703) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4606,c_5116])).

tff(c_5422,plain,(
    ! [B_702,D_704] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_702,'#skF_4',D_704))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4646,c_5420])).

tff(c_5428,plain,(
    ! [B_702,D_704] : v1_funct_1(k2_partfun1('#skF_4',B_702,'#skF_4',D_704)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4629,c_5422])).

tff(c_4572,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ v1_funct_2(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4526,c_4526,c_4550,c_4526,c_58])).

tff(c_4573,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4572])).

tff(c_4602,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4597,c_4597,c_4573])).

tff(c_4688,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4628,c_4602])).

tff(c_5432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5428,c_4688])).

tff(c_5433,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4572])).

tff(c_5528,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5487,c_5458,c_5458,c_5458,c_5487,c_5458,c_5458,c_5458,c_5433])).

tff(c_5529,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5528])).

tff(c_5673,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_5529])).

tff(c_5758,plain,(
    ~ v1_xboole_0(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_5737,c_5673])).

tff(c_6481,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6479,c_5758])).

tff(c_6486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5471,c_6481])).

tff(c_6488,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5528])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6556,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_6488,c_24])).

tff(c_6490,plain,(
    ! [A_8] :
      ( A_8 = '#skF_4'
      | ~ r1_tarski(A_8,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5458,c_5458,c_5455])).

tff(c_6562,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6556,c_6490])).

tff(c_6487,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_5528])).

tff(c_6638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5488,c_6562,c_6487])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.41/2.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.41/2.31  
% 6.41/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.41/2.32  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.41/2.32  
% 6.41/2.32  %Foreground sorts:
% 6.41/2.32  
% 6.41/2.32  
% 6.41/2.32  %Background operators:
% 6.41/2.32  
% 6.41/2.32  
% 6.41/2.32  %Foreground operators:
% 6.41/2.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.41/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.41/2.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.41/2.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.41/2.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.41/2.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.41/2.32  tff('#skF_5', type, '#skF_5': $i).
% 6.41/2.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.41/2.32  tff('#skF_2', type, '#skF_2': $i).
% 6.41/2.32  tff('#skF_3', type, '#skF_3': $i).
% 6.41/2.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.41/2.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.41/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.41/2.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.41/2.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.41/2.32  tff('#skF_4', type, '#skF_4': $i).
% 6.41/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.41/2.32  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.41/2.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.41/2.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.41/2.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.41/2.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.41/2.32  
% 6.41/2.34  tff(f_134, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 6.41/2.34  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.41/2.34  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.41/2.34  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.41/2.34  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 6.41/2.34  tff(f_114, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.41/2.34  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.41/2.34  tff(f_108, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 6.41/2.34  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 6.41/2.34  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.41/2.34  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.41/2.34  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.41/2.34  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.41/2.34  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 6.41/2.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.41/2.34  tff(f_58, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 6.41/2.34  tff(c_62, plain, (r1_tarski('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.41/2.34  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.41/2.34  tff(c_773, plain, (![C_139, A_140, B_141]: (v1_relat_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.41/2.34  tff(c_786, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_773])).
% 6.41/2.34  tff(c_60, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.41/2.34  tff(c_98, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_60])).
% 6.41/2.34  tff(c_66, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.41/2.34  tff(c_3717, plain, (![A_496, B_497, C_498]: (k1_relset_1(A_496, B_497, C_498)=k1_relat_1(C_498) | ~m1_subset_1(C_498, k1_zfmisc_1(k2_zfmisc_1(A_496, B_497))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.41/2.34  tff(c_3736, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_3717])).
% 6.41/2.34  tff(c_4230, plain, (![B_556, A_557, C_558]: (k1_xboole_0=B_556 | k1_relset_1(A_557, B_556, C_558)=A_557 | ~v1_funct_2(C_558, A_557, B_556) | ~m1_subset_1(C_558, k1_zfmisc_1(k2_zfmisc_1(A_557, B_556))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.41/2.34  tff(c_4243, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_4230])).
% 6.41/2.34  tff(c_4258, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3736, c_4243])).
% 6.41/2.34  tff(c_4259, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_98, c_4258])).
% 6.41/2.34  tff(c_32, plain, (![B_19, A_18]: (k1_relat_1(k7_relat_1(B_19, A_18))=A_18 | ~r1_tarski(A_18, k1_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.41/2.34  tff(c_4275, plain, (![A_18]: (k1_relat_1(k7_relat_1('#skF_5', A_18))=A_18 | ~r1_tarski(A_18, '#skF_2') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4259, c_32])).
% 6.41/2.34  tff(c_4281, plain, (![A_18]: (k1_relat_1(k7_relat_1('#skF_5', A_18))=A_18 | ~r1_tarski(A_18, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_786, c_4275])).
% 6.41/2.34  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.41/2.34  tff(c_4045, plain, (![A_543, B_544, C_545, D_546]: (k2_partfun1(A_543, B_544, C_545, D_546)=k7_relat_1(C_545, D_546) | ~m1_subset_1(C_545, k1_zfmisc_1(k2_zfmisc_1(A_543, B_544))) | ~v1_funct_1(C_545))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.41/2.34  tff(c_4052, plain, (![D_546]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_546)=k7_relat_1('#skF_5', D_546) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_4045])).
% 6.41/2.34  tff(c_4063, plain, (![D_546]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_546)=k7_relat_1('#skF_5', D_546))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4052])).
% 6.41/2.34  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.41/2.34  tff(c_1128, plain, (![A_184, B_185, C_186]: (k1_relset_1(A_184, B_185, C_186)=k1_relat_1(C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.41/2.34  tff(c_1143, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_1128])).
% 6.41/2.34  tff(c_1679, plain, (![B_258, A_259, C_260]: (k1_xboole_0=B_258 | k1_relset_1(A_259, B_258, C_260)=A_259 | ~v1_funct_2(C_260, A_259, B_258) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_259, B_258))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.41/2.34  tff(c_1689, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_1679])).
% 6.41/2.34  tff(c_1702, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1143, c_1689])).
% 6.41/2.34  tff(c_1703, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_98, c_1702])).
% 6.41/2.34  tff(c_1725, plain, (![A_18]: (k1_relat_1(k7_relat_1('#skF_5', A_18))=A_18 | ~r1_tarski(A_18, '#skF_2') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1703, c_32])).
% 6.41/2.34  tff(c_1731, plain, (![A_18]: (k1_relat_1(k7_relat_1('#skF_5', A_18))=A_18 | ~r1_tarski(A_18, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_786, c_1725])).
% 6.41/2.34  tff(c_1311, plain, (![A_210, B_211, C_212, D_213]: (k2_partfun1(A_210, B_211, C_212, D_213)=k7_relat_1(C_212, D_213) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))) | ~v1_funct_1(C_212))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.41/2.34  tff(c_1316, plain, (![D_213]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_213)=k7_relat_1('#skF_5', D_213) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_1311])).
% 6.41/2.34  tff(c_1324, plain, (![D_213]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_213)=k7_relat_1('#skF_5', D_213))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1316])).
% 6.41/2.34  tff(c_1896, plain, (![A_265, B_266, C_267, D_268]: (m1_subset_1(k2_partfun1(A_265, B_266, C_267, D_268), k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))) | ~v1_funct_1(C_267))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.41/2.34  tff(c_1922, plain, (![D_213]: (m1_subset_1(k7_relat_1('#skF_5', D_213), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1324, c_1896])).
% 6.41/2.34  tff(c_1942, plain, (![D_269]: (m1_subset_1(k7_relat_1('#skF_5', D_269), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_1922])).
% 6.41/2.34  tff(c_38, plain, (![D_29, B_27, C_28, A_26]: (m1_subset_1(D_29, k1_zfmisc_1(k2_zfmisc_1(B_27, C_28))) | ~r1_tarski(k1_relat_1(D_29), B_27) | ~m1_subset_1(D_29, k1_zfmisc_1(k2_zfmisc_1(A_26, C_28))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.41/2.34  tff(c_3169, plain, (![D_436, B_437]: (m1_subset_1(k7_relat_1('#skF_5', D_436), k1_zfmisc_1(k2_zfmisc_1(B_437, '#skF_3'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', D_436)), B_437))), inference(resolution, [status(thm)], [c_1942, c_38])).
% 6.41/2.34  tff(c_681, plain, (![A_126, B_127, C_128, D_129]: (v1_funct_1(k2_partfun1(A_126, B_127, C_128, D_129)) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~v1_funct_1(C_128))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.41/2.34  tff(c_686, plain, (![D_129]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_129)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_681])).
% 6.41/2.34  tff(c_694, plain, (![D_129]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_129)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_686])).
% 6.41/2.34  tff(c_58, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.41/2.34  tff(c_155, plain, (~v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_58])).
% 6.41/2.34  tff(c_705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_694, c_155])).
% 6.41/2.34  tff(c_706, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_58])).
% 6.41/2.34  tff(c_817, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_706])).
% 6.41/2.34  tff(c_1328, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1324, c_817])).
% 6.41/2.34  tff(c_3212, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_4')), '#skF_4')), inference(resolution, [status(thm)], [c_3169, c_1328])).
% 6.41/2.34  tff(c_3226, plain, (~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1731, c_3212])).
% 6.41/2.34  tff(c_3235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_14, c_3226])).
% 6.41/2.34  tff(c_3237, plain, (m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_706])).
% 6.41/2.34  tff(c_3734, plain, (k1_relset_1('#skF_4', '#skF_3', k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))=k1_relat_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_3237, c_3717])).
% 6.41/2.34  tff(c_4067, plain, (k1_relset_1('#skF_4', '#skF_3', k7_relat_1('#skF_5', '#skF_4'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4063, c_4063, c_3734])).
% 6.41/2.34  tff(c_3236, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_706])).
% 6.41/2.34  tff(c_4071, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_4'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4063, c_3236])).
% 6.41/2.34  tff(c_4070, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4063, c_3237])).
% 6.41/2.34  tff(c_4450, plain, (![B_562, C_563, A_564]: (k1_xboole_0=B_562 | v1_funct_2(C_563, A_564, B_562) | k1_relset_1(A_564, B_562, C_563)!=A_564 | ~m1_subset_1(C_563, k1_zfmisc_1(k2_zfmisc_1(A_564, B_562))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.41/2.34  tff(c_4456, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_4'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(resolution, [status(thm)], [c_4070, c_4450])).
% 6.41/2.34  tff(c_4475, plain, (k1_relset_1('#skF_4', '#skF_3', k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_4071, c_98, c_4456])).
% 6.41/2.34  tff(c_4501, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4067, c_4475])).
% 6.41/2.34  tff(c_4508, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4281, c_4501])).
% 6.41/2.34  tff(c_4515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_4508])).
% 6.41/2.34  tff(c_4517, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_60])).
% 6.41/2.34  tff(c_4516, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_60])).
% 6.41/2.34  tff(c_4526, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4517, c_4516])).
% 6.41/2.34  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.41/2.34  tff(c_4520, plain, (![A_8]: (r1_tarski('#skF_2', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_4516, c_16])).
% 6.41/2.34  tff(c_4539, plain, (![A_8]: (r1_tarski('#skF_3', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_4526, c_4520])).
% 6.41/2.34  tff(c_4533, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4526, c_62])).
% 6.41/2.34  tff(c_5440, plain, (![B_707, A_708]: (B_707=A_708 | ~r1_tarski(B_707, A_708) | ~r1_tarski(A_708, B_707))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.41/2.34  tff(c_5448, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_4533, c_5440])).
% 6.41/2.34  tff(c_5458, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4539, c_5448])).
% 6.41/2.34  tff(c_22, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.41/2.34  tff(c_4518, plain, (![B_10]: (k2_zfmisc_1('#skF_2', B_10)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4516, c_4516, c_22])).
% 6.41/2.34  tff(c_4541, plain, (![B_10]: (k2_zfmisc_1('#skF_3', B_10)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4526, c_4526, c_4518])).
% 6.41/2.34  tff(c_4538, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4526, c_64])).
% 6.41/2.34  tff(c_4542, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4541, c_4538])).
% 6.41/2.34  tff(c_4566, plain, (![A_571, B_572]: (r1_tarski(A_571, B_572) | ~m1_subset_1(A_571, k1_zfmisc_1(B_572)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.41/2.34  tff(c_4570, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_4542, c_4566])).
% 6.41/2.34  tff(c_5444, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_4570, c_5440])).
% 6.41/2.34  tff(c_5454, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4539, c_5444])).
% 6.41/2.34  tff(c_5487, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5458, c_5454])).
% 6.41/2.34  tff(c_4532, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4526, c_66])).
% 6.41/2.34  tff(c_5468, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5458, c_5458, c_4532])).
% 6.41/2.34  tff(c_5488, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5487, c_5468])).
% 6.41/2.34  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.41/2.34  tff(c_4521, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4516, c_8])).
% 6.41/2.34  tff(c_4531, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4526, c_4521])).
% 6.41/2.34  tff(c_5471, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5458, c_4531])).
% 6.41/2.34  tff(c_5489, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5487, c_68])).
% 6.41/2.34  tff(c_30, plain, (![B_17, A_16]: (r1_tarski(k7_relat_1(B_17, A_16), B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.41/2.34  tff(c_5455, plain, (![A_8]: (A_8='#skF_3' | ~r1_tarski(A_8, '#skF_3'))), inference(resolution, [status(thm)], [c_4539, c_5440])).
% 6.41/2.34  tff(c_5531, plain, (![A_714]: (A_714='#skF_4' | ~r1_tarski(A_714, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5458, c_5458, c_5455])).
% 6.41/2.34  tff(c_5546, plain, (![A_16]: (k7_relat_1('#skF_4', A_16)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_5531])).
% 6.41/2.34  tff(c_5550, plain, (~v1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_5546])).
% 6.41/2.34  tff(c_5465, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5458, c_4542])).
% 6.41/2.34  tff(c_5507, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5487, c_5465])).
% 6.41/2.34  tff(c_20, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.41/2.34  tff(c_4519, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4516, c_4516, c_20])).
% 6.41/2.34  tff(c_4550, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4526, c_4526, c_4519])).
% 6.41/2.34  tff(c_5466, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5458, c_5458, c_4550])).
% 6.41/2.34  tff(c_5570, plain, (![C_719, A_720, B_721]: (v1_relat_1(C_719) | ~m1_subset_1(C_719, k1_zfmisc_1(k2_zfmisc_1(A_720, B_721))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.41/2.34  tff(c_5584, plain, (![C_722]: (v1_relat_1(C_722) | ~m1_subset_1(C_722, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5466, c_5570])).
% 6.41/2.34  tff(c_5587, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_5507, c_5584])).
% 6.41/2.34  tff(c_5595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5550, c_5587])).
% 6.41/2.34  tff(c_5596, plain, (![A_16]: (k7_relat_1('#skF_4', A_16)='#skF_4')), inference(splitRight, [status(thm)], [c_5546])).
% 6.41/2.34  tff(c_5467, plain, (![B_10]: (k2_zfmisc_1('#skF_4', B_10)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5458, c_5458, c_4541])).
% 6.41/2.34  tff(c_6334, plain, (![A_843, B_844, C_845, D_846]: (k2_partfun1(A_843, B_844, C_845, D_846)=k7_relat_1(C_845, D_846) | ~m1_subset_1(C_845, k1_zfmisc_1(k2_zfmisc_1(A_843, B_844))) | ~v1_funct_1(C_845))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.41/2.34  tff(c_6471, plain, (![B_880, C_881, D_882]: (k2_partfun1('#skF_4', B_880, C_881, D_882)=k7_relat_1(C_881, D_882) | ~m1_subset_1(C_881, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_881))), inference(superposition, [status(thm), theory('equality')], [c_5467, c_6334])).
% 6.41/2.34  tff(c_6473, plain, (![B_880, D_882]: (k2_partfun1('#skF_4', B_880, '#skF_4', D_882)=k7_relat_1('#skF_4', D_882) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_5507, c_6471])).
% 6.41/2.34  tff(c_6479, plain, (![B_880, D_882]: (k2_partfun1('#skF_4', B_880, '#skF_4', D_882)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5489, c_5596, c_6473])).
% 6.41/2.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.41/2.34  tff(c_26, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.41/2.34  tff(c_5702, plain, (![C_738, B_739, A_740]: (~v1_xboole_0(C_738) | ~m1_subset_1(B_739, k1_zfmisc_1(C_738)) | ~r2_hidden(A_740, B_739))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.41/2.34  tff(c_5722, plain, (![B_745, A_746, A_747]: (~v1_xboole_0(B_745) | ~r2_hidden(A_746, A_747) | ~r1_tarski(A_747, B_745))), inference(resolution, [status(thm)], [c_26, c_5702])).
% 6.41/2.34  tff(c_5726, plain, (![B_748, A_749, B_750]: (~v1_xboole_0(B_748) | ~r1_tarski(A_749, B_748) | r1_tarski(A_749, B_750))), inference(resolution, [status(thm)], [c_6, c_5722])).
% 6.41/2.34  tff(c_5737, plain, (![B_751, B_752]: (~v1_xboole_0(B_751) | r1_tarski(B_751, B_752))), inference(resolution, [status(thm)], [c_14, c_5726])).
% 6.41/2.34  tff(c_4579, plain, (![B_577, A_578]: (B_577=A_578 | ~r1_tarski(B_577, A_578) | ~r1_tarski(A_578, B_577))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.41/2.34  tff(c_4587, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_4533, c_4579])).
% 6.41/2.34  tff(c_4597, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4539, c_4587])).
% 6.41/2.34  tff(c_4583, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_4570, c_4579])).
% 6.41/2.34  tff(c_4593, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4539, c_4583])).
% 6.41/2.34  tff(c_4628, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4597, c_4593])).
% 6.41/2.34  tff(c_4629, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4628, c_68])).
% 6.41/2.34  tff(c_4604, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4597, c_4542])).
% 6.41/2.34  tff(c_4646, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4628, c_4604])).
% 6.41/2.34  tff(c_4606, plain, (![B_10]: (k2_zfmisc_1('#skF_4', B_10)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4597, c_4597, c_4541])).
% 6.41/2.34  tff(c_5116, plain, (![A_651, B_652, C_653, D_654]: (v1_funct_1(k2_partfun1(A_651, B_652, C_653, D_654)) | ~m1_subset_1(C_653, k1_zfmisc_1(k2_zfmisc_1(A_651, B_652))) | ~v1_funct_1(C_653))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.41/2.34  tff(c_5420, plain, (![B_702, C_703, D_704]: (v1_funct_1(k2_partfun1('#skF_4', B_702, C_703, D_704)) | ~m1_subset_1(C_703, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_703))), inference(superposition, [status(thm), theory('equality')], [c_4606, c_5116])).
% 6.41/2.34  tff(c_5422, plain, (![B_702, D_704]: (v1_funct_1(k2_partfun1('#skF_4', B_702, '#skF_4', D_704)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4646, c_5420])).
% 6.41/2.34  tff(c_5428, plain, (![B_702, D_704]: (v1_funct_1(k2_partfun1('#skF_4', B_702, '#skF_4', D_704)))), inference(demodulation, [status(thm), theory('equality')], [c_4629, c_5422])).
% 6.41/2.34  tff(c_4572, plain, (~m1_subset_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1('#skF_3')) | ~v1_funct_2(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4526, c_4526, c_4550, c_4526, c_58])).
% 6.41/2.34  tff(c_4573, plain, (~v1_funct_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_4572])).
% 6.41/2.34  tff(c_4602, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4597, c_4597, c_4573])).
% 6.41/2.34  tff(c_4688, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4628, c_4602])).
% 6.41/2.34  tff(c_5432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5428, c_4688])).
% 6.41/2.34  tff(c_5433, plain, (~v1_funct_2(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_4572])).
% 6.41/2.34  tff(c_5528, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5487, c_5458, c_5458, c_5458, c_5487, c_5458, c_5458, c_5458, c_5433])).
% 6.41/2.34  tff(c_5529, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5528])).
% 6.41/2.34  tff(c_5673, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_26, c_5529])).
% 6.41/2.34  tff(c_5758, plain, (~v1_xboole_0(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_5737, c_5673])).
% 6.41/2.34  tff(c_6481, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6479, c_5758])).
% 6.41/2.34  tff(c_6486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5471, c_6481])).
% 6.41/2.34  tff(c_6488, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5528])).
% 6.41/2.34  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.41/2.34  tff(c_6556, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_6488, c_24])).
% 6.41/2.34  tff(c_6490, plain, (![A_8]: (A_8='#skF_4' | ~r1_tarski(A_8, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5458, c_5458, c_5455])).
% 6.41/2.34  tff(c_6562, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_6556, c_6490])).
% 6.41/2.34  tff(c_6487, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_5528])).
% 6.41/2.34  tff(c_6638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5488, c_6562, c_6487])).
% 6.41/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.41/2.34  
% 6.41/2.34  Inference rules
% 6.41/2.34  ----------------------
% 6.41/2.34  #Ref     : 0
% 6.41/2.34  #Sup     : 1448
% 6.41/2.34  #Fact    : 0
% 6.41/2.34  #Define  : 0
% 6.41/2.34  #Split   : 35
% 6.41/2.34  #Chain   : 0
% 6.41/2.34  #Close   : 0
% 6.41/2.34  
% 6.41/2.34  Ordering : KBO
% 6.41/2.34  
% 6.41/2.34  Simplification rules
% 6.41/2.34  ----------------------
% 6.41/2.34  #Subsume      : 305
% 6.41/2.34  #Demod        : 942
% 6.41/2.34  #Tautology    : 547
% 6.41/2.34  #SimpNegUnit  : 24
% 6.41/2.34  #BackRed      : 77
% 6.41/2.34  
% 6.41/2.34  #Partial instantiations: 0
% 6.41/2.34  #Strategies tried      : 1
% 6.41/2.34  
% 6.41/2.34  Timing (in seconds)
% 6.41/2.34  ----------------------
% 6.41/2.34  Preprocessing        : 0.35
% 6.41/2.34  Parsing              : 0.18
% 6.41/2.34  CNF conversion       : 0.02
% 6.41/2.34  Main loop            : 1.22
% 6.41/2.34  Inferencing          : 0.44
% 6.41/2.34  Reduction            : 0.39
% 6.41/2.34  Demodulation         : 0.27
% 6.41/2.34  BG Simplification    : 0.05
% 6.41/2.34  Subsumption          : 0.23
% 6.41/2.34  Abstraction          : 0.05
% 6.41/2.34  MUC search           : 0.00
% 6.41/2.34  Cooper               : 0.00
% 6.41/2.34  Total                : 1.63
% 6.41/2.34  Index Insertion      : 0.00
% 6.41/2.34  Index Deletion       : 0.00
% 6.41/2.34  Index Matching       : 0.00
% 6.41/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
