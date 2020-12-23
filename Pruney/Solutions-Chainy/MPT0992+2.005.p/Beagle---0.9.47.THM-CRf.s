%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:31 EST 2020

% Result     : Theorem 6.02s
% Output     : CNFRefutation 6.02s
% Verified   : 
% Statistics : Number of formulae       :  200 (2352 expanded)
%              Number of leaves         :   45 ( 712 expanded)
%              Depth                    :   14
%              Number of atoms          :  311 (7558 expanded)
%              Number of equality atoms :   79 (2892 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_161,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_127,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_141,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_135,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_72,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_820,plain,(
    ! [C_170,A_171,B_172] :
      ( v1_relat_1(C_170)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_837,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_820])).

tff(c_70,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_91,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_76,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_3341,plain,(
    ! [A_468,B_469,C_470] :
      ( k1_relset_1(A_468,B_469,C_470) = k1_relat_1(C_470)
      | ~ m1_subset_1(C_470,k1_zfmisc_1(k2_zfmisc_1(A_468,B_469))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3364,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_3341])).

tff(c_3965,plain,(
    ! [B_537,A_538,C_539] :
      ( k1_xboole_0 = B_537
      | k1_relset_1(A_538,B_537,C_539) = A_538
      | ~ v1_funct_2(C_539,A_538,B_537)
      | ~ m1_subset_1(C_539,k1_zfmisc_1(k2_zfmisc_1(A_538,B_537))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3978,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_3965])).

tff(c_3995,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3364,c_3978])).

tff(c_3996,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_3995])).

tff(c_38,plain,(
    ! [B_28,A_27] :
      ( k1_relat_1(k7_relat_1(B_28,A_27)) = A_27
      | ~ r1_tarski(A_27,k1_relat_1(B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4007,plain,(
    ! [A_27] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_27)) = A_27
      | ~ r1_tarski(A_27,'#skF_2')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3996,c_38])).

tff(c_4013,plain,(
    ! [A_27] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_27)) = A_27
      | ~ r1_tarski(A_27,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_4007])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_3775,plain,(
    ! [A_521,B_522,C_523,D_524] :
      ( k2_partfun1(A_521,B_522,C_523,D_524) = k7_relat_1(C_523,D_524)
      | ~ m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1(A_521,B_522)))
      | ~ v1_funct_1(C_523) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_3784,plain,(
    ! [D_524] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_524) = k7_relat_1('#skF_5',D_524)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_3775])).

tff(c_3799,plain,(
    ! [D_524] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_524) = k7_relat_1('#skF_5',D_524) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3784])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_960,plain,(
    ! [A_192,B_193] :
      ( ~ r2_hidden('#skF_1'(A_192,B_193),B_193)
      | r1_tarski(A_192,B_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_965,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_960])).

tff(c_1482,plain,(
    ! [A_268,B_269,C_270] :
      ( k1_relset_1(A_268,B_269,C_270) = k1_relat_1(C_270)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_268,B_269))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1501,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_1482])).

tff(c_2377,plain,(
    ! [B_349,A_350,C_351] :
      ( k1_xboole_0 = B_349
      | k1_relset_1(A_350,B_349,C_351) = A_350
      | ~ v1_funct_2(C_351,A_350,B_349)
      | ~ m1_subset_1(C_351,k1_zfmisc_1(k2_zfmisc_1(A_350,B_349))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2387,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_2377])).

tff(c_2402,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1501,c_2387])).

tff(c_2403,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_2402])).

tff(c_2414,plain,(
    ! [A_27] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_27)) = A_27
      | ~ r1_tarski(A_27,'#skF_2')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2403,c_38])).

tff(c_2447,plain,(
    ! [A_352] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_352)) = A_352
      | ~ r1_tarski(A_352,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_2414])).

tff(c_1761,plain,(
    ! [A_306,B_307,C_308,D_309] :
      ( k2_partfun1(A_306,B_307,C_308,D_309) = k7_relat_1(C_308,D_309)
      | ~ m1_subset_1(C_308,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307)))
      | ~ v1_funct_1(C_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1766,plain,(
    ! [D_309] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_309) = k7_relat_1('#skF_5',D_309)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_1761])).

tff(c_1777,plain,(
    ! [D_309] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_309) = k7_relat_1('#skF_5',D_309) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1766])).

tff(c_2226,plain,(
    ! [A_342,B_343,C_344,D_345] :
      ( m1_subset_1(k2_partfun1(A_342,B_343,C_344,D_345),k1_zfmisc_1(k2_zfmisc_1(A_342,B_343)))
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(A_342,B_343)))
      | ~ v1_funct_1(C_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2261,plain,(
    ! [D_309] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_309),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1777,c_2226])).

tff(c_2286,plain,(
    ! [D_346] : m1_subset_1(k7_relat_1('#skF_5',D_346),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_2261])).

tff(c_42,plain,(
    ! [C_34,B_33,A_32] :
      ( v5_relat_1(C_34,B_33)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2334,plain,(
    ! [D_346] : v5_relat_1(k7_relat_1('#skF_5',D_346),'#skF_3') ),
    inference(resolution,[status(thm)],[c_2286,c_42])).

tff(c_36,plain,(
    ! [B_26,A_25] :
      ( r1_tarski(k7_relat_1(B_26,A_25),B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_916,plain,(
    ! [B_184,A_185] :
      ( v1_relat_1(B_184)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(A_185))
      | ~ v1_relat_1(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_932,plain,(
    ! [A_186,B_187] :
      ( v1_relat_1(A_186)
      | ~ v1_relat_1(B_187)
      | ~ r1_tarski(A_186,B_187) ) ),
    inference(resolution,[status(thm)],[c_22,c_916])).

tff(c_950,plain,(
    ! [B_26,A_25] :
      ( v1_relat_1(k7_relat_1(B_26,A_25))
      | ~ v1_relat_1(B_26) ) ),
    inference(resolution,[status(thm)],[c_36,c_932])).

tff(c_48,plain,(
    ! [C_40,A_38,B_39] :
      ( m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ r1_tarski(k2_relat_1(C_40),B_39)
      | ~ r1_tarski(k1_relat_1(C_40),A_38)
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_767,plain,(
    ! [A_162,B_163,C_164,D_165] :
      ( v1_funct_1(k2_partfun1(A_162,B_163,C_164,D_165))
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163)))
      | ~ v1_funct_1(C_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_772,plain,(
    ! [D_165] :
      ( v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5',D_165))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_767])).

tff(c_783,plain,(
    ! [D_165] : v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5',D_165)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_772])).

tff(c_68,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_142,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_142])).

tff(c_805,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_848,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_805])).

tff(c_1783,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1777,c_848])).

tff(c_1855,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_4')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_4')),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_1783])).

tff(c_1872,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1855])).

tff(c_1875,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_950,c_1872])).

tff(c_1879,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_1875])).

tff(c_1881,plain,(
    v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1855])).

tff(c_32,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k2_relat_1(B_22),A_21)
      | ~ v5_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1880,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_4')),'#skF_4')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1855])).

tff(c_1989,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1880])).

tff(c_1995,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_1989])).

tff(c_1999,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1881,c_1995])).

tff(c_2347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2334,c_1999])).

tff(c_2348,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_4')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1880])).

tff(c_2456,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2447,c_2348])).

tff(c_2498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_965,c_2456])).

tff(c_2500,plain,(
    m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_805])).

tff(c_3362,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) = k1_relat_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2500,c_3341])).

tff(c_3804,plain,(
    k1_relset_1('#skF_4','#skF_3',k7_relat_1('#skF_5','#skF_4')) = k1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3799,c_3799,c_3362])).

tff(c_2499,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_805])).

tff(c_3812,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_4'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3799,c_2499])).

tff(c_3811,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3799,c_2500])).

tff(c_56,plain,(
    ! [B_42,C_43,A_41] :
      ( k1_xboole_0 = B_42
      | v1_funct_2(C_43,A_41,B_42)
      | k1_relset_1(A_41,B_42,C_43) != A_41
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3887,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_4'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_3811,c_56])).

tff(c_3916,plain,(
    k1_relset_1('#skF_4','#skF_3',k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3812,c_91,c_3887])).

tff(c_4121,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3804,c_3916])).

tff(c_4128,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4013,c_4121])).

tff(c_4135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4128])).

tff(c_4137,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_4136,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_4144,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4137,c_4136])).

tff(c_4151,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4144,c_72])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4191,plain,(
    ! [A_548] :
      ( A_548 = '#skF_3'
      | ~ r1_tarski(A_548,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4137,c_4137,c_10])).

tff(c_4195,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4151,c_4191])).

tff(c_16,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4158,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_3',B_8) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4137,c_4137,c_16])).

tff(c_4156,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4144,c_74])).

tff(c_4159,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4158,c_4156])).

tff(c_4198,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4195,c_4159])).

tff(c_4943,plain,(
    ! [A_669,B_670] :
      ( r1_tarski(A_669,B_670)
      | ~ m1_subset_1(A_669,k1_zfmisc_1(B_670)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4955,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_4198,c_4943])).

tff(c_4190,plain,(
    ! [A_6] :
      ( A_6 = '#skF_3'
      | ~ r1_tarski(A_6,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4137,c_4137,c_10])).

tff(c_4196,plain,(
    ! [A_6] :
      ( A_6 = '#skF_4'
      | ~ r1_tarski(A_6,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4195,c_4195,c_4190])).

tff(c_4967,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4955,c_4196])).

tff(c_4150,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4144,c_76])).

tff(c_4202,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4195,c_4195,c_4150])).

tff(c_4970,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4967,c_4202])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4139,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4136,c_8])).

tff(c_4149,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4144,c_4139])).

tff(c_4204,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4195,c_4149])).

tff(c_4972,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4967,c_78])).

tff(c_4160,plain,(
    ! [B_545] : k2_zfmisc_1('#skF_3',B_545) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4137,c_4137,c_16])).

tff(c_34,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4164,plain,(
    v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4160,c_34])).

tff(c_4200,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4195,c_4164])).

tff(c_4979,plain,(
    ! [B_672,A_673] :
      ( r1_tarski(k7_relat_1(B_672,A_673),B_672)
      | ~ v1_relat_1(B_672) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4983,plain,(
    ! [A_673] :
      ( k7_relat_1('#skF_4',A_673) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4979,c_4196])).

tff(c_4986,plain,(
    ! [A_673] : k7_relat_1('#skF_4',A_673) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4200,c_4983])).

tff(c_18,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4188,plain,(
    ! [A_9] : m1_subset_1('#skF_3',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4137,c_18])).

tff(c_4197,plain,(
    ! [A_9] : m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4195,c_4188])).

tff(c_6009,plain,(
    ! [A_825,B_826,C_827,D_828] :
      ( k2_partfun1(A_825,B_826,C_827,D_828) = k7_relat_1(C_827,D_828)
      | ~ m1_subset_1(C_827,k1_zfmisc_1(k2_zfmisc_1(A_825,B_826)))
      | ~ v1_funct_1(C_827) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_6019,plain,(
    ! [A_825,B_826,D_828] :
      ( k2_partfun1(A_825,B_826,'#skF_4',D_828) = k7_relat_1('#skF_4',D_828)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4197,c_6009])).

tff(c_6026,plain,(
    ! [A_825,B_826,D_828] : k2_partfun1(A_825,B_826,'#skF_4',D_828) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4972,c_4986,c_6019])).

tff(c_5107,plain,(
    ! [A_696,B_697] :
      ( r2_hidden('#skF_1'(A_696,B_697),A_696)
      | r1_tarski(A_696,B_697) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5112,plain,(
    ! [A_696] : r1_tarski(A_696,A_696) ),
    inference(resolution,[status(thm)],[c_5107,c_4])).

tff(c_5140,plain,(
    ! [C_699,B_700,A_701] :
      ( ~ v1_xboole_0(C_699)
      | ~ m1_subset_1(B_700,k1_zfmisc_1(C_699))
      | ~ r2_hidden(A_701,B_700) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_5155,plain,(
    ! [B_703,A_704,A_705] :
      ( ~ v1_xboole_0(B_703)
      | ~ r2_hidden(A_704,A_705)
      | ~ r1_tarski(A_705,B_703) ) ),
    inference(resolution,[status(thm)],[c_22,c_5140])).

tff(c_5159,plain,(
    ! [B_706,A_707,B_708] :
      ( ~ v1_xboole_0(B_706)
      | ~ r1_tarski(A_707,B_706)
      | r1_tarski(A_707,B_708) ) ),
    inference(resolution,[status(thm)],[c_6,c_5155])).

tff(c_5174,plain,(
    ! [A_712,B_713] :
      ( ~ v1_xboole_0(A_712)
      | r1_tarski(A_712,B_713) ) ),
    inference(resolution,[status(thm)],[c_5112,c_5159])).

tff(c_14,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4138,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4136,c_4136,c_14])).

tff(c_4169,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4144,c_4144,c_4138])).

tff(c_4199,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4195,c_4195,c_4169])).

tff(c_4205,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4195,c_4144])).

tff(c_4260,plain,(
    ! [A_556,B_557] :
      ( r1_tarski(A_556,B_557)
      | ~ m1_subset_1(A_556,k1_zfmisc_1(B_557)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4272,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_4198,c_4260])).

tff(c_4292,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4272,c_4196])).

tff(c_4297,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4292,c_78])).

tff(c_4876,plain,(
    ! [A_658,B_659,C_660,D_661] :
      ( v1_funct_1(k2_partfun1(A_658,B_659,C_660,D_661))
      | ~ m1_subset_1(C_660,k1_zfmisc_1(k2_zfmisc_1(A_658,B_659)))
      | ~ v1_funct_1(C_660) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_4882,plain,(
    ! [A_658,B_659,D_661] :
      ( v1_funct_1(k2_partfun1(A_658,B_659,'#skF_4',D_661))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4197,c_4876])).

tff(c_4890,plain,(
    ! [A_658,B_659,D_661] : v1_funct_1(k2_partfun1(A_658,B_659,'#skF_4',D_661)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4297,c_4882])).

tff(c_4211,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_2','#skF_4','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ v1_funct_2(k2_partfun1('#skF_2','#skF_4','#skF_5','#skF_4'),'#skF_4','#skF_4')
    | ~ v1_funct_1(k2_partfun1('#skF_2','#skF_4','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4195,c_4195,c_4195,c_4195,c_4195,c_68])).

tff(c_4212,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_2','#skF_4','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4211])).

tff(c_4251,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4205,c_4212])).

tff(c_4295,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4292,c_4251])).

tff(c_4893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4890,c_4295])).

tff(c_4894,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_2','#skF_4','#skF_5','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_2','#skF_4','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_4211])).

tff(c_5051,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4967,c_4199,c_4205,c_4967,c_4205,c_4894])).

tff(c_5052,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5051])).

tff(c_5139,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_5052])).

tff(c_5196,plain,(
    ~ v1_xboole_0(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_5174,c_5139])).

tff(c_6028,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6026,c_5196])).

tff(c_6034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4204,c_6028])).

tff(c_6036,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5051])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6133,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_6036,c_20])).

tff(c_6149,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6133,c_4196])).

tff(c_6035,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_5051])).

tff(c_6163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4970,c_6149,c_6035])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:23:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.02/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.02/2.18  
% 6.02/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.02/2.18  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.02/2.18  
% 6.02/2.18  %Foreground sorts:
% 6.02/2.18  
% 6.02/2.18  
% 6.02/2.18  %Background operators:
% 6.02/2.18  
% 6.02/2.18  
% 6.02/2.18  %Foreground operators:
% 6.02/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.02/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.02/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.02/2.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.02/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.02/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.02/2.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.02/2.18  tff('#skF_5', type, '#skF_5': $i).
% 6.02/2.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.02/2.18  tff('#skF_2', type, '#skF_2': $i).
% 6.02/2.18  tff('#skF_3', type, '#skF_3': $i).
% 6.02/2.18  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.02/2.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.02/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.02/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.02/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.02/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.02/2.18  tff('#skF_4', type, '#skF_4': $i).
% 6.02/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.02/2.18  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.02/2.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.02/2.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.02/2.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.02/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.02/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.02/2.18  
% 6.02/2.21  tff(f_161, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 6.02/2.21  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.02/2.21  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.02/2.21  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.02/2.21  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 6.02/2.21  tff(f_141, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.02/2.21  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.02/2.21  tff(f_135, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 6.02/2.21  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.02/2.21  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 6.02/2.21  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.02/2.21  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.02/2.21  tff(f_109, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 6.02/2.21  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.02/2.21  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.02/2.21  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.02/2.21  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.02/2.21  tff(f_77, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.02/2.21  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.02/2.21  tff(f_62, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 6.02/2.21  tff(c_72, plain, (r1_tarski('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.02/2.21  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.02/2.21  tff(c_820, plain, (![C_170, A_171, B_172]: (v1_relat_1(C_170) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.02/2.21  tff(c_837, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_820])).
% 6.02/2.21  tff(c_70, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.02/2.21  tff(c_91, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_70])).
% 6.02/2.21  tff(c_76, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.02/2.21  tff(c_3341, plain, (![A_468, B_469, C_470]: (k1_relset_1(A_468, B_469, C_470)=k1_relat_1(C_470) | ~m1_subset_1(C_470, k1_zfmisc_1(k2_zfmisc_1(A_468, B_469))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.02/2.21  tff(c_3364, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_3341])).
% 6.02/2.21  tff(c_3965, plain, (![B_537, A_538, C_539]: (k1_xboole_0=B_537 | k1_relset_1(A_538, B_537, C_539)=A_538 | ~v1_funct_2(C_539, A_538, B_537) | ~m1_subset_1(C_539, k1_zfmisc_1(k2_zfmisc_1(A_538, B_537))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.02/2.21  tff(c_3978, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_3965])).
% 6.02/2.21  tff(c_3995, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3364, c_3978])).
% 6.02/2.21  tff(c_3996, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_91, c_3995])).
% 6.02/2.21  tff(c_38, plain, (![B_28, A_27]: (k1_relat_1(k7_relat_1(B_28, A_27))=A_27 | ~r1_tarski(A_27, k1_relat_1(B_28)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.02/2.21  tff(c_4007, plain, (![A_27]: (k1_relat_1(k7_relat_1('#skF_5', A_27))=A_27 | ~r1_tarski(A_27, '#skF_2') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3996, c_38])).
% 6.02/2.21  tff(c_4013, plain, (![A_27]: (k1_relat_1(k7_relat_1('#skF_5', A_27))=A_27 | ~r1_tarski(A_27, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_837, c_4007])).
% 6.02/2.21  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.02/2.21  tff(c_3775, plain, (![A_521, B_522, C_523, D_524]: (k2_partfun1(A_521, B_522, C_523, D_524)=k7_relat_1(C_523, D_524) | ~m1_subset_1(C_523, k1_zfmisc_1(k2_zfmisc_1(A_521, B_522))) | ~v1_funct_1(C_523))), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.02/2.21  tff(c_3784, plain, (![D_524]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_524)=k7_relat_1('#skF_5', D_524) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_3775])).
% 6.02/2.21  tff(c_3799, plain, (![D_524]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_524)=k7_relat_1('#skF_5', D_524))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3784])).
% 6.02/2.21  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.02/2.21  tff(c_960, plain, (![A_192, B_193]: (~r2_hidden('#skF_1'(A_192, B_193), B_193) | r1_tarski(A_192, B_193))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.02/2.21  tff(c_965, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_960])).
% 6.02/2.21  tff(c_1482, plain, (![A_268, B_269, C_270]: (k1_relset_1(A_268, B_269, C_270)=k1_relat_1(C_270) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_268, B_269))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.02/2.21  tff(c_1501, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_1482])).
% 6.02/2.21  tff(c_2377, plain, (![B_349, A_350, C_351]: (k1_xboole_0=B_349 | k1_relset_1(A_350, B_349, C_351)=A_350 | ~v1_funct_2(C_351, A_350, B_349) | ~m1_subset_1(C_351, k1_zfmisc_1(k2_zfmisc_1(A_350, B_349))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.02/2.21  tff(c_2387, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_2377])).
% 6.02/2.21  tff(c_2402, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1501, c_2387])).
% 6.02/2.21  tff(c_2403, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_91, c_2402])).
% 6.02/2.21  tff(c_2414, plain, (![A_27]: (k1_relat_1(k7_relat_1('#skF_5', A_27))=A_27 | ~r1_tarski(A_27, '#skF_2') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2403, c_38])).
% 6.02/2.21  tff(c_2447, plain, (![A_352]: (k1_relat_1(k7_relat_1('#skF_5', A_352))=A_352 | ~r1_tarski(A_352, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_837, c_2414])).
% 6.02/2.21  tff(c_1761, plain, (![A_306, B_307, C_308, D_309]: (k2_partfun1(A_306, B_307, C_308, D_309)=k7_relat_1(C_308, D_309) | ~m1_subset_1(C_308, k1_zfmisc_1(k2_zfmisc_1(A_306, B_307))) | ~v1_funct_1(C_308))), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.02/2.21  tff(c_1766, plain, (![D_309]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_309)=k7_relat_1('#skF_5', D_309) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_1761])).
% 6.02/2.21  tff(c_1777, plain, (![D_309]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_309)=k7_relat_1('#skF_5', D_309))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1766])).
% 6.02/2.21  tff(c_2226, plain, (![A_342, B_343, C_344, D_345]: (m1_subset_1(k2_partfun1(A_342, B_343, C_344, D_345), k1_zfmisc_1(k2_zfmisc_1(A_342, B_343))) | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(A_342, B_343))) | ~v1_funct_1(C_344))), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.02/2.21  tff(c_2261, plain, (![D_309]: (m1_subset_1(k7_relat_1('#skF_5', D_309), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1777, c_2226])).
% 6.02/2.21  tff(c_2286, plain, (![D_346]: (m1_subset_1(k7_relat_1('#skF_5', D_346), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_2261])).
% 6.02/2.21  tff(c_42, plain, (![C_34, B_33, A_32]: (v5_relat_1(C_34, B_33) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.02/2.21  tff(c_2334, plain, (![D_346]: (v5_relat_1(k7_relat_1('#skF_5', D_346), '#skF_3'))), inference(resolution, [status(thm)], [c_2286, c_42])).
% 6.02/2.21  tff(c_36, plain, (![B_26, A_25]: (r1_tarski(k7_relat_1(B_26, A_25), B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.02/2.21  tff(c_22, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.02/2.21  tff(c_916, plain, (![B_184, A_185]: (v1_relat_1(B_184) | ~m1_subset_1(B_184, k1_zfmisc_1(A_185)) | ~v1_relat_1(A_185))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.02/2.21  tff(c_932, plain, (![A_186, B_187]: (v1_relat_1(A_186) | ~v1_relat_1(B_187) | ~r1_tarski(A_186, B_187))), inference(resolution, [status(thm)], [c_22, c_916])).
% 6.02/2.21  tff(c_950, plain, (![B_26, A_25]: (v1_relat_1(k7_relat_1(B_26, A_25)) | ~v1_relat_1(B_26))), inference(resolution, [status(thm)], [c_36, c_932])).
% 6.02/2.21  tff(c_48, plain, (![C_40, A_38, B_39]: (m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~r1_tarski(k2_relat_1(C_40), B_39) | ~r1_tarski(k1_relat_1(C_40), A_38) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.02/2.21  tff(c_767, plain, (![A_162, B_163, C_164, D_165]: (v1_funct_1(k2_partfun1(A_162, B_163, C_164, D_165)) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))) | ~v1_funct_1(C_164))), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.02/2.21  tff(c_772, plain, (![D_165]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_165)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_767])).
% 6.02/2.21  tff(c_783, plain, (![D_165]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_165)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_772])).
% 6.02/2.21  tff(c_68, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.02/2.21  tff(c_142, plain, (~v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_68])).
% 6.02/2.21  tff(c_804, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_783, c_142])).
% 6.02/2.21  tff(c_805, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_68])).
% 6.02/2.21  tff(c_848, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_805])).
% 6.02/2.21  tff(c_1783, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1777, c_848])).
% 6.02/2.21  tff(c_1855, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_4')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_4')), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_1783])).
% 6.02/2.21  tff(c_1872, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1855])).
% 6.02/2.21  tff(c_1875, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_950, c_1872])).
% 6.02/2.21  tff(c_1879, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_837, c_1875])).
% 6.02/2.21  tff(c_1881, plain, (v1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_1855])).
% 6.02/2.21  tff(c_32, plain, (![B_22, A_21]: (r1_tarski(k2_relat_1(B_22), A_21) | ~v5_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.02/2.21  tff(c_1880, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_4')), '#skF_4') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_4')), '#skF_3')), inference(splitRight, [status(thm)], [c_1855])).
% 6.02/2.21  tff(c_1989, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_1880])).
% 6.02/2.21  tff(c_1995, plain, (~v5_relat_1(k7_relat_1('#skF_5', '#skF_4'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_1989])).
% 6.02/2.21  tff(c_1999, plain, (~v5_relat_1(k7_relat_1('#skF_5', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1881, c_1995])).
% 6.02/2.21  tff(c_2347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2334, c_1999])).
% 6.02/2.21  tff(c_2348, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_4')), '#skF_4')), inference(splitRight, [status(thm)], [c_1880])).
% 6.02/2.21  tff(c_2456, plain, (~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2447, c_2348])).
% 6.02/2.21  tff(c_2498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_965, c_2456])).
% 6.02/2.21  tff(c_2500, plain, (m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_805])).
% 6.02/2.21  tff(c_3362, plain, (k1_relset_1('#skF_4', '#skF_3', k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))=k1_relat_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_2500, c_3341])).
% 6.02/2.21  tff(c_3804, plain, (k1_relset_1('#skF_4', '#skF_3', k7_relat_1('#skF_5', '#skF_4'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3799, c_3799, c_3362])).
% 6.02/2.21  tff(c_2499, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_805])).
% 6.02/2.21  tff(c_3812, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_4'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3799, c_2499])).
% 6.02/2.21  tff(c_3811, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3799, c_2500])).
% 6.02/2.21  tff(c_56, plain, (![B_42, C_43, A_41]: (k1_xboole_0=B_42 | v1_funct_2(C_43, A_41, B_42) | k1_relset_1(A_41, B_42, C_43)!=A_41 | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.02/2.21  tff(c_3887, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_4'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(resolution, [status(thm)], [c_3811, c_56])).
% 6.02/2.21  tff(c_3916, plain, (k1_relset_1('#skF_4', '#skF_3', k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3812, c_91, c_3887])).
% 6.02/2.21  tff(c_4121, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3804, c_3916])).
% 6.02/2.21  tff(c_4128, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4013, c_4121])).
% 6.02/2.21  tff(c_4135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_4128])).
% 6.02/2.21  tff(c_4137, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_70])).
% 6.02/2.21  tff(c_4136, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_70])).
% 6.02/2.21  tff(c_4144, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4137, c_4136])).
% 6.02/2.21  tff(c_4151, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4144, c_72])).
% 6.02/2.21  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.02/2.21  tff(c_4191, plain, (![A_548]: (A_548='#skF_3' | ~r1_tarski(A_548, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4137, c_4137, c_10])).
% 6.02/2.21  tff(c_4195, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_4151, c_4191])).
% 6.02/2.21  tff(c_16, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.02/2.21  tff(c_4158, plain, (![B_8]: (k2_zfmisc_1('#skF_3', B_8)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4137, c_4137, c_16])).
% 6.02/2.21  tff(c_4156, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4144, c_74])).
% 6.02/2.21  tff(c_4159, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4158, c_4156])).
% 6.02/2.21  tff(c_4198, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4195, c_4159])).
% 6.02/2.21  tff(c_4943, plain, (![A_669, B_670]: (r1_tarski(A_669, B_670) | ~m1_subset_1(A_669, k1_zfmisc_1(B_670)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.02/2.21  tff(c_4955, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_4198, c_4943])).
% 6.02/2.21  tff(c_4190, plain, (![A_6]: (A_6='#skF_3' | ~r1_tarski(A_6, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4137, c_4137, c_10])).
% 6.02/2.21  tff(c_4196, plain, (![A_6]: (A_6='#skF_4' | ~r1_tarski(A_6, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4195, c_4195, c_4190])).
% 6.02/2.21  tff(c_4967, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_4955, c_4196])).
% 6.02/2.21  tff(c_4150, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4144, c_76])).
% 6.02/2.21  tff(c_4202, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4195, c_4195, c_4150])).
% 6.02/2.21  tff(c_4970, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4967, c_4202])).
% 6.02/2.21  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.02/2.21  tff(c_4139, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4136, c_8])).
% 6.02/2.21  tff(c_4149, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4144, c_4139])).
% 6.02/2.21  tff(c_4204, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4195, c_4149])).
% 6.02/2.21  tff(c_4972, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4967, c_78])).
% 6.02/2.21  tff(c_4160, plain, (![B_545]: (k2_zfmisc_1('#skF_3', B_545)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4137, c_4137, c_16])).
% 6.02/2.21  tff(c_34, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.02/2.21  tff(c_4164, plain, (v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4160, c_34])).
% 6.02/2.21  tff(c_4200, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4195, c_4164])).
% 6.02/2.21  tff(c_4979, plain, (![B_672, A_673]: (r1_tarski(k7_relat_1(B_672, A_673), B_672) | ~v1_relat_1(B_672))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.02/2.21  tff(c_4983, plain, (![A_673]: (k7_relat_1('#skF_4', A_673)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4979, c_4196])).
% 6.02/2.21  tff(c_4986, plain, (![A_673]: (k7_relat_1('#skF_4', A_673)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4200, c_4983])).
% 6.02/2.21  tff(c_18, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.02/2.21  tff(c_4188, plain, (![A_9]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_4137, c_18])).
% 6.02/2.21  tff(c_4197, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_4195, c_4188])).
% 6.02/2.21  tff(c_6009, plain, (![A_825, B_826, C_827, D_828]: (k2_partfun1(A_825, B_826, C_827, D_828)=k7_relat_1(C_827, D_828) | ~m1_subset_1(C_827, k1_zfmisc_1(k2_zfmisc_1(A_825, B_826))) | ~v1_funct_1(C_827))), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.02/2.21  tff(c_6019, plain, (![A_825, B_826, D_828]: (k2_partfun1(A_825, B_826, '#skF_4', D_828)=k7_relat_1('#skF_4', D_828) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4197, c_6009])).
% 6.02/2.21  tff(c_6026, plain, (![A_825, B_826, D_828]: (k2_partfun1(A_825, B_826, '#skF_4', D_828)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4972, c_4986, c_6019])).
% 6.02/2.21  tff(c_5107, plain, (![A_696, B_697]: (r2_hidden('#skF_1'(A_696, B_697), A_696) | r1_tarski(A_696, B_697))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.02/2.21  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.02/2.21  tff(c_5112, plain, (![A_696]: (r1_tarski(A_696, A_696))), inference(resolution, [status(thm)], [c_5107, c_4])).
% 6.02/2.21  tff(c_5140, plain, (![C_699, B_700, A_701]: (~v1_xboole_0(C_699) | ~m1_subset_1(B_700, k1_zfmisc_1(C_699)) | ~r2_hidden(A_701, B_700))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.02/2.21  tff(c_5155, plain, (![B_703, A_704, A_705]: (~v1_xboole_0(B_703) | ~r2_hidden(A_704, A_705) | ~r1_tarski(A_705, B_703))), inference(resolution, [status(thm)], [c_22, c_5140])).
% 6.02/2.21  tff(c_5159, plain, (![B_706, A_707, B_708]: (~v1_xboole_0(B_706) | ~r1_tarski(A_707, B_706) | r1_tarski(A_707, B_708))), inference(resolution, [status(thm)], [c_6, c_5155])).
% 6.02/2.21  tff(c_5174, plain, (![A_712, B_713]: (~v1_xboole_0(A_712) | r1_tarski(A_712, B_713))), inference(resolution, [status(thm)], [c_5112, c_5159])).
% 6.02/2.21  tff(c_14, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.02/2.21  tff(c_4138, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4136, c_4136, c_14])).
% 6.02/2.21  tff(c_4169, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4144, c_4144, c_4138])).
% 6.02/2.21  tff(c_4199, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4195, c_4195, c_4169])).
% 6.02/2.21  tff(c_4205, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4195, c_4144])).
% 6.02/2.21  tff(c_4260, plain, (![A_556, B_557]: (r1_tarski(A_556, B_557) | ~m1_subset_1(A_556, k1_zfmisc_1(B_557)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.02/2.21  tff(c_4272, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_4198, c_4260])).
% 6.02/2.21  tff(c_4292, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_4272, c_4196])).
% 6.02/2.21  tff(c_4297, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4292, c_78])).
% 6.02/2.21  tff(c_4876, plain, (![A_658, B_659, C_660, D_661]: (v1_funct_1(k2_partfun1(A_658, B_659, C_660, D_661)) | ~m1_subset_1(C_660, k1_zfmisc_1(k2_zfmisc_1(A_658, B_659))) | ~v1_funct_1(C_660))), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.02/2.21  tff(c_4882, plain, (![A_658, B_659, D_661]: (v1_funct_1(k2_partfun1(A_658, B_659, '#skF_4', D_661)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4197, c_4876])).
% 6.02/2.21  tff(c_4890, plain, (![A_658, B_659, D_661]: (v1_funct_1(k2_partfun1(A_658, B_659, '#skF_4', D_661)))), inference(demodulation, [status(thm), theory('equality')], [c_4297, c_4882])).
% 6.02/2.21  tff(c_4211, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_4', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_2(k2_partfun1('#skF_2', '#skF_4', '#skF_5', '#skF_4'), '#skF_4', '#skF_4') | ~v1_funct_1(k2_partfun1('#skF_2', '#skF_4', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4195, c_4195, c_4195, c_4195, c_4195, c_68])).
% 6.02/2.21  tff(c_4212, plain, (~v1_funct_1(k2_partfun1('#skF_2', '#skF_4', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_4211])).
% 6.02/2.21  tff(c_4251, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4205, c_4212])).
% 6.02/2.21  tff(c_4295, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4292, c_4251])).
% 6.02/2.21  tff(c_4893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4890, c_4295])).
% 6.02/2.21  tff(c_4894, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_4', '#skF_5', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_2', '#skF_4', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(splitRight, [status(thm)], [c_4211])).
% 6.02/2.21  tff(c_5051, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4967, c_4199, c_4205, c_4967, c_4205, c_4894])).
% 6.02/2.21  tff(c_5052, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5051])).
% 6.02/2.21  tff(c_5139, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_22, c_5052])).
% 6.02/2.21  tff(c_5196, plain, (~v1_xboole_0(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_5174, c_5139])).
% 6.02/2.21  tff(c_6028, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6026, c_5196])).
% 6.02/2.21  tff(c_6034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4204, c_6028])).
% 6.02/2.21  tff(c_6036, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5051])).
% 6.02/2.21  tff(c_20, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.02/2.21  tff(c_6133, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_6036, c_20])).
% 6.02/2.21  tff(c_6149, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_6133, c_4196])).
% 6.02/2.21  tff(c_6035, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_5051])).
% 6.02/2.21  tff(c_6163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4970, c_6149, c_6035])).
% 6.02/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.02/2.21  
% 6.02/2.21  Inference rules
% 6.02/2.21  ----------------------
% 6.02/2.21  #Ref     : 0
% 6.02/2.21  #Sup     : 1262
% 6.02/2.21  #Fact    : 0
% 6.02/2.21  #Define  : 0
% 6.02/2.21  #Split   : 29
% 6.02/2.21  #Chain   : 0
% 6.02/2.21  #Close   : 0
% 6.02/2.21  
% 6.02/2.21  Ordering : KBO
% 6.02/2.21  
% 6.02/2.21  Simplification rules
% 6.02/2.21  ----------------------
% 6.02/2.21  #Subsume      : 214
% 6.02/2.21  #Demod        : 937
% 6.02/2.21  #Tautology    : 578
% 6.02/2.21  #SimpNegUnit  : 58
% 6.02/2.21  #BackRed      : 87
% 6.02/2.21  
% 6.02/2.21  #Partial instantiations: 0
% 6.02/2.21  #Strategies tried      : 1
% 6.02/2.21  
% 6.02/2.21  Timing (in seconds)
% 6.02/2.21  ----------------------
% 6.02/2.21  Preprocessing        : 0.34
% 6.02/2.21  Parsing              : 0.18
% 6.02/2.21  CNF conversion       : 0.02
% 6.02/2.21  Main loop            : 1.07
% 6.02/2.21  Inferencing          : 0.40
% 6.02/2.21  Reduction            : 0.35
% 6.02/2.21  Demodulation         : 0.24
% 6.02/2.21  BG Simplification    : 0.04
% 6.02/2.21  Subsumption          : 0.18
% 6.02/2.21  Abstraction          : 0.05
% 6.02/2.21  MUC search           : 0.00
% 6.02/2.21  Cooper               : 0.00
% 6.02/2.21  Total                : 1.47
% 6.02/2.21  Index Insertion      : 0.00
% 6.02/2.21  Index Deletion       : 0.00
% 6.02/2.21  Index Matching       : 0.00
% 6.02/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
