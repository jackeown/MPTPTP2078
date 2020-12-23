%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:34 EST 2020

% Result     : Theorem 9.63s
% Output     : CNFRefutation 9.63s
% Verified   : 
% Statistics : Number of formulae       :  215 (3056 expanded)
%              Number of leaves         :   39 ( 894 expanded)
%              Depth                    :   15
%              Number of atoms          :  353 (9323 expanded)
%              Number of equality atoms :   93 (3504 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
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

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_102,axiom,(
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

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_128,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(c_72,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1002,plain,(
    ! [C_179,A_180,B_181] :
      ( v1_relat_1(C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1015,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_1002])).

tff(c_70,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_76,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_10212,plain,(
    ! [A_924,B_925,C_926] :
      ( k1_relset_1(A_924,B_925,C_926) = k1_relat_1(C_926)
      | ~ m1_subset_1(C_926,k1_zfmisc_1(k2_zfmisc_1(A_924,B_925))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10231,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_10212])).

tff(c_10822,plain,(
    ! [B_1000,A_1001,C_1002] :
      ( k1_xboole_0 = B_1000
      | k1_relset_1(A_1001,B_1000,C_1002) = A_1001
      | ~ v1_funct_2(C_1002,A_1001,B_1000)
      | ~ m1_subset_1(C_1002,k1_zfmisc_1(k2_zfmisc_1(A_1001,B_1000))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_10835,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_10822])).

tff(c_10848,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_10231,c_10835])).

tff(c_10849,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_10848])).

tff(c_34,plain,(
    ! [B_20,A_19] :
      ( k1_relat_1(k7_relat_1(B_20,A_19)) = A_19
      | ~ r1_tarski(A_19,k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10864,plain,(
    ! [A_19] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_19)) = A_19
      | ~ r1_tarski(A_19,'#skF_2')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10849,c_34])).

tff(c_10874,plain,(
    ! [A_19] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_19)) = A_19
      | ~ r1_tarski(A_19,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1015,c_10864])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_10724,plain,(
    ! [A_994,B_995,C_996,D_997] :
      ( k2_partfun1(A_994,B_995,C_996,D_997) = k7_relat_1(C_996,D_997)
      | ~ m1_subset_1(C_996,k1_zfmisc_1(k2_zfmisc_1(A_994,B_995)))
      | ~ v1_funct_1(C_996) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_10733,plain,(
    ! [D_997] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_997) = k7_relat_1('#skF_5',D_997)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_10724])).

tff(c_10745,plain,(
    ! [D_997] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_997) = k7_relat_1('#skF_5',D_997) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_10733])).

tff(c_4675,plain,(
    ! [A_505,B_506,C_507,D_508] :
      ( k2_partfun1(A_505,B_506,C_507,D_508) = k7_relat_1(C_507,D_508)
      | ~ m1_subset_1(C_507,k1_zfmisc_1(k2_zfmisc_1(A_505,B_506)))
      | ~ v1_funct_1(C_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_4682,plain,(
    ! [D_508] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_508) = k7_relat_1('#skF_5',D_508)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_4675])).

tff(c_4691,plain,(
    ! [D_508] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_508) = k7_relat_1('#skF_5',D_508) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4682])).

tff(c_4913,plain,(
    ! [A_529,B_530,C_531,D_532] :
      ( m1_subset_1(k2_partfun1(A_529,B_530,C_531,D_532),k1_zfmisc_1(k2_zfmisc_1(A_529,B_530)))
      | ~ m1_subset_1(C_531,k1_zfmisc_1(k2_zfmisc_1(A_529,B_530)))
      | ~ v1_funct_1(C_531) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4941,plain,(
    ! [D_508] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_508),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4691,c_4913])).

tff(c_4966,plain,(
    ! [D_534] : m1_subset_1(k7_relat_1('#skF_5',D_534),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_4941])).

tff(c_36,plain,(
    ! [C_23,A_21,B_22] :
      ( v1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5007,plain,(
    ! [D_534] : v1_relat_1(k7_relat_1('#skF_5',D_534)) ),
    inference(resolution,[status(thm)],[c_4966,c_36])).

tff(c_38,plain,(
    ! [C_26,B_25,A_24] :
      ( v5_relat_1(C_26,B_25)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5006,plain,(
    ! [D_534] : v5_relat_1(k7_relat_1('#skF_5',D_534),'#skF_3') ),
    inference(resolution,[status(thm)],[c_4966,c_38])).

tff(c_28,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4447,plain,(
    ! [A_481,B_482,C_483,D_484] :
      ( v1_funct_1(k2_partfun1(A_481,B_482,C_483,D_484))
      | ~ m1_subset_1(C_483,k1_zfmisc_1(k2_zfmisc_1(A_481,B_482)))
      | ~ v1_funct_1(C_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4452,plain,(
    ! [D_484] :
      ( v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5',D_484))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_4447])).

tff(c_4460,plain,(
    ! [D_484] : v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5',D_484)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4452])).

tff(c_4692,plain,(
    ! [D_484] : v1_funct_1(k7_relat_1('#skF_5',D_484)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4691,c_4460])).

tff(c_1571,plain,(
    ! [A_256,B_257,C_258] :
      ( k1_relset_1(A_256,B_257,C_258) = k1_relat_1(C_258)
      | ~ m1_subset_1(C_258,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1586,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_1571])).

tff(c_4826,plain,(
    ! [B_525,A_526,C_527] :
      ( k1_xboole_0 = B_525
      | k1_relset_1(A_526,B_525,C_527) = A_526
      | ~ v1_funct_2(C_527,A_526,B_525)
      | ~ m1_subset_1(C_527,k1_zfmisc_1(k2_zfmisc_1(A_526,B_525))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4836,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_4826])).

tff(c_4847,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1586,c_4836])).

tff(c_4848,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4847])).

tff(c_4863,plain,(
    ! [A_19] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_19)) = A_19
      | ~ r1_tarski(A_19,'#skF_2')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4848,c_34])).

tff(c_5036,plain,(
    ! [A_540] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_540)) = A_540
      | ~ r1_tarski(A_540,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1015,c_4863])).

tff(c_62,plain,(
    ! [B_42,A_41] :
      ( m1_subset_1(B_42,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_42),A_41)))
      | ~ r1_tarski(k2_relat_1(B_42),A_41)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_5045,plain,(
    ! [A_540,A_41] :
      ( m1_subset_1(k7_relat_1('#skF_5',A_540),k1_zfmisc_1(k2_zfmisc_1(A_540,A_41)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5',A_540)),A_41)
      | ~ v1_funct_1(k7_relat_1('#skF_5',A_540))
      | ~ v1_relat_1(k7_relat_1('#skF_5',A_540))
      | ~ r1_tarski(A_540,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5036,c_62])).

tff(c_9555,plain,(
    ! [A_847,A_848] :
      ( m1_subset_1(k7_relat_1('#skF_5',A_847),k1_zfmisc_1(k2_zfmisc_1(A_847,A_848)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5',A_847)),A_848)
      | ~ r1_tarski(A_847,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5007,c_4692,c_5045])).

tff(c_915,plain,(
    ! [A_163,B_164,C_165,D_166] :
      ( v1_funct_1(k2_partfun1(A_163,B_164,C_165,D_166))
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164)))
      | ~ v1_funct_1(C_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_920,plain,(
    ! [D_166] :
      ( v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5',D_166))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_915])).

tff(c_928,plain,(
    ! [D_166] : v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5',D_166)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_920])).

tff(c_68,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_170,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_170])).

tff(c_932,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1042,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_932])).

tff(c_4694,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4691,c_1042])).

tff(c_9570,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_4')),'#skF_3')
    | ~ r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_9555,c_4694])).

tff(c_9612,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_9570])).

tff(c_9631,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_28,c_9612])).

tff(c_9635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5007,c_5006,c_9631])).

tff(c_9637,plain,(
    m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_932])).

tff(c_10229,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) = k1_relat_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_9637,c_10212])).

tff(c_10748,plain,(
    k1_relset_1('#skF_4','#skF_3',k7_relat_1('#skF_5','#skF_4')) = k1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10745,c_10745,c_10229])).

tff(c_9636,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_932])).

tff(c_10755,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_4'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10745,c_9636])).

tff(c_10754,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10745,c_9637])).

tff(c_10984,plain,(
    ! [B_1007,C_1008,A_1009] :
      ( k1_xboole_0 = B_1007
      | v1_funct_2(C_1008,A_1009,B_1007)
      | k1_relset_1(A_1009,B_1007,C_1008) != A_1009
      | ~ m1_subset_1(C_1008,k1_zfmisc_1(k2_zfmisc_1(A_1009,B_1007))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_10987,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_4'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_10754,c_10984])).

tff(c_11006,plain,(
    k1_relset_1('#skF_4','#skF_3',k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_10755,c_86,c_10987])).

tff(c_11014,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10748,c_11006])).

tff(c_11021,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10874,c_11014])).

tff(c_11025,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_11021])).

tff(c_11027,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_11026,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_11033,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11027,c_11026])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_11028,plain,(
    ! [A_8] : r1_tarski('#skF_2',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11026,c_14])).

tff(c_11045,plain,(
    ! [A_8] : r1_tarski('#skF_3',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11033,c_11028])).

tff(c_11040,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11033,c_72])).

tff(c_15654,plain,(
    ! [B_1556,A_1557] :
      ( B_1556 = A_1557
      | ~ r1_tarski(B_1556,A_1557)
      | ~ r1_tarski(A_1557,B_1556) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_15660,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_11040,c_15654])).

tff(c_15671,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11045,c_15660])).

tff(c_20,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_11055,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_3',B_10) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11027,c_11027,c_20])).

tff(c_11038,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11033,c_74])).

tff(c_12597,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11055,c_11038])).

tff(c_15644,plain,(
    ! [A_1552,B_1553] :
      ( r1_tarski(A_1552,B_1553)
      | ~ m1_subset_1(A_1552,k1_zfmisc_1(B_1553)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_15652,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_12597,c_15644])).

tff(c_15658,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_15652,c_15654])).

tff(c_15668,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11045,c_15658])).

tff(c_15700,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15671,c_15668])).

tff(c_11039,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11033,c_76])).

tff(c_15682,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15671,c_15671,c_11039])).

tff(c_15701,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15700,c_15682])).

tff(c_12610,plain,(
    ! [B_1214,A_1215] :
      ( B_1214 = A_1215
      | ~ r1_tarski(B_1214,A_1215)
      | ~ r1_tarski(A_1215,B_1214) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12616,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_11040,c_12610])).

tff(c_12627,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11045,c_12616])).

tff(c_12600,plain,(
    ! [A_1210,B_1211] :
      ( r1_tarski(A_1210,B_1211)
      | ~ m1_subset_1(A_1210,k1_zfmisc_1(B_1211)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12608,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_12597,c_12600])).

tff(c_12614,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_12608,c_12610])).

tff(c_12624,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11045,c_12614])).

tff(c_12657,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12627,c_12624])).

tff(c_12636,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12627,c_12597])).

tff(c_12683,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12657,c_12636])).

tff(c_12637,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_4',B_10) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12627,c_12627,c_11055])).

tff(c_12912,plain,(
    ! [C_1256,B_1257,A_1258] :
      ( v5_relat_1(C_1256,B_1257)
      | ~ m1_subset_1(C_1256,k1_zfmisc_1(k2_zfmisc_1(A_1258,B_1257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12955,plain,(
    ! [C_1266,B_1267] :
      ( v5_relat_1(C_1266,B_1267)
      | ~ m1_subset_1(C_1266,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12637,c_12912])).

tff(c_12961,plain,(
    ! [B_1267] : v5_relat_1('#skF_4',B_1267) ),
    inference(resolution,[status(thm)],[c_12683,c_12955])).

tff(c_12659,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12657,c_78])).

tff(c_32,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k7_relat_1(B_18,A_17),B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12628,plain,(
    ! [A_8] :
      ( A_8 = '#skF_3'
      | ~ r1_tarski(A_8,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_11045,c_12610])).

tff(c_12706,plain,(
    ! [A_1223] :
      ( A_1223 = '#skF_4'
      | ~ r1_tarski(A_1223,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12627,c_12627,c_12628])).

tff(c_12721,plain,(
    ! [A_17] :
      ( k7_relat_1('#skF_4',A_17) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_12706])).

tff(c_12724,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_12721])).

tff(c_18,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_11047,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11027,c_11027,c_18])).

tff(c_12638,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12627,c_12627,c_11047])).

tff(c_12737,plain,(
    ! [C_1226,A_1227,B_1228] :
      ( v1_relat_1(C_1226)
      | ~ m1_subset_1(C_1226,k1_zfmisc_1(k2_zfmisc_1(A_1227,B_1228))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12747,plain,(
    ! [C_1229] :
      ( v1_relat_1(C_1229)
      | ~ m1_subset_1(C_1229,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12638,c_12737])).

tff(c_12750,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12683,c_12747])).

tff(c_12758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12724,c_12750])).

tff(c_12759,plain,(
    ! [A_17] : k7_relat_1('#skF_4',A_17) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_12721])).

tff(c_13722,plain,(
    ! [A_1360,B_1361,C_1362,D_1363] :
      ( k2_partfun1(A_1360,B_1361,C_1362,D_1363) = k7_relat_1(C_1362,D_1363)
      | ~ m1_subset_1(C_1362,k1_zfmisc_1(k2_zfmisc_1(A_1360,B_1361)))
      | ~ v1_funct_1(C_1362) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_15622,plain,(
    ! [B_1547,C_1548,D_1549] :
      ( k2_partfun1('#skF_4',B_1547,C_1548,D_1549) = k7_relat_1(C_1548,D_1549)
      | ~ m1_subset_1(C_1548,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_1548) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12637,c_13722])).

tff(c_15626,plain,(
    ! [B_1547,D_1549] :
      ( k2_partfun1('#skF_4',B_1547,'#skF_4',D_1549) = k7_relat_1('#skF_4',D_1549)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12683,c_15622])).

tff(c_15633,plain,(
    ! [B_1547,D_1549] : k2_partfun1('#skF_4',B_1547,'#skF_4',D_1549) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12659,c_12759,c_15626])).

tff(c_14082,plain,(
    ! [A_1396,B_1397,C_1398,D_1399] :
      ( m1_subset_1(k2_partfun1(A_1396,B_1397,C_1398,D_1399),k1_zfmisc_1(k2_zfmisc_1(A_1396,B_1397)))
      | ~ m1_subset_1(C_1398,k1_zfmisc_1(k2_zfmisc_1(A_1396,B_1397)))
      | ~ v1_funct_1(C_1398) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_14756,plain,(
    ! [A_1451,B_1452,C_1453,D_1454] :
      ( v1_relat_1(k2_partfun1(A_1451,B_1452,C_1453,D_1454))
      | ~ m1_subset_1(C_1453,k1_zfmisc_1(k2_zfmisc_1(A_1451,B_1452)))
      | ~ v1_funct_1(C_1453) ) ),
    inference(resolution,[status(thm)],[c_14082,c_36])).

tff(c_14771,plain,(
    ! [A_1455,C_1456,D_1457] :
      ( v1_relat_1(k2_partfun1(A_1455,'#skF_4',C_1456,D_1457))
      | ~ m1_subset_1(C_1456,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_1456) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12638,c_14756])).

tff(c_14775,plain,(
    ! [A_1455,D_1457] :
      ( v1_relat_1(k2_partfun1(A_1455,'#skF_4','#skF_4',D_1457))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12683,c_14771])).

tff(c_14782,plain,(
    ! [A_1455,D_1457] : v1_relat_1(k2_partfun1(A_1455,'#skF_4','#skF_4',D_1457)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12659,c_14775])).

tff(c_11094,plain,(
    ! [B_1025,A_1026] :
      ( B_1025 = A_1026
      | ~ r1_tarski(B_1025,A_1026)
      | ~ r1_tarski(A_1026,B_1025) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11100,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_11040,c_11094])).

tff(c_11111,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11045,c_11100])).

tff(c_11074,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11047,c_11038])).

tff(c_11077,plain,(
    ! [A_1019,B_1020] :
      ( r1_tarski(A_1019,B_1020)
      | ~ m1_subset_1(A_1019,k1_zfmisc_1(B_1020)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_11085,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_11074,c_11077])).

tff(c_11096,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_11085,c_11094])).

tff(c_11107,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11045,c_11096])).

tff(c_11140,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11111,c_11107])).

tff(c_11141,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11140,c_78])).

tff(c_11124,plain,(
    ! [A_8] : r1_tarski('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11111,c_11045])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_11821,plain,(
    ! [A_1120,B_1121,C_1122,D_1123] :
      ( v1_funct_1(k2_partfun1(A_1120,B_1121,C_1122,D_1123))
      | ~ m1_subset_1(C_1122,k1_zfmisc_1(k2_zfmisc_1(A_1120,B_1121)))
      | ~ v1_funct_1(C_1122) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_12567,plain,(
    ! [A_1204,B_1205,A_1206,D_1207] :
      ( v1_funct_1(k2_partfun1(A_1204,B_1205,A_1206,D_1207))
      | ~ v1_funct_1(A_1206)
      | ~ r1_tarski(A_1206,k2_zfmisc_1(A_1204,B_1205)) ) ),
    inference(resolution,[status(thm)],[c_24,c_11821])).

tff(c_12577,plain,(
    ! [A_1204,B_1205,D_1207] :
      ( v1_funct_1(k2_partfun1(A_1204,B_1205,'#skF_4',D_1207))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_11124,c_12567])).

tff(c_12587,plain,(
    ! [A_1204,B_1205,D_1207] : v1_funct_1(k2_partfun1(A_1204,B_1205,'#skF_4',D_1207)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11141,c_12577])).

tff(c_11072,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ v1_funct_2(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11033,c_11033,c_11047,c_11033,c_68])).

tff(c_11073,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_11072])).

tff(c_11118,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11111,c_11111,c_11073])).

tff(c_11209,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11140,c_11118])).

tff(c_12594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12587,c_11209])).

tff(c_12596,plain,(
    v1_funct_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_11072])).

tff(c_12635,plain,(
    v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12627,c_12627,c_12596])).

tff(c_12704,plain,(
    v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12657,c_12635])).

tff(c_13622,plain,(
    ! [B_1353,A_1354] :
      ( m1_subset_1(B_1353,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1353),A_1354)))
      | ~ r1_tarski(k2_relat_1(B_1353),A_1354)
      | ~ v1_funct_1(B_1353)
      | ~ v1_relat_1(B_1353) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_13904,plain,(
    ! [B_1389] :
      ( m1_subset_1(B_1389,k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1(B_1389),'#skF_4')
      | ~ v1_funct_1(B_1389)
      | ~ v1_relat_1(B_1389) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12638,c_13622])).

tff(c_13915,plain,(
    ! [B_1390] :
      ( m1_subset_1(B_1390,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(B_1390)
      | ~ v5_relat_1(B_1390,'#skF_4')
      | ~ v1_relat_1(B_1390) ) ),
    inference(resolution,[status(thm)],[c_28,c_13904])).

tff(c_12595,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_11072])).

tff(c_12598,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_12595])).

tff(c_12778,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12627,c_12627,c_12627,c_12657,c_12598])).

tff(c_13931,plain,
    ( ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'))
    | ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_13915,c_12778])).

tff(c_13943,plain,
    ( ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12704,c_13931])).

tff(c_14141,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_13943])).

tff(c_14786,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14782,c_14141])).

tff(c_14787,plain,(
    ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_13943])).

tff(c_15635,plain,(
    ~ v5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15633,c_14787])).

tff(c_15640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12961,c_15635])).

tff(c_15642,plain,(
    m1_subset_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_12595])).

tff(c_15719,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15700,c_15671,c_15671,c_15671,c_15642])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_15723,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_15719,c_22])).

tff(c_15672,plain,(
    ! [A_8] :
      ( A_8 = '#skF_3'
      | ~ r1_tarski(A_8,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_11045,c_15654])).

tff(c_15746,plain,(
    ! [A_8] :
      ( A_8 = '#skF_4'
      | ~ r1_tarski(A_8,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15671,c_15671,c_15672])).

tff(c_15771,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_15723,c_15746])).

tff(c_15641,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_12595])).

tff(c_15798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15701,c_15771,c_15700,c_15671,c_15671,c_15671,c_15641])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:23:05 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.63/3.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.63/3.42  
% 9.63/3.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.63/3.42  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 9.63/3.42  
% 9.63/3.42  %Foreground sorts:
% 9.63/3.42  
% 9.63/3.42  
% 9.63/3.42  %Background operators:
% 9.63/3.42  
% 9.63/3.42  
% 9.63/3.42  %Foreground operators:
% 9.63/3.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.63/3.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.63/3.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.63/3.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.63/3.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.63/3.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.63/3.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.63/3.42  tff('#skF_5', type, '#skF_5': $i).
% 9.63/3.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.63/3.42  tff('#skF_2', type, '#skF_2': $i).
% 9.63/3.42  tff('#skF_3', type, '#skF_3': $i).
% 9.63/3.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.63/3.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.63/3.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.63/3.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.63/3.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.63/3.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.63/3.42  tff('#skF_4', type, '#skF_4': $i).
% 9.63/3.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.63/3.42  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.63/3.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.63/3.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.63/3.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.63/3.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.63/3.42  
% 9.63/3.45  tff(f_148, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 9.63/3.45  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.63/3.45  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.63/3.45  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.63/3.45  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 9.63/3.45  tff(f_116, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.63/3.45  tff(f_110, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 9.63/3.45  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.63/3.45  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 9.63/3.45  tff(f_128, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 9.63/3.45  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.63/3.45  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.63/3.45  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.63/3.45  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.63/3.45  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 9.63/3.45  tff(c_72, plain, (r1_tarski('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.63/3.45  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.63/3.45  tff(c_1002, plain, (![C_179, A_180, B_181]: (v1_relat_1(C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.63/3.45  tff(c_1015, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_1002])).
% 9.63/3.45  tff(c_70, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.63/3.45  tff(c_86, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_70])).
% 9.63/3.45  tff(c_76, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.63/3.45  tff(c_10212, plain, (![A_924, B_925, C_926]: (k1_relset_1(A_924, B_925, C_926)=k1_relat_1(C_926) | ~m1_subset_1(C_926, k1_zfmisc_1(k2_zfmisc_1(A_924, B_925))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.63/3.45  tff(c_10231, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_10212])).
% 9.63/3.45  tff(c_10822, plain, (![B_1000, A_1001, C_1002]: (k1_xboole_0=B_1000 | k1_relset_1(A_1001, B_1000, C_1002)=A_1001 | ~v1_funct_2(C_1002, A_1001, B_1000) | ~m1_subset_1(C_1002, k1_zfmisc_1(k2_zfmisc_1(A_1001, B_1000))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.63/3.45  tff(c_10835, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_10822])).
% 9.63/3.45  tff(c_10848, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_10231, c_10835])).
% 9.63/3.45  tff(c_10849, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_86, c_10848])).
% 9.63/3.45  tff(c_34, plain, (![B_20, A_19]: (k1_relat_1(k7_relat_1(B_20, A_19))=A_19 | ~r1_tarski(A_19, k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.63/3.45  tff(c_10864, plain, (![A_19]: (k1_relat_1(k7_relat_1('#skF_5', A_19))=A_19 | ~r1_tarski(A_19, '#skF_2') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_10849, c_34])).
% 9.63/3.45  tff(c_10874, plain, (![A_19]: (k1_relat_1(k7_relat_1('#skF_5', A_19))=A_19 | ~r1_tarski(A_19, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1015, c_10864])).
% 9.63/3.45  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.63/3.45  tff(c_10724, plain, (![A_994, B_995, C_996, D_997]: (k2_partfun1(A_994, B_995, C_996, D_997)=k7_relat_1(C_996, D_997) | ~m1_subset_1(C_996, k1_zfmisc_1(k2_zfmisc_1(A_994, B_995))) | ~v1_funct_1(C_996))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.63/3.45  tff(c_10733, plain, (![D_997]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_997)=k7_relat_1('#skF_5', D_997) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_10724])).
% 9.63/3.45  tff(c_10745, plain, (![D_997]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_997)=k7_relat_1('#skF_5', D_997))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_10733])).
% 9.63/3.45  tff(c_4675, plain, (![A_505, B_506, C_507, D_508]: (k2_partfun1(A_505, B_506, C_507, D_508)=k7_relat_1(C_507, D_508) | ~m1_subset_1(C_507, k1_zfmisc_1(k2_zfmisc_1(A_505, B_506))) | ~v1_funct_1(C_507))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.63/3.45  tff(c_4682, plain, (![D_508]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_508)=k7_relat_1('#skF_5', D_508) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_4675])).
% 9.63/3.45  tff(c_4691, plain, (![D_508]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_508)=k7_relat_1('#skF_5', D_508))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4682])).
% 9.63/3.45  tff(c_4913, plain, (![A_529, B_530, C_531, D_532]: (m1_subset_1(k2_partfun1(A_529, B_530, C_531, D_532), k1_zfmisc_1(k2_zfmisc_1(A_529, B_530))) | ~m1_subset_1(C_531, k1_zfmisc_1(k2_zfmisc_1(A_529, B_530))) | ~v1_funct_1(C_531))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.63/3.45  tff(c_4941, plain, (![D_508]: (m1_subset_1(k7_relat_1('#skF_5', D_508), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4691, c_4913])).
% 9.63/3.45  tff(c_4966, plain, (![D_534]: (m1_subset_1(k7_relat_1('#skF_5', D_534), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_4941])).
% 9.63/3.45  tff(c_36, plain, (![C_23, A_21, B_22]: (v1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.63/3.45  tff(c_5007, plain, (![D_534]: (v1_relat_1(k7_relat_1('#skF_5', D_534)))), inference(resolution, [status(thm)], [c_4966, c_36])).
% 9.63/3.45  tff(c_38, plain, (![C_26, B_25, A_24]: (v5_relat_1(C_26, B_25) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.63/3.45  tff(c_5006, plain, (![D_534]: (v5_relat_1(k7_relat_1('#skF_5', D_534), '#skF_3'))), inference(resolution, [status(thm)], [c_4966, c_38])).
% 9.63/3.45  tff(c_28, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.63/3.45  tff(c_4447, plain, (![A_481, B_482, C_483, D_484]: (v1_funct_1(k2_partfun1(A_481, B_482, C_483, D_484)) | ~m1_subset_1(C_483, k1_zfmisc_1(k2_zfmisc_1(A_481, B_482))) | ~v1_funct_1(C_483))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.63/3.45  tff(c_4452, plain, (![D_484]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_484)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_4447])).
% 9.63/3.45  tff(c_4460, plain, (![D_484]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_484)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4452])).
% 9.63/3.45  tff(c_4692, plain, (![D_484]: (v1_funct_1(k7_relat_1('#skF_5', D_484)))), inference(demodulation, [status(thm), theory('equality')], [c_4691, c_4460])).
% 9.63/3.45  tff(c_1571, plain, (![A_256, B_257, C_258]: (k1_relset_1(A_256, B_257, C_258)=k1_relat_1(C_258) | ~m1_subset_1(C_258, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.63/3.45  tff(c_1586, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_1571])).
% 9.63/3.45  tff(c_4826, plain, (![B_525, A_526, C_527]: (k1_xboole_0=B_525 | k1_relset_1(A_526, B_525, C_527)=A_526 | ~v1_funct_2(C_527, A_526, B_525) | ~m1_subset_1(C_527, k1_zfmisc_1(k2_zfmisc_1(A_526, B_525))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.63/3.45  tff(c_4836, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_4826])).
% 9.63/3.45  tff(c_4847, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1586, c_4836])).
% 9.63/3.45  tff(c_4848, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_86, c_4847])).
% 9.63/3.45  tff(c_4863, plain, (![A_19]: (k1_relat_1(k7_relat_1('#skF_5', A_19))=A_19 | ~r1_tarski(A_19, '#skF_2') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4848, c_34])).
% 9.63/3.45  tff(c_5036, plain, (![A_540]: (k1_relat_1(k7_relat_1('#skF_5', A_540))=A_540 | ~r1_tarski(A_540, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1015, c_4863])).
% 9.63/3.45  tff(c_62, plain, (![B_42, A_41]: (m1_subset_1(B_42, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_42), A_41))) | ~r1_tarski(k2_relat_1(B_42), A_41) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.63/3.45  tff(c_5045, plain, (![A_540, A_41]: (m1_subset_1(k7_relat_1('#skF_5', A_540), k1_zfmisc_1(k2_zfmisc_1(A_540, A_41))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', A_540)), A_41) | ~v1_funct_1(k7_relat_1('#skF_5', A_540)) | ~v1_relat_1(k7_relat_1('#skF_5', A_540)) | ~r1_tarski(A_540, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5036, c_62])).
% 9.63/3.45  tff(c_9555, plain, (![A_847, A_848]: (m1_subset_1(k7_relat_1('#skF_5', A_847), k1_zfmisc_1(k2_zfmisc_1(A_847, A_848))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', A_847)), A_848) | ~r1_tarski(A_847, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5007, c_4692, c_5045])).
% 9.63/3.45  tff(c_915, plain, (![A_163, B_164, C_165, D_166]: (v1_funct_1(k2_partfun1(A_163, B_164, C_165, D_166)) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))) | ~v1_funct_1(C_165))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.63/3.45  tff(c_920, plain, (![D_166]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_166)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_915])).
% 9.63/3.45  tff(c_928, plain, (![D_166]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_166)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_920])).
% 9.63/3.45  tff(c_68, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.63/3.45  tff(c_170, plain, (~v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_68])).
% 9.63/3.45  tff(c_931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_928, c_170])).
% 9.63/3.45  tff(c_932, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_68])).
% 9.63/3.45  tff(c_1042, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_932])).
% 9.63/3.45  tff(c_4694, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4691, c_1042])).
% 9.63/3.45  tff(c_9570, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_4')), '#skF_3') | ~r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_9555, c_4694])).
% 9.63/3.45  tff(c_9612, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_9570])).
% 9.63/3.45  tff(c_9631, plain, (~v5_relat_1(k7_relat_1('#skF_5', '#skF_4'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_9612])).
% 9.63/3.45  tff(c_9635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5007, c_5006, c_9631])).
% 9.63/3.45  tff(c_9637, plain, (m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_932])).
% 9.63/3.45  tff(c_10229, plain, (k1_relset_1('#skF_4', '#skF_3', k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))=k1_relat_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_9637, c_10212])).
% 9.63/3.45  tff(c_10748, plain, (k1_relset_1('#skF_4', '#skF_3', k7_relat_1('#skF_5', '#skF_4'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10745, c_10745, c_10229])).
% 9.63/3.45  tff(c_9636, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_932])).
% 9.63/3.45  tff(c_10755, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_4'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10745, c_9636])).
% 9.63/3.45  tff(c_10754, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_10745, c_9637])).
% 9.63/3.45  tff(c_10984, plain, (![B_1007, C_1008, A_1009]: (k1_xboole_0=B_1007 | v1_funct_2(C_1008, A_1009, B_1007) | k1_relset_1(A_1009, B_1007, C_1008)!=A_1009 | ~m1_subset_1(C_1008, k1_zfmisc_1(k2_zfmisc_1(A_1009, B_1007))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.63/3.45  tff(c_10987, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_4'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(resolution, [status(thm)], [c_10754, c_10984])).
% 9.63/3.45  tff(c_11006, plain, (k1_relset_1('#skF_4', '#skF_3', k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_10755, c_86, c_10987])).
% 9.63/3.45  tff(c_11014, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10748, c_11006])).
% 9.63/3.45  tff(c_11021, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10874, c_11014])).
% 9.63/3.45  tff(c_11025, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_11021])).
% 9.63/3.45  tff(c_11027, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_70])).
% 9.63/3.45  tff(c_11026, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_70])).
% 9.63/3.45  tff(c_11033, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11027, c_11026])).
% 9.63/3.45  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.63/3.45  tff(c_11028, plain, (![A_8]: (r1_tarski('#skF_2', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_11026, c_14])).
% 9.63/3.45  tff(c_11045, plain, (![A_8]: (r1_tarski('#skF_3', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_11033, c_11028])).
% 9.63/3.45  tff(c_11040, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11033, c_72])).
% 9.63/3.45  tff(c_15654, plain, (![B_1556, A_1557]: (B_1556=A_1557 | ~r1_tarski(B_1556, A_1557) | ~r1_tarski(A_1557, B_1556))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.63/3.45  tff(c_15660, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_11040, c_15654])).
% 9.63/3.45  tff(c_15671, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11045, c_15660])).
% 9.63/3.45  tff(c_20, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.63/3.45  tff(c_11055, plain, (![B_10]: (k2_zfmisc_1('#skF_3', B_10)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11027, c_11027, c_20])).
% 9.63/3.45  tff(c_11038, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_11033, c_74])).
% 9.63/3.45  tff(c_12597, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11055, c_11038])).
% 9.63/3.45  tff(c_15644, plain, (![A_1552, B_1553]: (r1_tarski(A_1552, B_1553) | ~m1_subset_1(A_1552, k1_zfmisc_1(B_1553)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.63/3.45  tff(c_15652, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_12597, c_15644])).
% 9.63/3.45  tff(c_15658, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_15652, c_15654])).
% 9.63/3.45  tff(c_15668, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11045, c_15658])).
% 9.63/3.45  tff(c_15700, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15671, c_15668])).
% 9.63/3.45  tff(c_11039, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11033, c_76])).
% 9.63/3.45  tff(c_15682, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15671, c_15671, c_11039])).
% 9.63/3.45  tff(c_15701, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15700, c_15682])).
% 9.63/3.45  tff(c_12610, plain, (![B_1214, A_1215]: (B_1214=A_1215 | ~r1_tarski(B_1214, A_1215) | ~r1_tarski(A_1215, B_1214))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.63/3.45  tff(c_12616, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_11040, c_12610])).
% 9.63/3.45  tff(c_12627, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11045, c_12616])).
% 9.63/3.45  tff(c_12600, plain, (![A_1210, B_1211]: (r1_tarski(A_1210, B_1211) | ~m1_subset_1(A_1210, k1_zfmisc_1(B_1211)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.63/3.45  tff(c_12608, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_12597, c_12600])).
% 9.63/3.45  tff(c_12614, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_12608, c_12610])).
% 9.63/3.45  tff(c_12624, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11045, c_12614])).
% 9.63/3.45  tff(c_12657, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12627, c_12624])).
% 9.63/3.45  tff(c_12636, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12627, c_12597])).
% 9.63/3.45  tff(c_12683, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12657, c_12636])).
% 9.63/3.45  tff(c_12637, plain, (![B_10]: (k2_zfmisc_1('#skF_4', B_10)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12627, c_12627, c_11055])).
% 9.63/3.45  tff(c_12912, plain, (![C_1256, B_1257, A_1258]: (v5_relat_1(C_1256, B_1257) | ~m1_subset_1(C_1256, k1_zfmisc_1(k2_zfmisc_1(A_1258, B_1257))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.63/3.45  tff(c_12955, plain, (![C_1266, B_1267]: (v5_relat_1(C_1266, B_1267) | ~m1_subset_1(C_1266, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_12637, c_12912])).
% 9.63/3.45  tff(c_12961, plain, (![B_1267]: (v5_relat_1('#skF_4', B_1267))), inference(resolution, [status(thm)], [c_12683, c_12955])).
% 9.63/3.45  tff(c_12659, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12657, c_78])).
% 9.63/3.45  tff(c_32, plain, (![B_18, A_17]: (r1_tarski(k7_relat_1(B_18, A_17), B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.63/3.45  tff(c_12628, plain, (![A_8]: (A_8='#skF_3' | ~r1_tarski(A_8, '#skF_3'))), inference(resolution, [status(thm)], [c_11045, c_12610])).
% 9.63/3.45  tff(c_12706, plain, (![A_1223]: (A_1223='#skF_4' | ~r1_tarski(A_1223, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12627, c_12627, c_12628])).
% 9.63/3.45  tff(c_12721, plain, (![A_17]: (k7_relat_1('#skF_4', A_17)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_12706])).
% 9.63/3.45  tff(c_12724, plain, (~v1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_12721])).
% 9.63/3.45  tff(c_18, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.63/3.45  tff(c_11047, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11027, c_11027, c_18])).
% 9.63/3.45  tff(c_12638, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12627, c_12627, c_11047])).
% 9.63/3.45  tff(c_12737, plain, (![C_1226, A_1227, B_1228]: (v1_relat_1(C_1226) | ~m1_subset_1(C_1226, k1_zfmisc_1(k2_zfmisc_1(A_1227, B_1228))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.63/3.45  tff(c_12747, plain, (![C_1229]: (v1_relat_1(C_1229) | ~m1_subset_1(C_1229, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_12638, c_12737])).
% 9.63/3.45  tff(c_12750, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12683, c_12747])).
% 9.63/3.45  tff(c_12758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12724, c_12750])).
% 9.63/3.45  tff(c_12759, plain, (![A_17]: (k7_relat_1('#skF_4', A_17)='#skF_4')), inference(splitRight, [status(thm)], [c_12721])).
% 9.63/3.45  tff(c_13722, plain, (![A_1360, B_1361, C_1362, D_1363]: (k2_partfun1(A_1360, B_1361, C_1362, D_1363)=k7_relat_1(C_1362, D_1363) | ~m1_subset_1(C_1362, k1_zfmisc_1(k2_zfmisc_1(A_1360, B_1361))) | ~v1_funct_1(C_1362))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.63/3.45  tff(c_15622, plain, (![B_1547, C_1548, D_1549]: (k2_partfun1('#skF_4', B_1547, C_1548, D_1549)=k7_relat_1(C_1548, D_1549) | ~m1_subset_1(C_1548, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_1548))), inference(superposition, [status(thm), theory('equality')], [c_12637, c_13722])).
% 9.63/3.45  tff(c_15626, plain, (![B_1547, D_1549]: (k2_partfun1('#skF_4', B_1547, '#skF_4', D_1549)=k7_relat_1('#skF_4', D_1549) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_12683, c_15622])).
% 9.63/3.45  tff(c_15633, plain, (![B_1547, D_1549]: (k2_partfun1('#skF_4', B_1547, '#skF_4', D_1549)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12659, c_12759, c_15626])).
% 9.63/3.45  tff(c_14082, plain, (![A_1396, B_1397, C_1398, D_1399]: (m1_subset_1(k2_partfun1(A_1396, B_1397, C_1398, D_1399), k1_zfmisc_1(k2_zfmisc_1(A_1396, B_1397))) | ~m1_subset_1(C_1398, k1_zfmisc_1(k2_zfmisc_1(A_1396, B_1397))) | ~v1_funct_1(C_1398))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.63/3.45  tff(c_14756, plain, (![A_1451, B_1452, C_1453, D_1454]: (v1_relat_1(k2_partfun1(A_1451, B_1452, C_1453, D_1454)) | ~m1_subset_1(C_1453, k1_zfmisc_1(k2_zfmisc_1(A_1451, B_1452))) | ~v1_funct_1(C_1453))), inference(resolution, [status(thm)], [c_14082, c_36])).
% 9.63/3.45  tff(c_14771, plain, (![A_1455, C_1456, D_1457]: (v1_relat_1(k2_partfun1(A_1455, '#skF_4', C_1456, D_1457)) | ~m1_subset_1(C_1456, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_1456))), inference(superposition, [status(thm), theory('equality')], [c_12638, c_14756])).
% 9.63/3.45  tff(c_14775, plain, (![A_1455, D_1457]: (v1_relat_1(k2_partfun1(A_1455, '#skF_4', '#skF_4', D_1457)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_12683, c_14771])).
% 9.63/3.45  tff(c_14782, plain, (![A_1455, D_1457]: (v1_relat_1(k2_partfun1(A_1455, '#skF_4', '#skF_4', D_1457)))), inference(demodulation, [status(thm), theory('equality')], [c_12659, c_14775])).
% 9.63/3.45  tff(c_11094, plain, (![B_1025, A_1026]: (B_1025=A_1026 | ~r1_tarski(B_1025, A_1026) | ~r1_tarski(A_1026, B_1025))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.63/3.45  tff(c_11100, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_11040, c_11094])).
% 9.63/3.45  tff(c_11111, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11045, c_11100])).
% 9.63/3.45  tff(c_11074, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11047, c_11038])).
% 9.63/3.45  tff(c_11077, plain, (![A_1019, B_1020]: (r1_tarski(A_1019, B_1020) | ~m1_subset_1(A_1019, k1_zfmisc_1(B_1020)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.63/3.45  tff(c_11085, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_11074, c_11077])).
% 9.63/3.45  tff(c_11096, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_11085, c_11094])).
% 9.63/3.45  tff(c_11107, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11045, c_11096])).
% 9.63/3.45  tff(c_11140, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11111, c_11107])).
% 9.63/3.45  tff(c_11141, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11140, c_78])).
% 9.63/3.45  tff(c_11124, plain, (![A_8]: (r1_tarski('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_11111, c_11045])).
% 9.63/3.45  tff(c_24, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.63/3.45  tff(c_11821, plain, (![A_1120, B_1121, C_1122, D_1123]: (v1_funct_1(k2_partfun1(A_1120, B_1121, C_1122, D_1123)) | ~m1_subset_1(C_1122, k1_zfmisc_1(k2_zfmisc_1(A_1120, B_1121))) | ~v1_funct_1(C_1122))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.63/3.45  tff(c_12567, plain, (![A_1204, B_1205, A_1206, D_1207]: (v1_funct_1(k2_partfun1(A_1204, B_1205, A_1206, D_1207)) | ~v1_funct_1(A_1206) | ~r1_tarski(A_1206, k2_zfmisc_1(A_1204, B_1205)))), inference(resolution, [status(thm)], [c_24, c_11821])).
% 9.63/3.45  tff(c_12577, plain, (![A_1204, B_1205, D_1207]: (v1_funct_1(k2_partfun1(A_1204, B_1205, '#skF_4', D_1207)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_11124, c_12567])).
% 9.63/3.45  tff(c_12587, plain, (![A_1204, B_1205, D_1207]: (v1_funct_1(k2_partfun1(A_1204, B_1205, '#skF_4', D_1207)))), inference(demodulation, [status(thm), theory('equality')], [c_11141, c_12577])).
% 9.63/3.45  tff(c_11072, plain, (~m1_subset_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1('#skF_3')) | ~v1_funct_2(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11033, c_11033, c_11047, c_11033, c_68])).
% 9.63/3.45  tff(c_11073, plain, (~v1_funct_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_11072])).
% 9.63/3.45  tff(c_11118, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11111, c_11111, c_11073])).
% 9.63/3.45  tff(c_11209, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11140, c_11118])).
% 9.63/3.45  tff(c_12594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12587, c_11209])).
% 9.63/3.45  tff(c_12596, plain, (v1_funct_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_11072])).
% 9.63/3.45  tff(c_12635, plain, (v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12627, c_12627, c_12596])).
% 9.63/3.45  tff(c_12704, plain, (v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12657, c_12635])).
% 9.63/3.45  tff(c_13622, plain, (![B_1353, A_1354]: (m1_subset_1(B_1353, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1353), A_1354))) | ~r1_tarski(k2_relat_1(B_1353), A_1354) | ~v1_funct_1(B_1353) | ~v1_relat_1(B_1353))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.63/3.45  tff(c_13904, plain, (![B_1389]: (m1_subset_1(B_1389, k1_zfmisc_1('#skF_4')) | ~r1_tarski(k2_relat_1(B_1389), '#skF_4') | ~v1_funct_1(B_1389) | ~v1_relat_1(B_1389))), inference(superposition, [status(thm), theory('equality')], [c_12638, c_13622])).
% 9.63/3.45  tff(c_13915, plain, (![B_1390]: (m1_subset_1(B_1390, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(B_1390) | ~v5_relat_1(B_1390, '#skF_4') | ~v1_relat_1(B_1390))), inference(resolution, [status(thm)], [c_28, c_13904])).
% 9.63/3.45  tff(c_12595, plain, (~v1_funct_2(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_11072])).
% 9.63/3.45  tff(c_12598, plain, (~m1_subset_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_12595])).
% 9.63/3.45  tff(c_12778, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12627, c_12627, c_12627, c_12657, c_12598])).
% 9.63/3.45  tff(c_13931, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')) | ~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4') | ~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_13915, c_12778])).
% 9.63/3.45  tff(c_13943, plain, (~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4') | ~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12704, c_13931])).
% 9.63/3.45  tff(c_14141, plain, (~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(splitLeft, [status(thm)], [c_13943])).
% 9.63/3.45  tff(c_14786, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14782, c_14141])).
% 9.63/3.45  tff(c_14787, plain, (~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_13943])).
% 9.63/3.45  tff(c_15635, plain, (~v5_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15633, c_14787])).
% 9.63/3.45  tff(c_15640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12961, c_15635])).
% 9.63/3.45  tff(c_15642, plain, (m1_subset_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_12595])).
% 9.63/3.45  tff(c_15719, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15700, c_15671, c_15671, c_15671, c_15642])).
% 9.63/3.45  tff(c_22, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.63/3.45  tff(c_15723, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_15719, c_22])).
% 9.63/3.45  tff(c_15672, plain, (![A_8]: (A_8='#skF_3' | ~r1_tarski(A_8, '#skF_3'))), inference(resolution, [status(thm)], [c_11045, c_15654])).
% 9.63/3.45  tff(c_15746, plain, (![A_8]: (A_8='#skF_4' | ~r1_tarski(A_8, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15671, c_15671, c_15672])).
% 9.63/3.45  tff(c_15771, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_15723, c_15746])).
% 9.63/3.45  tff(c_15641, plain, (~v1_funct_2(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_12595])).
% 9.63/3.45  tff(c_15798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15701, c_15771, c_15700, c_15671, c_15671, c_15671, c_15641])).
% 9.63/3.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.63/3.45  
% 9.63/3.45  Inference rules
% 9.63/3.45  ----------------------
% 9.63/3.45  #Ref     : 0
% 9.63/3.45  #Sup     : 3322
% 9.63/3.45  #Fact    : 0
% 9.63/3.45  #Define  : 0
% 9.63/3.45  #Split   : 35
% 9.63/3.45  #Chain   : 0
% 9.63/3.45  #Close   : 0
% 9.63/3.45  
% 9.63/3.45  Ordering : KBO
% 9.63/3.45  
% 9.63/3.45  Simplification rules
% 9.63/3.45  ----------------------
% 9.63/3.45  #Subsume      : 383
% 9.63/3.45  #Demod        : 4568
% 9.63/3.45  #Tautology    : 1583
% 9.63/3.45  #SimpNegUnit  : 34
% 9.63/3.45  #BackRed      : 98
% 9.63/3.45  
% 9.63/3.45  #Partial instantiations: 0
% 9.63/3.45  #Strategies tried      : 1
% 9.63/3.45  
% 9.63/3.45  Timing (in seconds)
% 9.63/3.45  ----------------------
% 9.63/3.45  Preprocessing        : 0.35
% 9.63/3.45  Parsing              : 0.18
% 9.63/3.45  CNF conversion       : 0.02
% 9.63/3.45  Main loop            : 2.29
% 9.63/3.45  Inferencing          : 0.73
% 9.63/3.45  Reduction            : 0.87
% 9.63/3.45  Demodulation         : 0.65
% 9.63/3.45  BG Simplification    : 0.07
% 9.63/3.45  Subsumption          : 0.45
% 9.63/3.45  Abstraction          : 0.08
% 9.63/3.45  MUC search           : 0.00
% 9.63/3.45  Cooper               : 0.00
% 9.63/3.45  Total                : 2.71
% 9.63/3.45  Index Insertion      : 0.00
% 9.63/3.45  Index Deletion       : 0.00
% 9.63/3.45  Index Matching       : 0.00
% 9.63/3.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
