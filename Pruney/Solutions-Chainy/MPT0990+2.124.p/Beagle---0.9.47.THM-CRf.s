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
% DateTime   : Thu Dec  3 10:13:14 EST 2020

% Result     : Theorem 12.79s
% Output     : CNFRefutation 13.04s
% Verified   : 
% Statistics : Number of formulae       :  271 (10131 expanded)
%              Number of leaves         :   53 (3542 expanded)
%              Depth                    :   27
%              Number of atoms          :  621 (30617 expanded)
%              Number of equality atoms :  135 (7668 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_192,negated_conjecture,(
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_156,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_144,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_154,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_140,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_128,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_166,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_64,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_109,plain,(
    ! [B_61,A_62] :
      ( v1_relat_1(B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62))
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_115,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_82,c_109])).

tff(c_124,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_115])).

tff(c_86,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_70,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_24,plain,(
    ! [A_23] :
      ( v1_relat_1(k2_funct_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_74,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_310,plain,(
    ! [A_94,B_95,C_96] :
      ( k2_relset_1(A_94,B_95,C_96) = k2_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_319,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_310])).

tff(c_326,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_319])).

tff(c_246,plain,(
    ! [A_87] :
      ( k1_relat_1(k2_funct_1(A_87)) = k2_relat_1(A_87)
      | ~ v2_funct_1(A_87)
      | ~ v1_funct_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_10,plain,(
    ! [A_8] :
      ( k9_relat_1(A_8,k1_relat_1(A_8)) = k2_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16710,plain,(
    ! [A_690] :
      ( k9_relat_1(k2_funct_1(A_690),k2_relat_1(A_690)) = k2_relat_1(k2_funct_1(A_690))
      | ~ v1_relat_1(k2_funct_1(A_690))
      | ~ v2_funct_1(A_690)
      | ~ v1_funct_1(A_690)
      | ~ v1_relat_1(A_690) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_10])).

tff(c_16726,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_16710])).

tff(c_16733,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_70,c_16726])).

tff(c_16740,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_16733])).

tff(c_16743,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_16740])).

tff(c_16747,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_16743])).

tff(c_16749,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_16733])).

tff(c_177,plain,(
    ! [C_78,A_79,B_80] :
      ( v4_relat_1(C_78,A_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_188,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_82,c_177])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    ! [A_9] :
      ( k10_relat_1(A_9,k2_relat_1(A_9)) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_340,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_12])).

tff(c_350,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_340])).

tff(c_16748,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_16733])).

tff(c_26,plain,(
    ! [B_25,A_24] :
      ( k9_relat_1(k2_funct_1(B_25),A_24) = k10_relat_1(B_25,A_24)
      | ~ v2_funct_1(B_25)
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_16755,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16748,c_26])).

tff(c_16762,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_70,c_350,c_16755])).

tff(c_56,plain,(
    ! [A_51] : k6_relat_1(A_51) = k6_partfun1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_18,plain,(
    ! [B_20,A_19] :
      ( k5_relat_1(B_20,k6_relat_1(A_19)) = B_20
      | ~ r1_tarski(k2_relat_1(B_20),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_90,plain,(
    ! [B_20,A_19] :
      ( k5_relat_1(B_20,k6_partfun1(A_19)) = B_20
      | ~ r1_tarski(k2_relat_1(B_20),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_18])).

tff(c_16785,plain,(
    ! [A_19] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(A_19)) = k2_funct_1('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_19)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16762,c_90])).

tff(c_16811,plain,(
    ! [A_19] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(A_19)) = k2_funct_1('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16749,c_16785])).

tff(c_52,plain,(
    ! [A_44] : m1_subset_1(k6_partfun1(A_44),k1_zfmisc_1(k2_zfmisc_1(A_44,A_44))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_112,plain,(
    ! [A_44] :
      ( v1_relat_1(k6_partfun1(A_44))
      | ~ v1_relat_1(k2_zfmisc_1(A_44,A_44)) ) ),
    inference(resolution,[status(thm)],[c_52,c_109])).

tff(c_121,plain,(
    ! [A_44] : v1_relat_1(k6_partfun1(A_44)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_112])).

tff(c_34,plain,(
    ! [A_27] :
      ( k5_relat_1(A_27,k2_funct_1(A_27)) = k6_relat_1(k1_relat_1(A_27))
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_87,plain,(
    ! [A_27] :
      ( k5_relat_1(A_27,k2_funct_1(A_27)) = k6_partfun1(k1_relat_1(A_27))
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_34])).

tff(c_527,plain,(
    ! [A_107,B_108,C_109] :
      ( k5_relat_1(k5_relat_1(A_107,B_108),C_109) = k5_relat_1(A_107,k5_relat_1(B_108,C_109))
      | ~ v1_relat_1(C_109)
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_19623,plain,(
    ! [A_766,C_767] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_766)),C_767) = k5_relat_1(A_766,k5_relat_1(k2_funct_1(A_766),C_767))
      | ~ v1_relat_1(C_767)
      | ~ v1_relat_1(k2_funct_1(A_766))
      | ~ v1_relat_1(A_766)
      | ~ v2_funct_1(A_766)
      | ~ v1_funct_1(A_766)
      | ~ v1_relat_1(A_766) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_527])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_118,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_76,c_109])).

tff(c_127,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_118])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_12379,plain,(
    ! [E_583,B_579,C_582,D_581,F_584,A_580] :
      ( k1_partfun1(A_580,B_579,C_582,D_581,E_583,F_584) = k5_relat_1(E_583,F_584)
      | ~ m1_subset_1(F_584,k1_zfmisc_1(k2_zfmisc_1(C_582,D_581)))
      | ~ v1_funct_1(F_584)
      | ~ m1_subset_1(E_583,k1_zfmisc_1(k2_zfmisc_1(A_580,B_579)))
      | ~ v1_funct_1(E_583) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_12389,plain,(
    ! [A_580,B_579,E_583] :
      ( k1_partfun1(A_580,B_579,'#skF_2','#skF_1',E_583,'#skF_4') = k5_relat_1(E_583,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_583,k1_zfmisc_1(k2_zfmisc_1(A_580,B_579)))
      | ~ v1_funct_1(E_583) ) ),
    inference(resolution,[status(thm)],[c_76,c_12379])).

tff(c_16128,plain,(
    ! [A_674,B_675,E_676] :
      ( k1_partfun1(A_674,B_675,'#skF_2','#skF_1',E_676,'#skF_4') = k5_relat_1(E_676,'#skF_4')
      | ~ m1_subset_1(E_676,k1_zfmisc_1(k2_zfmisc_1(A_674,B_675)))
      | ~ v1_funct_1(E_676) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_12389])).

tff(c_16140,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_16128])).

tff(c_16151,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_16140])).

tff(c_16175,plain,(
    ! [F_680,C_681,B_678,E_679,D_682,A_677] :
      ( m1_subset_1(k1_partfun1(A_677,B_678,C_681,D_682,E_679,F_680),k1_zfmisc_1(k2_zfmisc_1(A_677,D_682)))
      | ~ m1_subset_1(F_680,k1_zfmisc_1(k2_zfmisc_1(C_681,D_682)))
      | ~ v1_funct_1(F_680)
      | ~ m1_subset_1(E_679,k1_zfmisc_1(k2_zfmisc_1(A_677,B_678)))
      | ~ v1_funct_1(E_679) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_16205,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16151,c_16175])).

tff(c_16219,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_16205])).

tff(c_72,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_9147,plain,(
    ! [D_447,C_448,A_449,B_450] :
      ( D_447 = C_448
      | ~ r2_relset_1(A_449,B_450,C_448,D_447)
      | ~ m1_subset_1(D_447,k1_zfmisc_1(k2_zfmisc_1(A_449,B_450)))
      | ~ m1_subset_1(C_448,k1_zfmisc_1(k2_zfmisc_1(A_449,B_450))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_9159,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_72,c_9147])).

tff(c_9180,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_9159])).

tff(c_16590,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16219,c_16151,c_16151,c_9180])).

tff(c_203,plain,(
    ! [A_82] : v4_relat_1(k6_partfun1(A_82),A_82) ),
    inference(resolution,[status(thm)],[c_52,c_177])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( k7_relat_1(B_11,A_10) = B_11
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_206,plain,(
    ! [A_82] :
      ( k7_relat_1(k6_partfun1(A_82),A_82) = k6_partfun1(A_82)
      | ~ v1_relat_1(k6_partfun1(A_82)) ) ),
    inference(resolution,[status(thm)],[c_203,c_14])).

tff(c_209,plain,(
    ! [A_82] : k7_relat_1(k6_partfun1(A_82),A_82) = k6_partfun1(A_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_206])).

tff(c_20,plain,(
    ! [A_21,B_22] :
      ( k5_relat_1(k6_relat_1(A_21),B_22) = k7_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_89,plain,(
    ! [A_21,B_22] :
      ( k5_relat_1(k6_partfun1(A_21),B_22) = k7_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_20])).

tff(c_559,plain,(
    ! [A_21,B_22,C_109] :
      ( k5_relat_1(k6_partfun1(A_21),k5_relat_1(B_22,C_109)) = k5_relat_1(k7_relat_1(B_22,A_21),C_109)
      | ~ v1_relat_1(C_109)
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(k6_partfun1(A_21))
      | ~ v1_relat_1(B_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_527])).

tff(c_589,plain,(
    ! [A_112,B_113,C_114] :
      ( k5_relat_1(k6_partfun1(A_112),k5_relat_1(B_113,C_114)) = k5_relat_1(k7_relat_1(B_113,A_112),C_114)
      | ~ v1_relat_1(C_114)
      | ~ v1_relat_1(B_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_559])).

tff(c_628,plain,(
    ! [A_21,A_112,B_22] :
      ( k5_relat_1(k7_relat_1(k6_partfun1(A_21),A_112),B_22) = k5_relat_1(k6_partfun1(A_112),k7_relat_1(B_22,A_21))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(k6_partfun1(A_21))
      | ~ v1_relat_1(B_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_589])).

tff(c_1366,plain,(
    ! [A_160,A_161,B_162] :
      ( k5_relat_1(k7_relat_1(k6_partfun1(A_160),A_161),B_162) = k5_relat_1(k6_partfun1(A_161),k7_relat_1(B_162,A_160))
      | ~ v1_relat_1(B_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_628])).

tff(c_1479,plain,(
    ! [A_165,B_166] :
      ( k5_relat_1(k6_partfun1(A_165),k7_relat_1(B_166,A_165)) = k5_relat_1(k6_partfun1(A_165),B_166)
      | ~ v1_relat_1(B_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_1366])).

tff(c_1536,plain,(
    ! [B_167,A_168] :
      ( k7_relat_1(k7_relat_1(B_167,A_168),A_168) = k5_relat_1(k6_partfun1(A_168),B_167)
      | ~ v1_relat_1(k7_relat_1(B_167,A_168))
      | ~ v1_relat_1(B_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1479,c_89])).

tff(c_1542,plain,(
    ! [A_82] :
      ( k7_relat_1(k7_relat_1(k6_partfun1(A_82),A_82),A_82) = k5_relat_1(k6_partfun1(A_82),k6_partfun1(A_82))
      | ~ v1_relat_1(k6_partfun1(A_82))
      | ~ v1_relat_1(k6_partfun1(A_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_1536])).

tff(c_1550,plain,(
    ! [A_82] : k5_relat_1(k6_partfun1(A_82),k6_partfun1(A_82)) = k6_partfun1(A_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_121,c_209,c_209,c_1542])).

tff(c_58,plain,(
    ! [A_52] :
      ( m1_subset_1(A_52,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_52),k2_relat_1(A_52))))
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_331,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_58])).

tff(c_344,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_331])).

tff(c_38,plain,(
    ! [C_30,A_28,B_29] :
      ( v4_relat_1(C_30,A_28)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_377,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_344,c_38])).

tff(c_394,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_377,c_14])).

tff(c_397,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_394])).

tff(c_1540,plain,
    ( k7_relat_1(k7_relat_1('#skF_3',k1_relat_1('#skF_3')),k1_relat_1('#skF_3')) = k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_1536])).

tff(c_1548,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_124,c_397,c_397,c_1540])).

tff(c_16,plain,(
    ! [A_12,B_16,C_18] :
      ( k5_relat_1(k5_relat_1(A_12,B_16),C_18) = k5_relat_1(A_12,k5_relat_1(B_16,C_18))
      | ~ v1_relat_1(C_18)
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1648,plain,(
    ! [C_18] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k5_relat_1('#skF_3',C_18)) = k5_relat_1('#skF_3',C_18)
      | ~ v1_relat_1(C_18)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1548,c_16])).

tff(c_2187,plain,(
    ! [C_207] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k5_relat_1('#skF_3',C_207)) = k5_relat_1('#skF_3',C_207)
      | ~ v1_relat_1(C_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_124,c_1648])).

tff(c_2225,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1(k1_relat_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_2187])).

tff(c_2248,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_70,c_1550,c_2225])).

tff(c_2251,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2248])).

tff(c_2285,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_2251])).

tff(c_2289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_2285])).

tff(c_2291,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2248])).

tff(c_22,plain,(
    ! [A_23] :
      ( v1_funct_1(k2_funct_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2941,plain,(
    ! [A_223] :
      ( k9_relat_1(k2_funct_1(A_223),k2_relat_1(A_223)) = k2_relat_1(k2_funct_1(A_223))
      | ~ v1_relat_1(k2_funct_1(A_223))
      | ~ v2_funct_1(A_223)
      | ~ v1_funct_1(A_223)
      | ~ v1_relat_1(A_223) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_10])).

tff(c_2957,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_2941])).

tff(c_2964,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_70,c_2291,c_2957])).

tff(c_2968,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2964,c_26])).

tff(c_2975,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_70,c_350,c_2968])).

tff(c_277,plain,(
    ! [A_91] :
      ( m1_subset_1(A_91,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_91),k2_relat_1(A_91))))
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_36,plain,(
    ! [C_30,B_29,A_28] :
      ( v5_relat_1(C_30,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_297,plain,(
    ! [A_91] :
      ( v5_relat_1(A_91,k2_relat_1(A_91))
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(resolution,[status(thm)],[c_277,c_36])).

tff(c_2995,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2975,c_297])).

tff(c_3025,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2291,c_2995])).

tff(c_3089,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3025])).

tff(c_3092,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_3089])).

tff(c_3096,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_3092])).

tff(c_3098,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3025])).

tff(c_30,plain,(
    ! [A_26] :
      ( k1_relat_1(k2_funct_1(A_26)) = k2_relat_1(A_26)
      | ~ v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4024,plain,(
    ! [A_245] :
      ( m1_subset_1(k2_funct_1(A_245),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_245),k2_relat_1(k2_funct_1(A_245)))))
      | ~ v1_funct_1(k2_funct_1(A_245))
      | ~ v1_relat_1(k2_funct_1(A_245))
      | ~ v2_funct_1(A_245)
      | ~ v1_funct_1(A_245)
      | ~ v1_relat_1(A_245) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_277])).

tff(c_4062,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2975,c_4024])).

tff(c_4089,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_70,c_2291,c_3098,c_326,c_4062])).

tff(c_4148,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4089,c_38])).

tff(c_258,plain,(
    ! [A_87,A_4] :
      ( r1_tarski(k2_relat_1(A_87),A_4)
      | ~ v4_relat_1(k2_funct_1(A_87),A_4)
      | ~ v1_relat_1(k2_funct_1(A_87))
      | ~ v2_funct_1(A_87)
      | ~ v1_funct_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_6])).

tff(c_4156,plain,
    ( r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4148,c_258])).

tff(c_4162,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_70,c_2291,c_326,c_4156])).

tff(c_192,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_188,c_14])).

tff(c_195,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_192])).

tff(c_334,plain,(
    ! [A_19] :
      ( k5_relat_1('#skF_3',k6_partfun1(A_19)) = '#skF_3'
      | ~ r1_tarski('#skF_2',A_19)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_90])).

tff(c_346,plain,(
    ! [A_19] :
      ( k5_relat_1('#skF_3',k6_partfun1(A_19)) = '#skF_3'
      | ~ r1_tarski('#skF_2',A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_334])).

tff(c_622,plain,(
    ! [A_112,A_19] :
      ( k5_relat_1(k7_relat_1('#skF_3',A_112),k6_partfun1(A_19)) = k5_relat_1(k6_partfun1(A_112),'#skF_3')
      | ~ v1_relat_1(k6_partfun1(A_19))
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski('#skF_2',A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_589])).

tff(c_647,plain,(
    ! [A_115,A_116] :
      ( k5_relat_1(k7_relat_1('#skF_3',A_115),k6_partfun1(A_116)) = k5_relat_1(k6_partfun1(A_115),'#skF_3')
      | ~ r1_tarski('#skF_2',A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_121,c_622])).

tff(c_678,plain,(
    ! [A_117] :
      ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = k5_relat_1('#skF_3',k6_partfun1(A_117))
      | ~ r1_tarski('#skF_2',A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_647])).

tff(c_700,plain,(
    ! [A_117] :
      ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
      | ~ r1_tarski('#skF_2',A_117)
      | ~ r1_tarski('#skF_2',A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_678,c_346])).

tff(c_730,plain,(
    ! [A_117] :
      ( ~ r1_tarski('#skF_2',A_117)
      | ~ r1_tarski('#skF_2',A_117) ) ),
    inference(splitLeft,[status(thm)],[c_700])).

tff(c_4167,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_4162,c_730])).

tff(c_4171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4162,c_4167])).

tff(c_4172,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_700])).

tff(c_9095,plain,(
    ! [C_18] :
      ( k5_relat_1(k6_partfun1('#skF_1'),k5_relat_1('#skF_3',C_18)) = k5_relat_1('#skF_3',C_18)
      | ~ v1_relat_1(C_18)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k6_partfun1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4172,c_16])).

tff(c_9722,plain,(
    ! [C_494] :
      ( k5_relat_1(k6_partfun1('#skF_1'),k5_relat_1('#skF_3',C_494)) = k5_relat_1('#skF_3',C_494)
      | ~ v1_relat_1(C_494) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_124,c_9095])).

tff(c_9754,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k6_partfun1(k1_relat_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_9722])).

tff(c_9773,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k6_partfun1(k1_relat_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_70,c_9754])).

tff(c_9937,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_9773])).

tff(c_9967,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_9937])).

tff(c_9971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_9967])).

tff(c_9973,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_9773])).

tff(c_10500,plain,(
    ! [A_541] :
      ( k9_relat_1(k2_funct_1(A_541),k2_relat_1(A_541)) = k2_relat_1(k2_funct_1(A_541))
      | ~ v1_relat_1(k2_funct_1(A_541))
      | ~ v2_funct_1(A_541)
      | ~ v1_funct_1(A_541)
      | ~ v1_relat_1(A_541) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_10])).

tff(c_10516,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_10500])).

tff(c_10523,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_70,c_9973,c_10516])).

tff(c_10527,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10523,c_26])).

tff(c_10534,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_70,c_350,c_10527])).

tff(c_10554,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10534,c_297])).

tff(c_10584,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9973,c_10554])).

tff(c_10672,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_10584])).

tff(c_10675,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_10672])).

tff(c_10679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_10675])).

tff(c_10681,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_10584])).

tff(c_12142,plain,(
    ! [A_574] :
      ( m1_subset_1(k2_funct_1(A_574),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_574),k2_relat_1(k2_funct_1(A_574)))))
      | ~ v1_funct_1(k2_funct_1(A_574))
      | ~ v1_relat_1(k2_funct_1(A_574))
      | ~ v2_funct_1(A_574)
      | ~ v1_funct_1(A_574)
      | ~ v1_relat_1(A_574) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_277])).

tff(c_12180,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10534,c_12142])).

tff(c_12207,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_70,c_9973,c_10681,c_326,c_12180])).

tff(c_12266,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_12207,c_38])).

tff(c_12274,plain,
    ( r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12266,c_258])).

tff(c_12280,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_70,c_9973,c_326,c_12274])).

tff(c_302,plain,(
    ! [A_93] :
      ( v4_relat_1(A_93,k1_relat_1(A_93))
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(resolution,[status(thm)],[c_277,c_38])).

tff(c_309,plain,(
    ! [A_93] :
      ( k7_relat_1(A_93,k1_relat_1(A_93)) = A_93
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(resolution,[status(thm)],[c_302,c_14])).

tff(c_663,plain,(
    ! [A_116] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),'#skF_3') = k5_relat_1('#skF_3',k6_partfun1(A_116))
      | ~ r1_tarski('#skF_2',A_116)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_647])).

tff(c_9798,plain,(
    ! [A_501] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),'#skF_3') = k5_relat_1('#skF_3',k6_partfun1(A_501))
      | ~ r1_tarski('#skF_2',A_501) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_663])).

tff(c_9823,plain,(
    ! [A_501] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),'#skF_3') = '#skF_3'
      | ~ r1_tarski('#skF_2',A_501)
      | ~ r1_tarski('#skF_2',A_501) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9798,c_346])).

tff(c_9855,plain,(
    ! [A_501] :
      ( ~ r1_tarski('#skF_2',A_501)
      | ~ r1_tarski('#skF_2',A_501) ) ),
    inference(splitLeft,[status(thm)],[c_9823])).

tff(c_12285,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_12280,c_9855])).

tff(c_12289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12280,c_12285])).

tff(c_12290,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9823])).

tff(c_12328,plain,(
    ! [C_18] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k5_relat_1('#skF_3',C_18)) = k5_relat_1('#skF_3',C_18)
      | ~ v1_relat_1(C_18)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12290,c_16])).

tff(c_12343,plain,(
    ! [C_18] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k5_relat_1('#skF_3',C_18)) = k5_relat_1('#skF_3',C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_124,c_12328])).

tff(c_16611,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_1')) = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_16590,c_12343])).

tff(c_16624,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_1')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_16590,c_16611])).

tff(c_19673,plain,
    ( k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1'))) = k6_partfun1('#skF_1')
    | ~ v1_relat_1(k6_partfun1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_19623,c_16624])).

tff(c_19822,plain,(
    k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1'))) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_70,c_124,c_16749,c_121,c_19673])).

tff(c_20013,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16811,c_19822])).

tff(c_20151,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_20013])).

tff(c_20154,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_20151])).

tff(c_20158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_188,c_20154])).

tff(c_20160,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_20013])).

tff(c_189,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_177])).

tff(c_198,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_189,c_14])).

tff(c_201,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_198])).

tff(c_16779,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16762,c_297])).

tff(c_16807,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16749,c_16779])).

tff(c_16847,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_16807])).

tff(c_16850,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_16847])).

tff(c_16854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_16850])).

tff(c_16856,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_16807])).

tff(c_32,plain,(
    ! [A_27] :
      ( k5_relat_1(k2_funct_1(A_27),A_27) = k6_relat_1(k2_relat_1(A_27))
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_88,plain,(
    ! [A_27] :
      ( k5_relat_1(k2_funct_1(A_27),A_27) = k6_partfun1(k2_relat_1(A_27))
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_32])).

tff(c_12387,plain,(
    ! [A_580,B_579,E_583] :
      ( k1_partfun1(A_580,B_579,'#skF_1','#skF_2',E_583,'#skF_3') = k5_relat_1(E_583,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_583,k1_zfmisc_1(k2_zfmisc_1(A_580,B_579)))
      | ~ v1_funct_1(E_583) ) ),
    inference(resolution,[status(thm)],[c_82,c_12379])).

tff(c_16354,plain,(
    ! [A_685,B_686,E_687] :
      ( k1_partfun1(A_685,B_686,'#skF_1','#skF_2',E_687,'#skF_3') = k5_relat_1(E_687,'#skF_3')
      | ~ m1_subset_1(E_687,k1_zfmisc_1(k2_zfmisc_1(A_685,B_686)))
      | ~ v1_funct_1(E_687) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_12387])).

tff(c_17257,plain,(
    ! [A_702] :
      ( k1_partfun1(k1_relat_1(A_702),k2_relat_1(A_702),'#skF_1','#skF_2',A_702,'#skF_3') = k5_relat_1(A_702,'#skF_3')
      | ~ v1_funct_1(A_702)
      | ~ v1_relat_1(A_702) ) ),
    inference(resolution,[status(thm)],[c_58,c_16354])).

tff(c_9776,plain,(
    ! [D_500,C_499,B_496,E_497,A_495,F_498] :
      ( v1_funct_1(k1_partfun1(A_495,B_496,C_499,D_500,E_497,F_498))
      | ~ m1_subset_1(F_498,k1_zfmisc_1(k2_zfmisc_1(C_499,D_500)))
      | ~ v1_funct_1(F_498)
      | ~ m1_subset_1(E_497,k1_zfmisc_1(k2_zfmisc_1(A_495,B_496)))
      | ~ v1_funct_1(E_497) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_9784,plain,(
    ! [A_495,B_496,E_497] :
      ( v1_funct_1(k1_partfun1(A_495,B_496,'#skF_1','#skF_2',E_497,'#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_497,k1_zfmisc_1(k2_zfmisc_1(A_495,B_496)))
      | ~ v1_funct_1(E_497) ) ),
    inference(resolution,[status(thm)],[c_82,c_9776])).

tff(c_12291,plain,(
    ! [A_575,B_576,E_577] :
      ( v1_funct_1(k1_partfun1(A_575,B_576,'#skF_1','#skF_2',E_577,'#skF_3'))
      | ~ m1_subset_1(E_577,k1_zfmisc_1(k2_zfmisc_1(A_575,B_576)))
      | ~ v1_funct_1(E_577) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_9784])).

tff(c_12310,plain,(
    ! [A_52] :
      ( v1_funct_1(k1_partfun1(k1_relat_1(A_52),k2_relat_1(A_52),'#skF_1','#skF_2',A_52,'#skF_3'))
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(resolution,[status(thm)],[c_58,c_12291])).

tff(c_17709,plain,(
    ! [A_721] :
      ( v1_funct_1(k5_relat_1(A_721,'#skF_3'))
      | ~ v1_funct_1(A_721)
      | ~ v1_relat_1(A_721)
      | ~ v1_funct_1(A_721)
      | ~ v1_relat_1(A_721) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17257,c_12310])).

tff(c_17739,plain,
    ( v1_funct_1(k6_partfun1(k2_relat_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_17709])).

tff(c_17757,plain,(
    v1_funct_1(k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_70,c_16749,c_16856,c_16749,c_16856,c_326,c_17739])).

tff(c_16148,plain,(
    ! [A_44] :
      ( k1_partfun1(A_44,A_44,'#skF_2','#skF_1',k6_partfun1(A_44),'#skF_4') = k5_relat_1(k6_partfun1(A_44),'#skF_4')
      | ~ v1_funct_1(k6_partfun1(A_44)) ) ),
    inference(resolution,[status(thm)],[c_52,c_16128])).

tff(c_17764,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_1',k6_partfun1('#skF_2'),'#skF_4') = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_17757,c_16148])).

tff(c_46,plain,(
    ! [D_41,B_39,A_38,F_43,E_42,C_40] :
      ( m1_subset_1(k1_partfun1(A_38,B_39,C_40,D_41,E_42,F_43),k1_zfmisc_1(k2_zfmisc_1(A_38,D_41)))
      | ~ m1_subset_1(F_43,k1_zfmisc_1(k2_zfmisc_1(C_40,D_41)))
      | ~ v1_funct_1(F_43)
      | ~ m1_subset_1(E_42,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_1(E_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_18809,plain,
    ( m1_subset_1(k5_relat_1(k6_partfun1('#skF_2'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_1(k6_partfun1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17764,c_46])).

tff(c_18816,plain,(
    m1_subset_1(k5_relat_1(k6_partfun1('#skF_2'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17757,c_52,c_80,c_76,c_18809])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18948,plain,
    ( v1_relat_1(k5_relat_1(k6_partfun1('#skF_2'),'#skF_4'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_18816,c_2])).

tff(c_18994,plain,(
    v1_relat_1(k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18948])).

tff(c_18990,plain,(
    v4_relat_1(k5_relat_1(k6_partfun1('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_18816,c_38])).

tff(c_19004,plain,
    ( k7_relat_1(k5_relat_1(k6_partfun1('#skF_2'),'#skF_4'),'#skF_2') = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1(k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_18990,c_14])).

tff(c_19010,plain,(
    k7_relat_1(k5_relat_1(k6_partfun1('#skF_2'),'#skF_4'),'#skF_2') = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18994,c_19004])).

tff(c_19402,plain,
    ( k7_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_2') = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_19010])).

tff(c_19406,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_201,c_201,c_19402])).

tff(c_19018,plain,(
    ! [A_754,C_755] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_754)),C_755) = k5_relat_1(k2_funct_1(A_754),k5_relat_1(A_754,C_755))
      | ~ v1_relat_1(C_755)
      | ~ v1_relat_1(A_754)
      | ~ v1_relat_1(k2_funct_1(A_754))
      | ~ v2_funct_1(A_754)
      | ~ v1_funct_1(A_754)
      | ~ v1_relat_1(A_754) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_527])).

tff(c_19164,plain,(
    ! [C_755] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_755)) = k5_relat_1(k6_partfun1('#skF_2'),C_755)
      | ~ v1_relat_1(C_755)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_19018])).

tff(c_23026,plain,(
    ! [C_849] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_849)) = k5_relat_1(k6_partfun1('#skF_2'),C_849)
      | ~ v1_relat_1(C_849) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_70,c_16749,c_124,c_19164])).

tff(c_23107,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_16590,c_23026])).

tff(c_23149,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_19406,c_23107])).

tff(c_28,plain,(
    ! [A_26] :
      ( k2_relat_1(k2_funct_1(A_26)) = k1_relat_1(A_26)
      | ~ v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_242,plain,(
    ! [B_85,A_86] :
      ( k5_relat_1(B_85,k6_partfun1(A_86)) = B_85
      | ~ r1_tarski(k2_relat_1(B_85),A_86)
      | ~ v1_relat_1(B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_18])).

tff(c_245,plain,(
    ! [A_26,A_86] :
      ( k5_relat_1(k2_funct_1(A_26),k6_partfun1(A_86)) = k2_funct_1(A_26)
      | ~ r1_tarski(k1_relat_1(A_26),A_86)
      | ~ v1_relat_1(k2_funct_1(A_26))
      | ~ v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_242])).

tff(c_23168,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_23149,c_245])).

tff(c_23193,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_70,c_16749,c_20160,c_23168])).

tff(c_23195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_23193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.79/5.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.79/5.28  
% 12.79/5.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.79/5.28  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.79/5.28  
% 12.79/5.28  %Foreground sorts:
% 12.79/5.28  
% 12.79/5.28  
% 12.79/5.28  %Background operators:
% 12.79/5.28  
% 12.79/5.28  
% 12.79/5.28  %Foreground operators:
% 12.79/5.28  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.79/5.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.79/5.28  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 12.79/5.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.79/5.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.79/5.28  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 12.79/5.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.79/5.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.79/5.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 12.79/5.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.79/5.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.79/5.28  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.79/5.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.79/5.28  tff('#skF_2', type, '#skF_2': $i).
% 12.79/5.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.79/5.28  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 12.79/5.28  tff('#skF_3', type, '#skF_3': $i).
% 12.79/5.28  tff('#skF_1', type, '#skF_1': $i).
% 12.79/5.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.79/5.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.79/5.28  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 12.79/5.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.79/5.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 12.79/5.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.79/5.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.79/5.28  tff('#skF_4', type, '#skF_4': $i).
% 12.79/5.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 12.79/5.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.79/5.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.79/5.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.79/5.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.79/5.28  
% 13.04/5.32  tff(f_192, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 13.04/5.32  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 13.04/5.32  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 13.04/5.32  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 13.04/5.32  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.04/5.32  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 13.04/5.32  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 13.04/5.32  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.04/5.32  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 13.04/5.32  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 13.04/5.32  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 13.04/5.32  tff(f_156, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 13.04/5.32  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 13.04/5.32  tff(f_144, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 13.04/5.32  tff(f_110, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 13.04/5.32  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 13.04/5.32  tff(f_154, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 13.04/5.32  tff(f_140, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 13.04/5.32  tff(f_128, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 13.04/5.32  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 13.04/5.32  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 13.04/5.32  tff(f_166, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 13.04/5.32  tff(c_64, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_192])).
% 13.04/5.32  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 13.04/5.32  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 13.04/5.32  tff(c_109, plain, (![B_61, A_62]: (v1_relat_1(B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.04/5.32  tff(c_115, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_82, c_109])).
% 13.04/5.32  tff(c_124, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_115])).
% 13.04/5.32  tff(c_86, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 13.04/5.32  tff(c_70, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 13.04/5.32  tff(c_24, plain, (![A_23]: (v1_relat_1(k2_funct_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_82])).
% 13.04/5.32  tff(c_74, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_192])).
% 13.04/5.32  tff(c_310, plain, (![A_94, B_95, C_96]: (k2_relset_1(A_94, B_95, C_96)=k2_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 13.04/5.32  tff(c_319, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_310])).
% 13.04/5.32  tff(c_326, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_319])).
% 13.04/5.32  tff(c_246, plain, (![A_87]: (k1_relat_1(k2_funct_1(A_87))=k2_relat_1(A_87) | ~v2_funct_1(A_87) | ~v1_funct_1(A_87) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.04/5.32  tff(c_10, plain, (![A_8]: (k9_relat_1(A_8, k1_relat_1(A_8))=k2_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.04/5.32  tff(c_16710, plain, (![A_690]: (k9_relat_1(k2_funct_1(A_690), k2_relat_1(A_690))=k2_relat_1(k2_funct_1(A_690)) | ~v1_relat_1(k2_funct_1(A_690)) | ~v2_funct_1(A_690) | ~v1_funct_1(A_690) | ~v1_relat_1(A_690))), inference(superposition, [status(thm), theory('equality')], [c_246, c_10])).
% 13.04/5.32  tff(c_16726, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_326, c_16710])).
% 13.04/5.32  tff(c_16733, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_70, c_16726])).
% 13.04/5.32  tff(c_16740, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_16733])).
% 13.04/5.32  tff(c_16743, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_16740])).
% 13.04/5.32  tff(c_16747, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_16743])).
% 13.04/5.32  tff(c_16749, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_16733])).
% 13.04/5.32  tff(c_177, plain, (![C_78, A_79, B_80]: (v4_relat_1(C_78, A_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 13.04/5.32  tff(c_188, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_82, c_177])).
% 13.04/5.32  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.04/5.32  tff(c_12, plain, (![A_9]: (k10_relat_1(A_9, k2_relat_1(A_9))=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.04/5.32  tff(c_340, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_326, c_12])).
% 13.04/5.32  tff(c_350, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_340])).
% 13.04/5.32  tff(c_16748, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_16733])).
% 13.04/5.32  tff(c_26, plain, (![B_25, A_24]: (k9_relat_1(k2_funct_1(B_25), A_24)=k10_relat_1(B_25, A_24) | ~v2_funct_1(B_25) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_90])).
% 13.04/5.32  tff(c_16755, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16748, c_26])).
% 13.04/5.32  tff(c_16762, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_70, c_350, c_16755])).
% 13.04/5.32  tff(c_56, plain, (![A_51]: (k6_relat_1(A_51)=k6_partfun1(A_51))), inference(cnfTransformation, [status(thm)], [f_156])).
% 13.04/5.32  tff(c_18, plain, (![B_20, A_19]: (k5_relat_1(B_20, k6_relat_1(A_19))=B_20 | ~r1_tarski(k2_relat_1(B_20), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.04/5.32  tff(c_90, plain, (![B_20, A_19]: (k5_relat_1(B_20, k6_partfun1(A_19))=B_20 | ~r1_tarski(k2_relat_1(B_20), A_19) | ~v1_relat_1(B_20))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_18])).
% 13.04/5.32  tff(c_16785, plain, (![A_19]: (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(A_19))=k2_funct_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), A_19) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_16762, c_90])).
% 13.04/5.32  tff(c_16811, plain, (![A_19]: (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(A_19))=k2_funct_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), A_19))), inference(demodulation, [status(thm), theory('equality')], [c_16749, c_16785])).
% 13.04/5.32  tff(c_52, plain, (![A_44]: (m1_subset_1(k6_partfun1(A_44), k1_zfmisc_1(k2_zfmisc_1(A_44, A_44))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.04/5.32  tff(c_112, plain, (![A_44]: (v1_relat_1(k6_partfun1(A_44)) | ~v1_relat_1(k2_zfmisc_1(A_44, A_44)))), inference(resolution, [status(thm)], [c_52, c_109])).
% 13.04/5.32  tff(c_121, plain, (![A_44]: (v1_relat_1(k6_partfun1(A_44)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_112])).
% 13.04/5.32  tff(c_34, plain, (![A_27]: (k5_relat_1(A_27, k2_funct_1(A_27))=k6_relat_1(k1_relat_1(A_27)) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_110])).
% 13.04/5.32  tff(c_87, plain, (![A_27]: (k5_relat_1(A_27, k2_funct_1(A_27))=k6_partfun1(k1_relat_1(A_27)) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_34])).
% 13.04/5.32  tff(c_527, plain, (![A_107, B_108, C_109]: (k5_relat_1(k5_relat_1(A_107, B_108), C_109)=k5_relat_1(A_107, k5_relat_1(B_108, C_109)) | ~v1_relat_1(C_109) | ~v1_relat_1(B_108) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.04/5.32  tff(c_19623, plain, (![A_766, C_767]: (k5_relat_1(k6_partfun1(k1_relat_1(A_766)), C_767)=k5_relat_1(A_766, k5_relat_1(k2_funct_1(A_766), C_767)) | ~v1_relat_1(C_767) | ~v1_relat_1(k2_funct_1(A_766)) | ~v1_relat_1(A_766) | ~v2_funct_1(A_766) | ~v1_funct_1(A_766) | ~v1_relat_1(A_766))), inference(superposition, [status(thm), theory('equality')], [c_87, c_527])).
% 13.04/5.32  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 13.04/5.32  tff(c_118, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_76, c_109])).
% 13.04/5.32  tff(c_127, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_118])).
% 13.04/5.32  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_192])).
% 13.04/5.32  tff(c_12379, plain, (![E_583, B_579, C_582, D_581, F_584, A_580]: (k1_partfun1(A_580, B_579, C_582, D_581, E_583, F_584)=k5_relat_1(E_583, F_584) | ~m1_subset_1(F_584, k1_zfmisc_1(k2_zfmisc_1(C_582, D_581))) | ~v1_funct_1(F_584) | ~m1_subset_1(E_583, k1_zfmisc_1(k2_zfmisc_1(A_580, B_579))) | ~v1_funct_1(E_583))), inference(cnfTransformation, [status(thm)], [f_154])).
% 13.04/5.32  tff(c_12389, plain, (![A_580, B_579, E_583]: (k1_partfun1(A_580, B_579, '#skF_2', '#skF_1', E_583, '#skF_4')=k5_relat_1(E_583, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_583, k1_zfmisc_1(k2_zfmisc_1(A_580, B_579))) | ~v1_funct_1(E_583))), inference(resolution, [status(thm)], [c_76, c_12379])).
% 13.04/5.32  tff(c_16128, plain, (![A_674, B_675, E_676]: (k1_partfun1(A_674, B_675, '#skF_2', '#skF_1', E_676, '#skF_4')=k5_relat_1(E_676, '#skF_4') | ~m1_subset_1(E_676, k1_zfmisc_1(k2_zfmisc_1(A_674, B_675))) | ~v1_funct_1(E_676))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_12389])).
% 13.04/5.32  tff(c_16140, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_16128])).
% 13.04/5.32  tff(c_16151, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_16140])).
% 13.04/5.32  tff(c_16175, plain, (![F_680, C_681, B_678, E_679, D_682, A_677]: (m1_subset_1(k1_partfun1(A_677, B_678, C_681, D_682, E_679, F_680), k1_zfmisc_1(k2_zfmisc_1(A_677, D_682))) | ~m1_subset_1(F_680, k1_zfmisc_1(k2_zfmisc_1(C_681, D_682))) | ~v1_funct_1(F_680) | ~m1_subset_1(E_679, k1_zfmisc_1(k2_zfmisc_1(A_677, B_678))) | ~v1_funct_1(E_679))), inference(cnfTransformation, [status(thm)], [f_140])).
% 13.04/5.32  tff(c_16205, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16151, c_16175])).
% 13.04/5.32  tff(c_16219, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_16205])).
% 13.04/5.32  tff(c_72, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 13.04/5.32  tff(c_9147, plain, (![D_447, C_448, A_449, B_450]: (D_447=C_448 | ~r2_relset_1(A_449, B_450, C_448, D_447) | ~m1_subset_1(D_447, k1_zfmisc_1(k2_zfmisc_1(A_449, B_450))) | ~m1_subset_1(C_448, k1_zfmisc_1(k2_zfmisc_1(A_449, B_450))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 13.04/5.32  tff(c_9159, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_72, c_9147])).
% 13.04/5.32  tff(c_9180, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_9159])).
% 13.04/5.32  tff(c_16590, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16219, c_16151, c_16151, c_9180])).
% 13.04/5.32  tff(c_203, plain, (![A_82]: (v4_relat_1(k6_partfun1(A_82), A_82))), inference(resolution, [status(thm)], [c_52, c_177])).
% 13.04/5.32  tff(c_14, plain, (![B_11, A_10]: (k7_relat_1(B_11, A_10)=B_11 | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.04/5.32  tff(c_206, plain, (![A_82]: (k7_relat_1(k6_partfun1(A_82), A_82)=k6_partfun1(A_82) | ~v1_relat_1(k6_partfun1(A_82)))), inference(resolution, [status(thm)], [c_203, c_14])).
% 13.04/5.32  tff(c_209, plain, (![A_82]: (k7_relat_1(k6_partfun1(A_82), A_82)=k6_partfun1(A_82))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_206])).
% 13.04/5.32  tff(c_20, plain, (![A_21, B_22]: (k5_relat_1(k6_relat_1(A_21), B_22)=k7_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.04/5.32  tff(c_89, plain, (![A_21, B_22]: (k5_relat_1(k6_partfun1(A_21), B_22)=k7_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_20])).
% 13.04/5.32  tff(c_559, plain, (![A_21, B_22, C_109]: (k5_relat_1(k6_partfun1(A_21), k5_relat_1(B_22, C_109))=k5_relat_1(k7_relat_1(B_22, A_21), C_109) | ~v1_relat_1(C_109) | ~v1_relat_1(B_22) | ~v1_relat_1(k6_partfun1(A_21)) | ~v1_relat_1(B_22))), inference(superposition, [status(thm), theory('equality')], [c_89, c_527])).
% 13.04/5.32  tff(c_589, plain, (![A_112, B_113, C_114]: (k5_relat_1(k6_partfun1(A_112), k5_relat_1(B_113, C_114))=k5_relat_1(k7_relat_1(B_113, A_112), C_114) | ~v1_relat_1(C_114) | ~v1_relat_1(B_113))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_559])).
% 13.04/5.32  tff(c_628, plain, (![A_21, A_112, B_22]: (k5_relat_1(k7_relat_1(k6_partfun1(A_21), A_112), B_22)=k5_relat_1(k6_partfun1(A_112), k7_relat_1(B_22, A_21)) | ~v1_relat_1(B_22) | ~v1_relat_1(k6_partfun1(A_21)) | ~v1_relat_1(B_22))), inference(superposition, [status(thm), theory('equality')], [c_89, c_589])).
% 13.04/5.32  tff(c_1366, plain, (![A_160, A_161, B_162]: (k5_relat_1(k7_relat_1(k6_partfun1(A_160), A_161), B_162)=k5_relat_1(k6_partfun1(A_161), k7_relat_1(B_162, A_160)) | ~v1_relat_1(B_162))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_628])).
% 13.04/5.32  tff(c_1479, plain, (![A_165, B_166]: (k5_relat_1(k6_partfun1(A_165), k7_relat_1(B_166, A_165))=k5_relat_1(k6_partfun1(A_165), B_166) | ~v1_relat_1(B_166))), inference(superposition, [status(thm), theory('equality')], [c_209, c_1366])).
% 13.04/5.32  tff(c_1536, plain, (![B_167, A_168]: (k7_relat_1(k7_relat_1(B_167, A_168), A_168)=k5_relat_1(k6_partfun1(A_168), B_167) | ~v1_relat_1(k7_relat_1(B_167, A_168)) | ~v1_relat_1(B_167))), inference(superposition, [status(thm), theory('equality')], [c_1479, c_89])).
% 13.04/5.32  tff(c_1542, plain, (![A_82]: (k7_relat_1(k7_relat_1(k6_partfun1(A_82), A_82), A_82)=k5_relat_1(k6_partfun1(A_82), k6_partfun1(A_82)) | ~v1_relat_1(k6_partfun1(A_82)) | ~v1_relat_1(k6_partfun1(A_82)))), inference(superposition, [status(thm), theory('equality')], [c_209, c_1536])).
% 13.04/5.32  tff(c_1550, plain, (![A_82]: (k5_relat_1(k6_partfun1(A_82), k6_partfun1(A_82))=k6_partfun1(A_82))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_121, c_209, c_209, c_1542])).
% 13.04/5.32  tff(c_58, plain, (![A_52]: (m1_subset_1(A_52, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_52), k2_relat_1(A_52)))) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_166])).
% 13.04/5.32  tff(c_331, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_326, c_58])).
% 13.04/5.32  tff(c_344, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_331])).
% 13.04/5.32  tff(c_38, plain, (![C_30, A_28, B_29]: (v4_relat_1(C_30, A_28) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 13.04/5.32  tff(c_377, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_344, c_38])).
% 13.04/5.32  tff(c_394, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_377, c_14])).
% 13.04/5.32  tff(c_397, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_394])).
% 13.04/5.32  tff(c_1540, plain, (k7_relat_1(k7_relat_1('#skF_3', k1_relat_1('#skF_3')), k1_relat_1('#skF_3'))=k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_397, c_1536])).
% 13.04/5.32  tff(c_1548, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_124, c_397, c_397, c_1540])).
% 13.04/5.32  tff(c_16, plain, (![A_12, B_16, C_18]: (k5_relat_1(k5_relat_1(A_12, B_16), C_18)=k5_relat_1(A_12, k5_relat_1(B_16, C_18)) | ~v1_relat_1(C_18) | ~v1_relat_1(B_16) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.04/5.32  tff(c_1648, plain, (![C_18]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k5_relat_1('#skF_3', C_18))=k5_relat_1('#skF_3', C_18) | ~v1_relat_1(C_18) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_1548, c_16])).
% 13.04/5.32  tff(c_2187, plain, (![C_207]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k5_relat_1('#skF_3', C_207))=k5_relat_1('#skF_3', C_207) | ~v1_relat_1(C_207))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_124, c_1648])).
% 13.04/5.32  tff(c_2225, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1(k1_relat_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_87, c_2187])).
% 13.04/5.32  tff(c_2248, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_70, c_1550, c_2225])).
% 13.04/5.32  tff(c_2251, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2248])).
% 13.04/5.32  tff(c_2285, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_2251])).
% 13.04/5.32  tff(c_2289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_2285])).
% 13.04/5.32  tff(c_2291, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2248])).
% 13.04/5.32  tff(c_22, plain, (![A_23]: (v1_funct_1(k2_funct_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_82])).
% 13.04/5.32  tff(c_2941, plain, (![A_223]: (k9_relat_1(k2_funct_1(A_223), k2_relat_1(A_223))=k2_relat_1(k2_funct_1(A_223)) | ~v1_relat_1(k2_funct_1(A_223)) | ~v2_funct_1(A_223) | ~v1_funct_1(A_223) | ~v1_relat_1(A_223))), inference(superposition, [status(thm), theory('equality')], [c_246, c_10])).
% 13.04/5.32  tff(c_2957, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_326, c_2941])).
% 13.04/5.32  tff(c_2964, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_70, c_2291, c_2957])).
% 13.04/5.32  tff(c_2968, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2964, c_26])).
% 13.04/5.32  tff(c_2975, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_70, c_350, c_2968])).
% 13.04/5.32  tff(c_277, plain, (![A_91]: (m1_subset_1(A_91, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_91), k2_relat_1(A_91)))) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_166])).
% 13.04/5.32  tff(c_36, plain, (![C_30, B_29, A_28]: (v5_relat_1(C_30, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 13.04/5.32  tff(c_297, plain, (![A_91]: (v5_relat_1(A_91, k2_relat_1(A_91)) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(resolution, [status(thm)], [c_277, c_36])).
% 13.04/5.32  tff(c_2995, plain, (v5_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2975, c_297])).
% 13.04/5.32  tff(c_3025, plain, (v5_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2291, c_2995])).
% 13.04/5.32  tff(c_3089, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3025])).
% 13.04/5.32  tff(c_3092, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_3089])).
% 13.04/5.32  tff(c_3096, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_3092])).
% 13.04/5.32  tff(c_3098, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3025])).
% 13.04/5.32  tff(c_30, plain, (![A_26]: (k1_relat_1(k2_funct_1(A_26))=k2_relat_1(A_26) | ~v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.04/5.32  tff(c_4024, plain, (![A_245]: (m1_subset_1(k2_funct_1(A_245), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_245), k2_relat_1(k2_funct_1(A_245))))) | ~v1_funct_1(k2_funct_1(A_245)) | ~v1_relat_1(k2_funct_1(A_245)) | ~v2_funct_1(A_245) | ~v1_funct_1(A_245) | ~v1_relat_1(A_245))), inference(superposition, [status(thm), theory('equality')], [c_30, c_277])).
% 13.04/5.32  tff(c_4062, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2975, c_4024])).
% 13.04/5.32  tff(c_4089, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_70, c_2291, c_3098, c_326, c_4062])).
% 13.04/5.32  tff(c_4148, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_4089, c_38])).
% 13.04/5.32  tff(c_258, plain, (![A_87, A_4]: (r1_tarski(k2_relat_1(A_87), A_4) | ~v4_relat_1(k2_funct_1(A_87), A_4) | ~v1_relat_1(k2_funct_1(A_87)) | ~v2_funct_1(A_87) | ~v1_funct_1(A_87) | ~v1_relat_1(A_87))), inference(superposition, [status(thm), theory('equality')], [c_246, c_6])).
% 13.04/5.32  tff(c_4156, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4148, c_258])).
% 13.04/5.32  tff(c_4162, plain, (r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_70, c_2291, c_326, c_4156])).
% 13.04/5.32  tff(c_192, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_188, c_14])).
% 13.04/5.32  tff(c_195, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_192])).
% 13.04/5.32  tff(c_334, plain, (![A_19]: (k5_relat_1('#skF_3', k6_partfun1(A_19))='#skF_3' | ~r1_tarski('#skF_2', A_19) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_326, c_90])).
% 13.04/5.32  tff(c_346, plain, (![A_19]: (k5_relat_1('#skF_3', k6_partfun1(A_19))='#skF_3' | ~r1_tarski('#skF_2', A_19))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_334])).
% 13.04/5.32  tff(c_622, plain, (![A_112, A_19]: (k5_relat_1(k7_relat_1('#skF_3', A_112), k6_partfun1(A_19))=k5_relat_1(k6_partfun1(A_112), '#skF_3') | ~v1_relat_1(k6_partfun1(A_19)) | ~v1_relat_1('#skF_3') | ~r1_tarski('#skF_2', A_19))), inference(superposition, [status(thm), theory('equality')], [c_346, c_589])).
% 13.04/5.32  tff(c_647, plain, (![A_115, A_116]: (k5_relat_1(k7_relat_1('#skF_3', A_115), k6_partfun1(A_116))=k5_relat_1(k6_partfun1(A_115), '#skF_3') | ~r1_tarski('#skF_2', A_116))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_121, c_622])).
% 13.04/5.32  tff(c_678, plain, (![A_117]: (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')=k5_relat_1('#skF_3', k6_partfun1(A_117)) | ~r1_tarski('#skF_2', A_117))), inference(superposition, [status(thm), theory('equality')], [c_195, c_647])).
% 13.04/5.32  tff(c_700, plain, (![A_117]: (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~r1_tarski('#skF_2', A_117) | ~r1_tarski('#skF_2', A_117))), inference(superposition, [status(thm), theory('equality')], [c_678, c_346])).
% 13.04/5.32  tff(c_730, plain, (![A_117]: (~r1_tarski('#skF_2', A_117) | ~r1_tarski('#skF_2', A_117))), inference(splitLeft, [status(thm)], [c_700])).
% 13.04/5.32  tff(c_4167, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_4162, c_730])).
% 13.04/5.32  tff(c_4171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4162, c_4167])).
% 13.04/5.32  tff(c_4172, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_700])).
% 13.04/5.32  tff(c_9095, plain, (![C_18]: (k5_relat_1(k6_partfun1('#skF_1'), k5_relat_1('#skF_3', C_18))=k5_relat_1('#skF_3', C_18) | ~v1_relat_1(C_18) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_partfun1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4172, c_16])).
% 13.04/5.32  tff(c_9722, plain, (![C_494]: (k5_relat_1(k6_partfun1('#skF_1'), k5_relat_1('#skF_3', C_494))=k5_relat_1('#skF_3', C_494) | ~v1_relat_1(C_494))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_124, c_9095])).
% 13.04/5.32  tff(c_9754, plain, (k5_relat_1(k6_partfun1('#skF_1'), k6_partfun1(k1_relat_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_87, c_9722])).
% 13.04/5.32  tff(c_9773, plain, (k5_relat_1(k6_partfun1('#skF_1'), k6_partfun1(k1_relat_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_70, c_9754])).
% 13.04/5.32  tff(c_9937, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_9773])).
% 13.04/5.32  tff(c_9967, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_9937])).
% 13.04/5.32  tff(c_9971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_9967])).
% 13.04/5.32  tff(c_9973, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_9773])).
% 13.04/5.32  tff(c_10500, plain, (![A_541]: (k9_relat_1(k2_funct_1(A_541), k2_relat_1(A_541))=k2_relat_1(k2_funct_1(A_541)) | ~v1_relat_1(k2_funct_1(A_541)) | ~v2_funct_1(A_541) | ~v1_funct_1(A_541) | ~v1_relat_1(A_541))), inference(superposition, [status(thm), theory('equality')], [c_246, c_10])).
% 13.04/5.32  tff(c_10516, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_326, c_10500])).
% 13.04/5.32  tff(c_10523, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_70, c_9973, c_10516])).
% 13.04/5.32  tff(c_10527, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10523, c_26])).
% 13.04/5.32  tff(c_10534, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_70, c_350, c_10527])).
% 13.04/5.32  tff(c_10554, plain, (v5_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_10534, c_297])).
% 13.04/5.32  tff(c_10584, plain, (v5_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9973, c_10554])).
% 13.04/5.32  tff(c_10672, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_10584])).
% 13.04/5.32  tff(c_10675, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_10672])).
% 13.04/5.32  tff(c_10679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_10675])).
% 13.04/5.32  tff(c_10681, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_10584])).
% 13.04/5.32  tff(c_12142, plain, (![A_574]: (m1_subset_1(k2_funct_1(A_574), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_574), k2_relat_1(k2_funct_1(A_574))))) | ~v1_funct_1(k2_funct_1(A_574)) | ~v1_relat_1(k2_funct_1(A_574)) | ~v2_funct_1(A_574) | ~v1_funct_1(A_574) | ~v1_relat_1(A_574))), inference(superposition, [status(thm), theory('equality')], [c_30, c_277])).
% 13.04/5.32  tff(c_12180, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10534, c_12142])).
% 13.04/5.32  tff(c_12207, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_70, c_9973, c_10681, c_326, c_12180])).
% 13.04/5.32  tff(c_12266, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_12207, c_38])).
% 13.04/5.32  tff(c_12274, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12266, c_258])).
% 13.04/5.32  tff(c_12280, plain, (r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_70, c_9973, c_326, c_12274])).
% 13.04/5.32  tff(c_302, plain, (![A_93]: (v4_relat_1(A_93, k1_relat_1(A_93)) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(resolution, [status(thm)], [c_277, c_38])).
% 13.04/5.32  tff(c_309, plain, (![A_93]: (k7_relat_1(A_93, k1_relat_1(A_93))=A_93 | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(resolution, [status(thm)], [c_302, c_14])).
% 13.04/5.32  tff(c_663, plain, (![A_116]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), '#skF_3')=k5_relat_1('#skF_3', k6_partfun1(A_116)) | ~r1_tarski('#skF_2', A_116) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_309, c_647])).
% 13.04/5.32  tff(c_9798, plain, (![A_501]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), '#skF_3')=k5_relat_1('#skF_3', k6_partfun1(A_501)) | ~r1_tarski('#skF_2', A_501))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_663])).
% 13.04/5.32  tff(c_9823, plain, (![A_501]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), '#skF_3')='#skF_3' | ~r1_tarski('#skF_2', A_501) | ~r1_tarski('#skF_2', A_501))), inference(superposition, [status(thm), theory('equality')], [c_9798, c_346])).
% 13.04/5.32  tff(c_9855, plain, (![A_501]: (~r1_tarski('#skF_2', A_501) | ~r1_tarski('#skF_2', A_501))), inference(splitLeft, [status(thm)], [c_9823])).
% 13.04/5.32  tff(c_12285, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_12280, c_9855])).
% 13.04/5.32  tff(c_12289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12280, c_12285])).
% 13.04/5.32  tff(c_12290, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_9823])).
% 13.04/5.32  tff(c_12328, plain, (![C_18]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k5_relat_1('#skF_3', C_18))=k5_relat_1('#skF_3', C_18) | ~v1_relat_1(C_18) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_12290, c_16])).
% 13.04/5.32  tff(c_12343, plain, (![C_18]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k5_relat_1('#skF_3', C_18))=k5_relat_1('#skF_3', C_18) | ~v1_relat_1(C_18))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_124, c_12328])).
% 13.04/5.32  tff(c_16611, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_1'))=k5_relat_1('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_16590, c_12343])).
% 13.04/5.32  tff(c_16624, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_1'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_16590, c_16611])).
% 13.04/5.32  tff(c_19673, plain, (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1')))=k6_partfun1('#skF_1') | ~v1_relat_1(k6_partfun1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_19623, c_16624])).
% 13.04/5.32  tff(c_19822, plain, (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1')))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_70, c_124, c_16749, c_121, c_19673])).
% 13.04/5.32  tff(c_20013, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16811, c_19822])).
% 13.04/5.32  tff(c_20151, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_20013])).
% 13.04/5.32  tff(c_20154, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_20151])).
% 13.04/5.32  tff(c_20158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_188, c_20154])).
% 13.04/5.32  tff(c_20160, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_20013])).
% 13.04/5.32  tff(c_189, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_177])).
% 13.04/5.32  tff(c_198, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_189, c_14])).
% 13.04/5.32  tff(c_201, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_198])).
% 13.04/5.32  tff(c_16779, plain, (v5_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_16762, c_297])).
% 13.04/5.32  tff(c_16807, plain, (v5_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16749, c_16779])).
% 13.04/5.32  tff(c_16847, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_16807])).
% 13.04/5.32  tff(c_16850, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_16847])).
% 13.04/5.32  tff(c_16854, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_16850])).
% 13.04/5.32  tff(c_16856, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_16807])).
% 13.04/5.32  tff(c_32, plain, (![A_27]: (k5_relat_1(k2_funct_1(A_27), A_27)=k6_relat_1(k2_relat_1(A_27)) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_110])).
% 13.04/5.32  tff(c_88, plain, (![A_27]: (k5_relat_1(k2_funct_1(A_27), A_27)=k6_partfun1(k2_relat_1(A_27)) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_32])).
% 13.04/5.32  tff(c_12387, plain, (![A_580, B_579, E_583]: (k1_partfun1(A_580, B_579, '#skF_1', '#skF_2', E_583, '#skF_3')=k5_relat_1(E_583, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_583, k1_zfmisc_1(k2_zfmisc_1(A_580, B_579))) | ~v1_funct_1(E_583))), inference(resolution, [status(thm)], [c_82, c_12379])).
% 13.04/5.32  tff(c_16354, plain, (![A_685, B_686, E_687]: (k1_partfun1(A_685, B_686, '#skF_1', '#skF_2', E_687, '#skF_3')=k5_relat_1(E_687, '#skF_3') | ~m1_subset_1(E_687, k1_zfmisc_1(k2_zfmisc_1(A_685, B_686))) | ~v1_funct_1(E_687))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_12387])).
% 13.04/5.32  tff(c_17257, plain, (![A_702]: (k1_partfun1(k1_relat_1(A_702), k2_relat_1(A_702), '#skF_1', '#skF_2', A_702, '#skF_3')=k5_relat_1(A_702, '#skF_3') | ~v1_funct_1(A_702) | ~v1_relat_1(A_702))), inference(resolution, [status(thm)], [c_58, c_16354])).
% 13.04/5.32  tff(c_9776, plain, (![D_500, C_499, B_496, E_497, A_495, F_498]: (v1_funct_1(k1_partfun1(A_495, B_496, C_499, D_500, E_497, F_498)) | ~m1_subset_1(F_498, k1_zfmisc_1(k2_zfmisc_1(C_499, D_500))) | ~v1_funct_1(F_498) | ~m1_subset_1(E_497, k1_zfmisc_1(k2_zfmisc_1(A_495, B_496))) | ~v1_funct_1(E_497))), inference(cnfTransformation, [status(thm)], [f_140])).
% 13.04/5.32  tff(c_9784, plain, (![A_495, B_496, E_497]: (v1_funct_1(k1_partfun1(A_495, B_496, '#skF_1', '#skF_2', E_497, '#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_497, k1_zfmisc_1(k2_zfmisc_1(A_495, B_496))) | ~v1_funct_1(E_497))), inference(resolution, [status(thm)], [c_82, c_9776])).
% 13.04/5.32  tff(c_12291, plain, (![A_575, B_576, E_577]: (v1_funct_1(k1_partfun1(A_575, B_576, '#skF_1', '#skF_2', E_577, '#skF_3')) | ~m1_subset_1(E_577, k1_zfmisc_1(k2_zfmisc_1(A_575, B_576))) | ~v1_funct_1(E_577))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_9784])).
% 13.04/5.32  tff(c_12310, plain, (![A_52]: (v1_funct_1(k1_partfun1(k1_relat_1(A_52), k2_relat_1(A_52), '#skF_1', '#skF_2', A_52, '#skF_3')) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(resolution, [status(thm)], [c_58, c_12291])).
% 13.04/5.32  tff(c_17709, plain, (![A_721]: (v1_funct_1(k5_relat_1(A_721, '#skF_3')) | ~v1_funct_1(A_721) | ~v1_relat_1(A_721) | ~v1_funct_1(A_721) | ~v1_relat_1(A_721))), inference(superposition, [status(thm), theory('equality')], [c_17257, c_12310])).
% 13.04/5.32  tff(c_17739, plain, (v1_funct_1(k6_partfun1(k2_relat_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_88, c_17709])).
% 13.04/5.32  tff(c_17757, plain, (v1_funct_1(k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_70, c_16749, c_16856, c_16749, c_16856, c_326, c_17739])).
% 13.04/5.32  tff(c_16148, plain, (![A_44]: (k1_partfun1(A_44, A_44, '#skF_2', '#skF_1', k6_partfun1(A_44), '#skF_4')=k5_relat_1(k6_partfun1(A_44), '#skF_4') | ~v1_funct_1(k6_partfun1(A_44)))), inference(resolution, [status(thm)], [c_52, c_16128])).
% 13.04/5.32  tff(c_17764, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_1', k6_partfun1('#skF_2'), '#skF_4')=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_17757, c_16148])).
% 13.04/5.32  tff(c_46, plain, (![D_41, B_39, A_38, F_43, E_42, C_40]: (m1_subset_1(k1_partfun1(A_38, B_39, C_40, D_41, E_42, F_43), k1_zfmisc_1(k2_zfmisc_1(A_38, D_41))) | ~m1_subset_1(F_43, k1_zfmisc_1(k2_zfmisc_1(C_40, D_41))) | ~v1_funct_1(F_43) | ~m1_subset_1(E_42, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_1(E_42))), inference(cnfTransformation, [status(thm)], [f_140])).
% 13.04/5.32  tff(c_18809, plain, (m1_subset_1(k5_relat_1(k6_partfun1('#skF_2'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1(k6_partfun1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_17764, c_46])).
% 13.04/5.32  tff(c_18816, plain, (m1_subset_1(k5_relat_1(k6_partfun1('#skF_2'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_17757, c_52, c_80, c_76, c_18809])).
% 13.04/5.32  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.04/5.32  tff(c_18948, plain, (v1_relat_1(k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_18816, c_2])).
% 13.04/5.32  tff(c_18994, plain, (v1_relat_1(k5_relat_1(k6_partfun1('#skF_2'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18948])).
% 13.04/5.32  tff(c_18990, plain, (v4_relat_1(k5_relat_1(k6_partfun1('#skF_2'), '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_18816, c_38])).
% 13.04/5.32  tff(c_19004, plain, (k7_relat_1(k5_relat_1(k6_partfun1('#skF_2'), '#skF_4'), '#skF_2')=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1(k5_relat_1(k6_partfun1('#skF_2'), '#skF_4'))), inference(resolution, [status(thm)], [c_18990, c_14])).
% 13.04/5.32  tff(c_19010, plain, (k7_relat_1(k5_relat_1(k6_partfun1('#skF_2'), '#skF_4'), '#skF_2')=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18994, c_19004])).
% 13.04/5.32  tff(c_19402, plain, (k7_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_2')=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_89, c_19010])).
% 13.04/5.32  tff(c_19406, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_201, c_201, c_19402])).
% 13.04/5.32  tff(c_19018, plain, (![A_754, C_755]: (k5_relat_1(k6_partfun1(k2_relat_1(A_754)), C_755)=k5_relat_1(k2_funct_1(A_754), k5_relat_1(A_754, C_755)) | ~v1_relat_1(C_755) | ~v1_relat_1(A_754) | ~v1_relat_1(k2_funct_1(A_754)) | ~v2_funct_1(A_754) | ~v1_funct_1(A_754) | ~v1_relat_1(A_754))), inference(superposition, [status(thm), theory('equality')], [c_88, c_527])).
% 13.04/5.32  tff(c_19164, plain, (![C_755]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_755))=k5_relat_1(k6_partfun1('#skF_2'), C_755) | ~v1_relat_1(C_755) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_326, c_19018])).
% 13.04/5.32  tff(c_23026, plain, (![C_849]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_849))=k5_relat_1(k6_partfun1('#skF_2'), C_849) | ~v1_relat_1(C_849))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_70, c_16749, c_124, c_19164])).
% 13.04/5.32  tff(c_23107, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_16590, c_23026])).
% 13.04/5.32  tff(c_23149, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_19406, c_23107])).
% 13.04/5.32  tff(c_28, plain, (![A_26]: (k2_relat_1(k2_funct_1(A_26))=k1_relat_1(A_26) | ~v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.04/5.32  tff(c_242, plain, (![B_85, A_86]: (k5_relat_1(B_85, k6_partfun1(A_86))=B_85 | ~r1_tarski(k2_relat_1(B_85), A_86) | ~v1_relat_1(B_85))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_18])).
% 13.04/5.32  tff(c_245, plain, (![A_26, A_86]: (k5_relat_1(k2_funct_1(A_26), k6_partfun1(A_86))=k2_funct_1(A_26) | ~r1_tarski(k1_relat_1(A_26), A_86) | ~v1_relat_1(k2_funct_1(A_26)) | ~v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_28, c_242])).
% 13.04/5.32  tff(c_23168, plain, (k2_funct_1('#skF_3')='#skF_4' | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_23149, c_245])).
% 13.04/5.32  tff(c_23193, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_70, c_16749, c_20160, c_23168])).
% 13.04/5.32  tff(c_23195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_23193])).
% 13.04/5.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.04/5.32  
% 13.04/5.32  Inference rules
% 13.04/5.32  ----------------------
% 13.04/5.32  #Ref     : 0
% 13.04/5.32  #Sup     : 5105
% 13.04/5.32  #Fact    : 0
% 13.04/5.32  #Define  : 0
% 13.04/5.32  #Split   : 36
% 13.04/5.32  #Chain   : 0
% 13.04/5.32  #Close   : 0
% 13.04/5.32  
% 13.04/5.32  Ordering : KBO
% 13.04/5.32  
% 13.04/5.32  Simplification rules
% 13.04/5.32  ----------------------
% 13.04/5.32  #Subsume      : 224
% 13.04/5.32  #Demod        : 6490
% 13.04/5.32  #Tautology    : 1927
% 13.04/5.32  #SimpNegUnit  : 4
% 13.04/5.32  #BackRed      : 132
% 13.04/5.32  
% 13.04/5.32  #Partial instantiations: 0
% 13.04/5.32  #Strategies tried      : 1
% 13.04/5.32  
% 13.04/5.32  Timing (in seconds)
% 13.04/5.32  ----------------------
% 13.04/5.32  Preprocessing        : 0.35
% 13.04/5.32  Parsing              : 0.19
% 13.04/5.32  CNF conversion       : 0.02
% 13.04/5.32  Main loop            : 4.15
% 13.04/5.32  Inferencing          : 1.18
% 13.04/5.32  Reduction            : 1.93
% 13.04/5.32  Demodulation         : 1.56
% 13.04/5.32  BG Simplification    : 0.11
% 13.04/5.32  Subsumption          : 0.70
% 13.04/5.32  Abstraction          : 0.16
% 13.04/5.32  MUC search           : 0.00
% 13.04/5.32  Cooper               : 0.00
% 13.04/5.32  Total                : 4.58
% 13.04/5.32  Index Insertion      : 0.00
% 13.04/5.32  Index Deletion       : 0.00
% 13.04/5.32  Index Matching       : 0.00
% 13.04/5.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
