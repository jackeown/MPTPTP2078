%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:40 EST 2020

% Result     : Theorem 10.87s
% Output     : CNFRefutation 11.09s
% Verified   : 
% Statistics : Number of formulae       :  333 (22131 expanded)
%              Number of leaves         :   59 (7741 expanded)
%              Depth                    :   27
%              Number of atoms          :  757 (68238 expanded)
%              Number of equality atoms :  247 (12668 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_263,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,C,B),B)
                & v2_funct_1(B) )
             => r2_relset_1(A,A,C,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).

tff(f_167,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_155,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_243,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_197,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_73,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_195,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_185,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_219,axiom,(
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

tff(f_95,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_151,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_159,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_173,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_235,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_120,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = A )
           => B = k6_relat_1(k1_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_130,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_145,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & v2_funct_1(B) )
           => k2_funct_1(k5_relat_1(A,B)) = k5_relat_1(k2_funct_1(B),k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).

tff(c_88,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_476,plain,(
    ! [A_125,B_126,D_127] :
      ( r2_relset_1(A_125,B_126,D_127,D_127)
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_482,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_476])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_206,plain,(
    ! [B_83,A_84] :
      ( v1_relat_1(B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_84))
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_212,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_88,c_206])).

tff(c_218,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_212])).

tff(c_92,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_90,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_533,plain,(
    ! [A_132,B_133,C_134] :
      ( k1_relset_1(A_132,B_133,C_134) = k1_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_541,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_533])).

tff(c_902,plain,(
    ! [A_176,B_177] :
      ( k1_relset_1(A_176,A_176,B_177) = A_176
      | ~ m1_subset_1(B_177,k1_zfmisc_1(k2_zfmisc_1(A_176,A_176)))
      | ~ v1_funct_2(B_177,A_176,A_176)
      | ~ v1_funct_1(B_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_908,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_902])).

tff(c_914,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_541,c_908])).

tff(c_38,plain,(
    ! [B_23,A_22] :
      ( k10_relat_1(B_23,k9_relat_1(B_23,A_22)) = A_22
      | ~ v2_funct_1(B_23)
      | ~ r1_tarski(A_22,k1_relat_1(B_23))
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_931,plain,(
    ! [A_22] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_22)) = A_22
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_22,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_914,c_38])).

tff(c_935,plain,(
    ! [A_22] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_22)) = A_22
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_22,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_92,c_931])).

tff(c_3982,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_935])).

tff(c_70,plain,(
    ! [A_60] : k6_relat_1(A_60) = k6_partfun1(A_60) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_24,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_103,plain,(
    ! [A_17] : k2_relat_1(k6_partfun1(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_24])).

tff(c_28,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_101,plain,(
    ! [A_20] : v1_relat_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_28])).

tff(c_135,plain,(
    ! [A_80] :
      ( k2_relat_1(A_80) != k1_xboole_0
      | k1_xboole_0 = A_80
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_141,plain,(
    ! [A_20] :
      ( k2_relat_1(k6_partfun1(A_20)) != k1_xboole_0
      | k6_partfun1(A_20) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_101,c_135])).

tff(c_156,plain,(
    ! [A_82] :
      ( k1_xboole_0 != A_82
      | k6_partfun1(A_82) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_141])).

tff(c_82,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_162,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_82])).

tff(c_241,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_98,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_96,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_94,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_84,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_4895,plain,(
    ! [D_391,C_387,E_386,A_388,B_390,F_389] :
      ( k1_partfun1(A_388,B_390,C_387,D_391,E_386,F_389) = k5_relat_1(E_386,F_389)
      | ~ m1_subset_1(F_389,k1_zfmisc_1(k2_zfmisc_1(C_387,D_391)))
      | ~ v1_funct_1(F_389)
      | ~ m1_subset_1(E_386,k1_zfmisc_1(k2_zfmisc_1(A_388,B_390)))
      | ~ v1_funct_1(E_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_4897,plain,(
    ! [A_388,B_390,E_386] :
      ( k1_partfun1(A_388,B_390,'#skF_1','#skF_1',E_386,'#skF_2') = k5_relat_1(E_386,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_386,k1_zfmisc_1(k2_zfmisc_1(A_388,B_390)))
      | ~ v1_funct_1(E_386) ) ),
    inference(resolution,[status(thm)],[c_94,c_4895])).

tff(c_5330,plain,(
    ! [A_408,B_409,E_410] :
      ( k1_partfun1(A_408,B_409,'#skF_1','#skF_1',E_410,'#skF_2') = k5_relat_1(E_410,'#skF_2')
      | ~ m1_subset_1(E_410,k1_zfmisc_1(k2_zfmisc_1(A_408,B_409)))
      | ~ v1_funct_1(E_410) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_4897])).

tff(c_5336,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_5330])).

tff(c_5342,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_5336])).

tff(c_86,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_4040,plain,(
    ! [D_343,C_344,A_345,B_346] :
      ( D_343 = C_344
      | ~ r2_relset_1(A_345,B_346,C_344,D_343)
      | ~ m1_subset_1(D_343,k1_zfmisc_1(k2_zfmisc_1(A_345,B_346)))
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(A_345,B_346))) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_4046,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_86,c_4040])).

tff(c_4057,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_4046])).

tff(c_4066,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4057])).

tff(c_5349,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5342,c_4066])).

tff(c_5360,plain,(
    ! [B_413,A_414,D_412,C_415,F_411,E_416] :
      ( m1_subset_1(k1_partfun1(A_414,B_413,C_415,D_412,E_416,F_411),k1_zfmisc_1(k2_zfmisc_1(A_414,D_412)))
      | ~ m1_subset_1(F_411,k1_zfmisc_1(k2_zfmisc_1(C_415,D_412)))
      | ~ v1_funct_1(F_411)
      | ~ m1_subset_1(E_416,k1_zfmisc_1(k2_zfmisc_1(A_414,B_413)))
      | ~ v1_funct_1(E_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_5404,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5342,c_5360])).

tff(c_5427,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_98,c_94,c_5404])).

tff(c_5430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5349,c_5427])).

tff(c_5431,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4057])).

tff(c_7277,plain,(
    ! [E_499,C_500,A_503,D_501,B_502] :
      ( k1_xboole_0 = C_500
      | v2_funct_1(D_501)
      | ~ v2_funct_1(k1_partfun1(A_503,B_502,B_502,C_500,D_501,E_499))
      | ~ m1_subset_1(E_499,k1_zfmisc_1(k2_zfmisc_1(B_502,C_500)))
      | ~ v1_funct_2(E_499,B_502,C_500)
      | ~ v1_funct_1(E_499)
      | ~ m1_subset_1(D_501,k1_zfmisc_1(k2_zfmisc_1(A_503,B_502)))
      | ~ v1_funct_2(D_501,A_503,B_502)
      | ~ v1_funct_1(D_501) ) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_7285,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5431,c_7277])).

tff(c_7296,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_98,c_96,c_94,c_84,c_7285])).

tff(c_7298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3982,c_241,c_7296])).

tff(c_7300,plain,(
    v2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_935])).

tff(c_36,plain,(
    ! [A_21] :
      ( v1_relat_1(k2_funct_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_315,plain,(
    ! [C_93,B_94,A_95] :
      ( v5_relat_1(C_93,B_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_323,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_315])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_374,plain,(
    ! [C_112,A_113,B_114] :
      ( v4_relat_1(C_112,A_113)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_382,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_374])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_391,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_382,c_16])).

tff(c_394,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_391])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_407,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_10])).

tff(c_411,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_407])).

tff(c_684,plain,(
    ! [A_149,B_150,C_151,D_152] :
      ( k7_relset_1(A_149,B_150,C_151,D_152) = k9_relat_1(C_151,D_152)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_690,plain,(
    ! [D_152] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_152) = k9_relat_1('#skF_3',D_152) ),
    inference(resolution,[status(thm)],[c_88,c_684])).

tff(c_850,plain,(
    ! [A_166,B_167,C_168] :
      ( k7_relset_1(A_166,B_167,C_168,A_166) = k2_relset_1(A_166,B_167,C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_854,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') = k2_relset_1('#skF_1','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_850])).

tff(c_858,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_690,c_854])).

tff(c_9802,plain,(
    ! [A_628,C_629,B_630] :
      ( k6_partfun1(A_628) = k5_relat_1(C_629,k2_funct_1(C_629))
      | k1_xboole_0 = B_630
      | ~ v2_funct_1(C_629)
      | k2_relset_1(A_628,B_630,C_629) != B_630
      | ~ m1_subset_1(C_629,k1_zfmisc_1(k2_zfmisc_1(A_628,B_630)))
      | ~ v1_funct_2(C_629,A_628,B_630)
      | ~ v1_funct_1(C_629) ) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_9806,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_1','#skF_3') != '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_9802])).

tff(c_9813,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | k2_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_858,c_7300,c_9806])).

tff(c_9814,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_9813])).

tff(c_9816,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9814])).

tff(c_209,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_94,c_206])).

tff(c_215,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_209])).

tff(c_381,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_94,c_374])).

tff(c_385,plain,
    ( k7_relat_1('#skF_2','#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_381,c_16])).

tff(c_388,plain,(
    k7_relat_1('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_385])).

tff(c_398,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_10])).

tff(c_402,plain,(
    k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_398])).

tff(c_540,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_94,c_533])).

tff(c_905,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_94,c_902])).

tff(c_911,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_540,c_905])).

tff(c_920,plain,(
    ! [A_22] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_22)) = A_22
      | ~ v2_funct_1('#skF_2')
      | ~ r1_tarski(A_22,'#skF_1')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_911,c_38])).

tff(c_953,plain,(
    ! [A_178] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_178)) = A_178
      | ~ r1_tarski(A_178,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_98,c_84,c_920])).

tff(c_970,plain,
    ( k10_relat_1('#skF_2',k2_relat_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_953])).

tff(c_977,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_970])).

tff(c_1989,plain,(
    ! [B_237,F_236,A_235,D_238,C_234,E_233] :
      ( k1_partfun1(A_235,B_237,C_234,D_238,E_233,F_236) = k5_relat_1(E_233,F_236)
      | ~ m1_subset_1(F_236,k1_zfmisc_1(k2_zfmisc_1(C_234,D_238)))
      | ~ v1_funct_1(F_236)
      | ~ m1_subset_1(E_233,k1_zfmisc_1(k2_zfmisc_1(A_235,B_237)))
      | ~ v1_funct_1(E_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_1991,plain,(
    ! [A_235,B_237,E_233] :
      ( k1_partfun1(A_235,B_237,'#skF_1','#skF_1',E_233,'#skF_2') = k5_relat_1(E_233,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_233,k1_zfmisc_1(k2_zfmisc_1(A_235,B_237)))
      | ~ v1_funct_1(E_233) ) ),
    inference(resolution,[status(thm)],[c_94,c_1989])).

tff(c_2274,plain,(
    ! [A_253,B_254,E_255] :
      ( k1_partfun1(A_253,B_254,'#skF_1','#skF_1',E_255,'#skF_2') = k5_relat_1(E_255,'#skF_2')
      | ~ m1_subset_1(E_255,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254)))
      | ~ v1_funct_1(E_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1991])).

tff(c_2280,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_2274])).

tff(c_2286,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2280])).

tff(c_978,plain,(
    ! [D_179,C_180,A_181,B_182] :
      ( D_179 = C_180
      | ~ r2_relset_1(A_181,B_182,C_180,D_179)
      | ~ m1_subset_1(D_179,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182)))
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_984,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_86,c_978])).

tff(c_995,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_984])).

tff(c_1040,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_995])).

tff(c_2359,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2286,c_1040])).

tff(c_2370,plain,(
    ! [B_259,A_260,E_262,F_257,C_261,D_258] :
      ( m1_subset_1(k1_partfun1(A_260,B_259,C_261,D_258,E_262,F_257),k1_zfmisc_1(k2_zfmisc_1(A_260,D_258)))
      | ~ m1_subset_1(F_257,k1_zfmisc_1(k2_zfmisc_1(C_261,D_258)))
      | ~ v1_funct_1(F_257)
      | ~ m1_subset_1(E_262,k1_zfmisc_1(k2_zfmisc_1(A_260,B_259)))
      | ~ v1_funct_1(E_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_2417,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2286,c_2370])).

tff(c_2444,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_98,c_94,c_2417])).

tff(c_2446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2359,c_2444])).

tff(c_2447,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_995])).

tff(c_3612,plain,(
    ! [B_322,E_318,A_320,F_321,C_319,D_323] :
      ( k1_partfun1(A_320,B_322,C_319,D_323,E_318,F_321) = k5_relat_1(E_318,F_321)
      | ~ m1_subset_1(F_321,k1_zfmisc_1(k2_zfmisc_1(C_319,D_323)))
      | ~ v1_funct_1(F_321)
      | ~ m1_subset_1(E_318,k1_zfmisc_1(k2_zfmisc_1(A_320,B_322)))
      | ~ v1_funct_1(E_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_3614,plain,(
    ! [A_320,B_322,E_318] :
      ( k1_partfun1(A_320,B_322,'#skF_1','#skF_1',E_318,'#skF_2') = k5_relat_1(E_318,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_318,k1_zfmisc_1(k2_zfmisc_1(A_320,B_322)))
      | ~ v1_funct_1(E_318) ) ),
    inference(resolution,[status(thm)],[c_94,c_3612])).

tff(c_3647,plain,(
    ! [A_325,B_326,E_327] :
      ( k1_partfun1(A_325,B_326,'#skF_1','#skF_1',E_327,'#skF_2') = k5_relat_1(E_327,'#skF_2')
      | ~ m1_subset_1(E_327,k1_zfmisc_1(k2_zfmisc_1(A_325,B_326)))
      | ~ v1_funct_1(E_327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_3614])).

tff(c_3653,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_3647])).

tff(c_3659,plain,(
    k5_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2447,c_3653])).

tff(c_40,plain,(
    ! [B_26,A_24] :
      ( k6_relat_1(k1_relat_1(B_26)) = B_26
      | k5_relat_1(A_24,B_26) != A_24
      | k2_relat_1(A_24) != k1_relat_1(B_26)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_99,plain,(
    ! [B_26,A_24] :
      ( k6_partfun1(k1_relat_1(B_26)) = B_26
      | k5_relat_1(A_24,B_26) != A_24
      | k2_relat_1(A_24) != k1_relat_1(B_26)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_40])).

tff(c_3665,plain,
    ( k6_partfun1(k1_relat_1('#skF_2')) = '#skF_2'
    | '#skF_2' != '#skF_3'
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3659,c_99])).

tff(c_3671,plain,
    ( k6_partfun1('#skF_1') = '#skF_2'
    | '#skF_2' != '#skF_3'
    | k2_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_92,c_215,c_98,c_911,c_911,c_3665])).

tff(c_3673,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3671])).

tff(c_12,plain,(
    ! [B_12,A_10] :
      ( k9_relat_1(B_12,k2_relat_1(A_10)) = k2_relat_1(k5_relat_1(A_10,B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_967,plain,(
    ! [A_10] :
      ( k10_relat_1('#skF_2',k2_relat_1(k5_relat_1(A_10,'#skF_2'))) = k2_relat_1(A_10)
      | ~ r1_tarski(k2_relat_1(A_10),'#skF_1')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_953])).

tff(c_976,plain,(
    ! [A_10] :
      ( k10_relat_1('#skF_2',k2_relat_1(k5_relat_1(A_10,'#skF_2'))) = k2_relat_1(A_10)
      | ~ r1_tarski(k2_relat_1(A_10),'#skF_1')
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_967])).

tff(c_3663,plain,
    ( k10_relat_1('#skF_2',k2_relat_1('#skF_2')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3659,c_976])).

tff(c_3669,plain,
    ( k10_relat_1('#skF_2',k2_relat_1('#skF_2')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_3663])).

tff(c_3787,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3669])).

tff(c_3803,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_3787])).

tff(c_3807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_323,c_3803])).

tff(c_3808,plain,(
    k10_relat_1('#skF_2',k2_relat_1('#skF_2')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3669])).

tff(c_14,plain,(
    ! [A_13] :
      ( k10_relat_1(A_13,k2_relat_1(A_13)) = k1_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3874,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3808,c_14])).

tff(c_3881,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_911,c_3874])).

tff(c_3883,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3673,c_3881])).

tff(c_3885,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3671])).

tff(c_3901,plain,(
    ! [A_4] :
      ( r1_tarski('#skF_1',A_4)
      | ~ v5_relat_1('#skF_3',A_4)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3885,c_6])).

tff(c_3956,plain,(
    ! [A_341] :
      ( r1_tarski('#skF_1',A_341)
      | ~ v5_relat_1('#skF_3',A_341) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_3901])).

tff(c_3959,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_323,c_3956])).

tff(c_3963,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_977,c_3959])).

tff(c_3964,plain,(
    k10_relat_1('#skF_2',k2_relat_1('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_970])).

tff(c_8273,plain,(
    ! [D_555,C_551,B_554,E_550,F_553,A_552] :
      ( k1_partfun1(A_552,B_554,C_551,D_555,E_550,F_553) = k5_relat_1(E_550,F_553)
      | ~ m1_subset_1(F_553,k1_zfmisc_1(k2_zfmisc_1(C_551,D_555)))
      | ~ v1_funct_1(F_553)
      | ~ m1_subset_1(E_550,k1_zfmisc_1(k2_zfmisc_1(A_552,B_554)))
      | ~ v1_funct_1(E_550) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_8275,plain,(
    ! [A_552,B_554,E_550] :
      ( k1_partfun1(A_552,B_554,'#skF_1','#skF_1',E_550,'#skF_2') = k5_relat_1(E_550,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_550,k1_zfmisc_1(k2_zfmisc_1(A_552,B_554)))
      | ~ v1_funct_1(E_550) ) ),
    inference(resolution,[status(thm)],[c_94,c_8273])).

tff(c_8550,plain,(
    ! [A_570,B_571,E_572] :
      ( k1_partfun1(A_570,B_571,'#skF_1','#skF_1',E_572,'#skF_2') = k5_relat_1(E_572,'#skF_2')
      | ~ m1_subset_1(E_572,k1_zfmisc_1(k2_zfmisc_1(A_570,B_571)))
      | ~ v1_funct_1(E_572) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_8275])).

tff(c_8556,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_8550])).

tff(c_8562,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_8556])).

tff(c_7406,plain,(
    ! [D_507,C_508,A_509,B_510] :
      ( D_507 = C_508
      | ~ r2_relset_1(A_509,B_510,C_508,D_507)
      | ~ m1_subset_1(D_507,k1_zfmisc_1(k2_zfmisc_1(A_509,B_510)))
      | ~ m1_subset_1(C_508,k1_zfmisc_1(k2_zfmisc_1(A_509,B_510))) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_7412,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_86,c_7406])).

tff(c_7423,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_7412])).

tff(c_7437,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_7423])).

tff(c_8655,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8562,c_7437])).

tff(c_8661,plain,(
    ! [B_576,D_575,A_577,F_574,E_579,C_578] :
      ( m1_subset_1(k1_partfun1(A_577,B_576,C_578,D_575,E_579,F_574),k1_zfmisc_1(k2_zfmisc_1(A_577,D_575)))
      | ~ m1_subset_1(F_574,k1_zfmisc_1(k2_zfmisc_1(C_578,D_575)))
      | ~ v1_funct_1(F_574)
      | ~ m1_subset_1(E_579,k1_zfmisc_1(k2_zfmisc_1(A_577,B_576)))
      | ~ v1_funct_1(E_579) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_8708,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8562,c_8661])).

tff(c_8738,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_98,c_94,c_8708])).

tff(c_8750,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8655,c_8738])).

tff(c_8751,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7423])).

tff(c_9595,plain,(
    ! [E_617,D_622,C_618,B_621,F_620,A_619] :
      ( k1_partfun1(A_619,B_621,C_618,D_622,E_617,F_620) = k5_relat_1(E_617,F_620)
      | ~ m1_subset_1(F_620,k1_zfmisc_1(k2_zfmisc_1(C_618,D_622)))
      | ~ v1_funct_1(F_620)
      | ~ m1_subset_1(E_617,k1_zfmisc_1(k2_zfmisc_1(A_619,B_621)))
      | ~ v1_funct_1(E_617) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_9597,plain,(
    ! [A_619,B_621,E_617] :
      ( k1_partfun1(A_619,B_621,'#skF_1','#skF_1',E_617,'#skF_2') = k5_relat_1(E_617,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_617,k1_zfmisc_1(k2_zfmisc_1(A_619,B_621)))
      | ~ v1_funct_1(E_617) ) ),
    inference(resolution,[status(thm)],[c_94,c_9595])).

tff(c_9958,plain,(
    ! [A_638,B_639,E_640] :
      ( k1_partfun1(A_638,B_639,'#skF_1','#skF_1',E_640,'#skF_2') = k5_relat_1(E_640,'#skF_2')
      | ~ m1_subset_1(E_640,k1_zfmisc_1(k2_zfmisc_1(A_638,B_639)))
      | ~ v1_funct_1(E_640) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_9597])).

tff(c_9964,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_9958])).

tff(c_9970,plain,(
    k5_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_8751,c_9964])).

tff(c_9974,plain,
    ( k10_relat_1('#skF_2',k2_relat_1('#skF_2')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9970,c_976])).

tff(c_9980,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_3964,c_9974])).

tff(c_9981,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_9816,c_9980])).

tff(c_9987,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_9981])).

tff(c_9991,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_323,c_9987])).

tff(c_9992,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_9814])).

tff(c_9993,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9814])).

tff(c_10001,plain,(
    ! [B_12] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_12)) = k9_relat_1(B_12,'#skF_1')
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9993,c_12])).

tff(c_10233,plain,(
    ! [B_656] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_656)) = k9_relat_1(B_656,'#skF_1')
      | ~ v1_relat_1(B_656) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_10001])).

tff(c_10272,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_relat_1(k6_partfun1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9992,c_10233])).

tff(c_10294,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_10272])).

tff(c_10505,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_10294])).

tff(c_10508,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_10505])).

tff(c_10512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_92,c_7300,c_10508])).

tff(c_10514,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_10294])).

tff(c_34,plain,(
    ! [A_21] :
      ( v1_funct_1(k2_funct_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3965,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_970])).

tff(c_492,plain,(
    ! [A_129] :
      ( k2_relat_1(k2_funct_1(A_129)) = k1_relat_1(A_129)
      | ~ v2_funct_1(A_129)
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_11299,plain,(
    ! [A_689] :
      ( k10_relat_1(k2_funct_1(A_689),k1_relat_1(A_689)) = k1_relat_1(k2_funct_1(A_689))
      | ~ v1_relat_1(k2_funct_1(A_689))
      | ~ v2_funct_1(A_689)
      | ~ v1_funct_1(A_689)
      | ~ v1_relat_1(A_689) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_14])).

tff(c_11308,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_914,c_11299])).

tff(c_11321,plain,(
    k10_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_92,c_7300,c_10514,c_11308])).

tff(c_10513,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10294])).

tff(c_44,plain,(
    ! [A_27] :
      ( k1_relat_1(k2_funct_1(A_27)) = k2_relat_1(A_27)
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_883,plain,(
    ! [B_171,A_172] :
      ( k10_relat_1(B_171,k9_relat_1(B_171,A_172)) = A_172
      | ~ v2_funct_1(B_171)
      | ~ r1_tarski(A_172,k1_relat_1(B_171))
      | ~ v1_funct_1(B_171)
      | ~ v1_relat_1(B_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_13562,plain,(
    ! [A_770,A_771] :
      ( k10_relat_1(k2_funct_1(A_770),k9_relat_1(k2_funct_1(A_770),A_771)) = A_771
      | ~ v2_funct_1(k2_funct_1(A_770))
      | ~ r1_tarski(A_771,k2_relat_1(A_770))
      | ~ v1_funct_1(k2_funct_1(A_770))
      | ~ v1_relat_1(k2_funct_1(A_770))
      | ~ v2_funct_1(A_770)
      | ~ v1_funct_1(A_770)
      | ~ v1_relat_1(A_770) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_883])).

tff(c_13589,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),'#skF_1') = '#skF_1'
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10513,c_13562])).

tff(c_13607,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_92,c_7300,c_10514,c_3965,c_9993,c_11321,c_13589])).

tff(c_13608,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_13607])).

tff(c_13611,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_13608])).

tff(c_13615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_92,c_7300,c_13611])).

tff(c_13617,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_13607])).

tff(c_42,plain,(
    ! [A_27] :
      ( k2_relat_1(k2_funct_1(A_27)) = k1_relat_1(A_27)
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_10013,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9993,c_14])).

tff(c_10025,plain,(
    k10_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_914,c_10013])).

tff(c_9995,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9993,c_858])).

tff(c_10052,plain,(
    ! [B_641,C_642,A_643] :
      ( k6_partfun1(B_641) = k5_relat_1(k2_funct_1(C_642),C_642)
      | k1_xboole_0 = B_641
      | ~ v2_funct_1(C_642)
      | k2_relset_1(A_643,B_641,C_642) != B_641
      | ~ m1_subset_1(C_642,k1_zfmisc_1(k2_zfmisc_1(A_643,B_641)))
      | ~ v1_funct_2(C_642,A_643,B_641)
      | ~ v1_funct_1(C_642) ) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_10056,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_1','#skF_3') != '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_10052])).

tff(c_10063,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | k2_relset_1('#skF_1','#skF_1','#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_7300,c_10056])).

tff(c_10064,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_1')
    | k2_relset_1('#skF_1','#skF_1','#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_10063])).

tff(c_10973,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9995,c_10064])).

tff(c_7315,plain,(
    ! [A_504] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_504)) = A_504
      | ~ r1_tarski(A_504,'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_935])).

tff(c_7329,plain,(
    ! [A_10] :
      ( k10_relat_1('#skF_3',k2_relat_1(k5_relat_1(A_10,'#skF_3'))) = k2_relat_1(A_10)
      | ~ r1_tarski(k2_relat_1(A_10),'#skF_1')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_7315])).

tff(c_7338,plain,(
    ! [A_10] :
      ( k10_relat_1('#skF_3',k2_relat_1(k5_relat_1(A_10,'#skF_3'))) = k2_relat_1(A_10)
      | ~ r1_tarski(k2_relat_1(A_10),'#skF_1')
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_7329])).

tff(c_10977,plain,
    ( k10_relat_1('#skF_3',k2_relat_1(k6_partfun1('#skF_1'))) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10973,c_7338])).

tff(c_10983,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10514,c_10025,c_103,c_10977])).

tff(c_11205,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_10983])).

tff(c_11209,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_11205])).

tff(c_11215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_92,c_7300,c_3965,c_914,c_11209])).

tff(c_11216,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10983])).

tff(c_11311,plain,
    ( k10_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_911,c_11299])).

tff(c_11323,plain,
    ( k10_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_98,c_84,c_11311])).

tff(c_11449,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_11323])).

tff(c_11452,plain,
    ( ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_11449])).

tff(c_11456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_98,c_84,c_11452])).

tff(c_11458,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_11323])).

tff(c_32,plain,(
    ! [A_21] :
      ( v2_funct_1(k2_funct_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_13616,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k1_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13607])).

tff(c_13653,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_13616])).

tff(c_13656,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_13653])).

tff(c_13660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_92,c_7300,c_13656])).

tff(c_13661,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13616])).

tff(c_10071,plain,(
    ! [A_644,B_645,E_646] :
      ( k1_partfun1(A_644,B_645,'#skF_1','#skF_1',E_646,'#skF_2') = k5_relat_1(E_646,'#skF_2')
      | ~ m1_subset_1(E_646,k1_zfmisc_1(k2_zfmisc_1(A_644,B_645)))
      | ~ v1_funct_1(E_646) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_9597])).

tff(c_10077,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_10071])).

tff(c_10083,plain,(
    k5_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_8751,c_10077])).

tff(c_9005,plain,(
    ! [B_590,A_591] :
      ( k5_relat_1(k2_funct_1(B_590),k2_funct_1(A_591)) = k2_funct_1(k5_relat_1(A_591,B_590))
      | ~ v2_funct_1(B_590)
      | ~ v2_funct_1(A_591)
      | ~ v1_funct_1(B_590)
      | ~ v1_relat_1(B_590)
      | ~ v1_funct_1(A_591)
      | ~ v1_relat_1(A_591) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_14753,plain,(
    ! [A_835,B_836] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_835))) = k2_funct_1(A_835)
      | k2_funct_1(k5_relat_1(A_835,B_836)) != k2_funct_1(B_836)
      | k2_relat_1(k2_funct_1(B_836)) != k1_relat_1(k2_funct_1(A_835))
      | ~ v1_funct_1(k2_funct_1(A_835))
      | ~ v1_relat_1(k2_funct_1(A_835))
      | ~ v1_funct_1(k2_funct_1(B_836))
      | ~ v1_relat_1(k2_funct_1(B_836))
      | ~ v2_funct_1(B_836)
      | ~ v2_funct_1(A_835)
      | ~ v1_funct_1(B_836)
      | ~ v1_relat_1(B_836)
      | ~ v1_funct_1(A_835)
      | ~ v1_relat_1(A_835) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9005,c_99])).

tff(c_14771,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3')
    | k2_relat_1(k2_funct_1('#skF_2')) != k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10083,c_14753])).

tff(c_14796,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k2_relat_1(k2_funct_1('#skF_2')) != '#skF_1'
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_92,c_215,c_98,c_7300,c_84,c_11458,c_10514,c_13617,c_13661,c_13661,c_14771])).

tff(c_14801,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_14796])).

tff(c_14804,plain,
    ( ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_14801])).

tff(c_14808,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_98,c_84,c_14804])).

tff(c_14809,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) != '#skF_1'
    | k6_partfun1('#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_14796])).

tff(c_14840,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_14809])).

tff(c_14843,plain,
    ( k1_relat_1('#skF_2') != '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_14840])).

tff(c_14846,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_98,c_84,c_911,c_14843])).

tff(c_14847,plain,(
    k6_partfun1('#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_14809])).

tff(c_14900,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14847,c_10973])).

tff(c_15089,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14900,c_99])).

tff(c_15104,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10514,c_13617,c_218,c_92,c_914,c_11216,c_14847,c_914,c_15089])).

tff(c_14902,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14847,c_82])).

tff(c_15106,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15104,c_14902])).

tff(c_15126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_15106])).

tff(c_15128,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_20,plain,(
    ! [A_16] :
      ( k1_relat_1(A_16) != k1_xboole_0
      | k1_xboole_0 = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_233,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_218,c_20])).

tff(c_16011,plain,
    ( k1_relat_1('#skF_3') != '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15128,c_15128,c_233])).

tff(c_16012,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_16011])).

tff(c_16622,plain,(
    ! [A_1002,B_1003,C_1004] :
      ( k1_relset_1(A_1002,B_1003,C_1004) = k1_relat_1(C_1004)
      | ~ m1_subset_1(C_1004,k1_zfmisc_1(k2_zfmisc_1(A_1002,B_1003))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_16631,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_16622])).

tff(c_17829,plain,(
    ! [A_1060,B_1061] :
      ( k1_relset_1(A_1060,A_1060,B_1061) = A_1060
      | ~ m1_subset_1(B_1061,k1_zfmisc_1(k2_zfmisc_1(A_1060,A_1060)))
      | ~ v1_funct_2(B_1061,A_1060,A_1060)
      | ~ v1_funct_1(B_1061) ) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_17835,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_17829])).

tff(c_17841,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_16631,c_17835])).

tff(c_17843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16012,c_17841])).

tff(c_17844,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16011])).

tff(c_15127,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_16010,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15128,c_15127])).

tff(c_17846,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17844,c_16010])).

tff(c_165,plain,(
    ! [A_82] :
      ( k2_relat_1(k1_xboole_0) = A_82
      | k1_xboole_0 != A_82 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_103])).

tff(c_15198,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15128,c_15128,c_165])).

tff(c_225,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_215,c_20])).

tff(c_15193,plain,
    ( k1_relat_1('#skF_2') != '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15128,c_15128,c_225])).

tff(c_15194,plain,(
    k1_relat_1('#skF_2') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_15193])).

tff(c_15581,plain,(
    ! [A_899,B_900,C_901] :
      ( k1_relset_1(A_899,B_900,C_901) = k1_relat_1(C_901)
      | ~ m1_subset_1(C_901,k1_zfmisc_1(k2_zfmisc_1(A_899,B_900))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_15588,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_94,c_15581])).

tff(c_15920,plain,(
    ! [A_937,B_938] :
      ( k1_relset_1(A_937,A_937,B_938) = A_937
      | ~ m1_subset_1(B_938,k1_zfmisc_1(k2_zfmisc_1(A_937,A_937)))
      | ~ v1_funct_2(B_938,A_937,A_937)
      | ~ v1_funct_1(B_938) ) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_15923,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_94,c_15920])).

tff(c_15929,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_15588,c_15923])).

tff(c_15931,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15194,c_15929])).

tff(c_15932,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_15193])).

tff(c_18,plain,(
    ! [A_16] :
      ( k2_relat_1(A_16) != k1_xboole_0
      | k1_xboole_0 = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_226,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_215,c_18])).

tff(c_15139,plain,
    ( k2_relat_1('#skF_2') != '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15128,c_15128,c_226])).

tff(c_15140,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_15139])).

tff(c_15934,plain,(
    k2_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15932,c_15140])).

tff(c_15956,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15198,c_15934])).

tff(c_15957,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_15139])).

tff(c_15961,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15957,c_94])).

tff(c_18124,plain,(
    ! [A_1101,B_1102,D_1103] :
      ( r2_relset_1(A_1101,B_1102,D_1103,D_1103)
      | ~ m1_subset_1(D_1103,k1_zfmisc_1(k2_zfmisc_1(A_1101,B_1102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_18126,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_15961,c_18124])).

tff(c_18130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17846,c_18126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.87/4.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.09/4.20  
% 11.09/4.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.09/4.21  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.09/4.21  
% 11.09/4.21  %Foreground sorts:
% 11.09/4.21  
% 11.09/4.21  
% 11.09/4.21  %Background operators:
% 11.09/4.21  
% 11.09/4.21  
% 11.09/4.21  %Foreground operators:
% 11.09/4.21  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.09/4.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.09/4.21  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.09/4.21  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.09/4.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.09/4.21  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 11.09/4.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 11.09/4.21  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 11.09/4.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.09/4.21  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.09/4.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.09/4.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.09/4.21  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 11.09/4.21  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.09/4.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.09/4.21  tff('#skF_2', type, '#skF_2': $i).
% 11.09/4.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.09/4.21  tff('#skF_3', type, '#skF_3': $i).
% 11.09/4.21  tff('#skF_1', type, '#skF_1': $i).
% 11.09/4.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.09/4.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.09/4.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.09/4.21  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 11.09/4.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.09/4.21  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 11.09/4.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.09/4.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.09/4.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.09/4.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.09/4.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.09/4.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.09/4.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.09/4.21  
% 11.09/4.25  tff(f_263, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r2_relset_1(A, A, k1_partfun1(A, A, A, A, C, B), B) & v2_funct_1(B)) => r2_relset_1(A, A, C, k6_partfun1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_funct_2)).
% 11.09/4.25  tff(f_167, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 11.09/4.25  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.09/4.25  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.09/4.25  tff(f_155, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.09/4.25  tff(f_243, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 11.09/4.25  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 11.09/4.25  tff(f_197, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 11.09/4.25  tff(f_73, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 11.09/4.25  tff(f_83, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 11.09/4.25  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 11.09/4.25  tff(f_195, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 11.09/4.25  tff(f_185, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 11.09/4.25  tff(f_219, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 11.09/4.25  tff(f_95, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 11.09/4.25  tff(f_151, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.09/4.25  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 11.09/4.25  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 11.09/4.25  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 11.09/4.25  tff(f_159, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 11.09/4.25  tff(f_173, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 11.09/4.25  tff(f_235, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 11.09/4.25  tff(f_120, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_funct_1)).
% 11.09/4.25  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 11.09/4.25  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 11.09/4.25  tff(f_130, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 11.09/4.25  tff(f_145, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(A) & v2_funct_1(B)) => (k2_funct_1(k5_relat_1(A, B)) = k5_relat_1(k2_funct_1(B), k2_funct_1(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_funct_1)).
% 11.09/4.25  tff(c_88, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_263])).
% 11.09/4.25  tff(c_476, plain, (![A_125, B_126, D_127]: (r2_relset_1(A_125, B_126, D_127, D_127) | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.09/4.25  tff(c_482, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_88, c_476])).
% 11.09/4.25  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.09/4.25  tff(c_206, plain, (![B_83, A_84]: (v1_relat_1(B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_84)) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.09/4.25  tff(c_212, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_88, c_206])).
% 11.09/4.25  tff(c_218, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_212])).
% 11.09/4.25  tff(c_92, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_263])).
% 11.09/4.25  tff(c_90, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_263])).
% 11.09/4.25  tff(c_533, plain, (![A_132, B_133, C_134]: (k1_relset_1(A_132, B_133, C_134)=k1_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 11.09/4.25  tff(c_541, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_533])).
% 11.09/4.25  tff(c_902, plain, (![A_176, B_177]: (k1_relset_1(A_176, A_176, B_177)=A_176 | ~m1_subset_1(B_177, k1_zfmisc_1(k2_zfmisc_1(A_176, A_176))) | ~v1_funct_2(B_177, A_176, A_176) | ~v1_funct_1(B_177))), inference(cnfTransformation, [status(thm)], [f_243])).
% 11.09/4.25  tff(c_908, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_902])).
% 11.09/4.25  tff(c_914, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_541, c_908])).
% 11.09/4.25  tff(c_38, plain, (![B_23, A_22]: (k10_relat_1(B_23, k9_relat_1(B_23, A_22))=A_22 | ~v2_funct_1(B_23) | ~r1_tarski(A_22, k1_relat_1(B_23)) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.09/4.25  tff(c_931, plain, (![A_22]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_22))=A_22 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_22, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_914, c_38])).
% 11.09/4.25  tff(c_935, plain, (![A_22]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_22))=A_22 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_22, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_92, c_931])).
% 11.09/4.25  tff(c_3982, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_935])).
% 11.09/4.25  tff(c_70, plain, (![A_60]: (k6_relat_1(A_60)=k6_partfun1(A_60))), inference(cnfTransformation, [status(thm)], [f_197])).
% 11.09/4.25  tff(c_24, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.09/4.25  tff(c_103, plain, (![A_17]: (k2_relat_1(k6_partfun1(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_24])).
% 11.09/4.25  tff(c_28, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.09/4.25  tff(c_101, plain, (![A_20]: (v1_relat_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_28])).
% 11.09/4.25  tff(c_135, plain, (![A_80]: (k2_relat_1(A_80)!=k1_xboole_0 | k1_xboole_0=A_80 | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.09/4.25  tff(c_141, plain, (![A_20]: (k2_relat_1(k6_partfun1(A_20))!=k1_xboole_0 | k6_partfun1(A_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_101, c_135])).
% 11.09/4.25  tff(c_156, plain, (![A_82]: (k1_xboole_0!=A_82 | k6_partfun1(A_82)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_103, c_141])).
% 11.09/4.25  tff(c_82, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_263])).
% 11.09/4.25  tff(c_162, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_156, c_82])).
% 11.09/4.25  tff(c_241, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_162])).
% 11.09/4.25  tff(c_98, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_263])).
% 11.09/4.25  tff(c_96, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_263])).
% 11.09/4.25  tff(c_94, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_263])).
% 11.09/4.25  tff(c_84, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_263])).
% 11.09/4.25  tff(c_4895, plain, (![D_391, C_387, E_386, A_388, B_390, F_389]: (k1_partfun1(A_388, B_390, C_387, D_391, E_386, F_389)=k5_relat_1(E_386, F_389) | ~m1_subset_1(F_389, k1_zfmisc_1(k2_zfmisc_1(C_387, D_391))) | ~v1_funct_1(F_389) | ~m1_subset_1(E_386, k1_zfmisc_1(k2_zfmisc_1(A_388, B_390))) | ~v1_funct_1(E_386))), inference(cnfTransformation, [status(thm)], [f_195])).
% 11.09/4.25  tff(c_4897, plain, (![A_388, B_390, E_386]: (k1_partfun1(A_388, B_390, '#skF_1', '#skF_1', E_386, '#skF_2')=k5_relat_1(E_386, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_386, k1_zfmisc_1(k2_zfmisc_1(A_388, B_390))) | ~v1_funct_1(E_386))), inference(resolution, [status(thm)], [c_94, c_4895])).
% 11.09/4.25  tff(c_5330, plain, (![A_408, B_409, E_410]: (k1_partfun1(A_408, B_409, '#skF_1', '#skF_1', E_410, '#skF_2')=k5_relat_1(E_410, '#skF_2') | ~m1_subset_1(E_410, k1_zfmisc_1(k2_zfmisc_1(A_408, B_409))) | ~v1_funct_1(E_410))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_4897])).
% 11.09/4.25  tff(c_5336, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_5330])).
% 11.09/4.25  tff(c_5342, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_5336])).
% 11.09/4.25  tff(c_86, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_263])).
% 11.09/4.25  tff(c_4040, plain, (![D_343, C_344, A_345, B_346]: (D_343=C_344 | ~r2_relset_1(A_345, B_346, C_344, D_343) | ~m1_subset_1(D_343, k1_zfmisc_1(k2_zfmisc_1(A_345, B_346))) | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(A_345, B_346))))), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.09/4.25  tff(c_4046, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_86, c_4040])).
% 11.09/4.25  tff(c_4057, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_4046])).
% 11.09/4.25  tff(c_4066, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_4057])).
% 11.09/4.25  tff(c_5349, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5342, c_4066])).
% 11.09/4.25  tff(c_5360, plain, (![B_413, A_414, D_412, C_415, F_411, E_416]: (m1_subset_1(k1_partfun1(A_414, B_413, C_415, D_412, E_416, F_411), k1_zfmisc_1(k2_zfmisc_1(A_414, D_412))) | ~m1_subset_1(F_411, k1_zfmisc_1(k2_zfmisc_1(C_415, D_412))) | ~v1_funct_1(F_411) | ~m1_subset_1(E_416, k1_zfmisc_1(k2_zfmisc_1(A_414, B_413))) | ~v1_funct_1(E_416))), inference(cnfTransformation, [status(thm)], [f_185])).
% 11.09/4.25  tff(c_5404, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5342, c_5360])).
% 11.09/4.25  tff(c_5427, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_98, c_94, c_5404])).
% 11.09/4.25  tff(c_5430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5349, c_5427])).
% 11.09/4.25  tff(c_5431, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_4057])).
% 11.09/4.25  tff(c_7277, plain, (![E_499, C_500, A_503, D_501, B_502]: (k1_xboole_0=C_500 | v2_funct_1(D_501) | ~v2_funct_1(k1_partfun1(A_503, B_502, B_502, C_500, D_501, E_499)) | ~m1_subset_1(E_499, k1_zfmisc_1(k2_zfmisc_1(B_502, C_500))) | ~v1_funct_2(E_499, B_502, C_500) | ~v1_funct_1(E_499) | ~m1_subset_1(D_501, k1_zfmisc_1(k2_zfmisc_1(A_503, B_502))) | ~v1_funct_2(D_501, A_503, B_502) | ~v1_funct_1(D_501))), inference(cnfTransformation, [status(thm)], [f_219])).
% 11.09/4.25  tff(c_7285, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1('#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5431, c_7277])).
% 11.09/4.25  tff(c_7296, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_98, c_96, c_94, c_84, c_7285])).
% 11.09/4.25  tff(c_7298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3982, c_241, c_7296])).
% 11.09/4.25  tff(c_7300, plain, (v2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_935])).
% 11.09/4.25  tff(c_36, plain, (![A_21]: (v1_relat_1(k2_funct_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_95])).
% 11.09/4.25  tff(c_315, plain, (![C_93, B_94, A_95]: (v5_relat_1(C_93, B_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.09/4.25  tff(c_323, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_88, c_315])).
% 11.09/4.25  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.09/4.25  tff(c_374, plain, (![C_112, A_113, B_114]: (v4_relat_1(C_112, A_113) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.09/4.25  tff(c_382, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_88, c_374])).
% 11.09/4.25  tff(c_16, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.09/4.25  tff(c_391, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_382, c_16])).
% 11.09/4.25  tff(c_394, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_218, c_391])).
% 11.09/4.25  tff(c_10, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.09/4.25  tff(c_407, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_394, c_10])).
% 11.09/4.25  tff(c_411, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_218, c_407])).
% 11.09/4.25  tff(c_684, plain, (![A_149, B_150, C_151, D_152]: (k7_relset_1(A_149, B_150, C_151, D_152)=k9_relat_1(C_151, D_152) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_159])).
% 11.09/4.25  tff(c_690, plain, (![D_152]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_152)=k9_relat_1('#skF_3', D_152))), inference(resolution, [status(thm)], [c_88, c_684])).
% 11.09/4.25  tff(c_850, plain, (![A_166, B_167, C_168]: (k7_relset_1(A_166, B_167, C_168, A_166)=k2_relset_1(A_166, B_167, C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_173])).
% 11.09/4.25  tff(c_854, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')=k2_relset_1('#skF_1', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_88, c_850])).
% 11.09/4.25  tff(c_858, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_411, c_690, c_854])).
% 11.09/4.25  tff(c_9802, plain, (![A_628, C_629, B_630]: (k6_partfun1(A_628)=k5_relat_1(C_629, k2_funct_1(C_629)) | k1_xboole_0=B_630 | ~v2_funct_1(C_629) | k2_relset_1(A_628, B_630, C_629)!=B_630 | ~m1_subset_1(C_629, k1_zfmisc_1(k2_zfmisc_1(A_628, B_630))) | ~v1_funct_2(C_629, A_628, B_630) | ~v1_funct_1(C_629))), inference(cnfTransformation, [status(thm)], [f_235])).
% 11.09/4.25  tff(c_9806, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_1', '#skF_3')!='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_9802])).
% 11.09/4.25  tff(c_9813, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | k2_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_858, c_7300, c_9806])).
% 11.09/4.25  tff(c_9814, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_241, c_9813])).
% 11.09/4.25  tff(c_9816, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_9814])).
% 11.09/4.25  tff(c_209, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_94, c_206])).
% 11.09/4.25  tff(c_215, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_209])).
% 11.09/4.25  tff(c_381, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_94, c_374])).
% 11.09/4.25  tff(c_385, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_381, c_16])).
% 11.09/4.25  tff(c_388, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_215, c_385])).
% 11.09/4.25  tff(c_398, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_388, c_10])).
% 11.09/4.25  tff(c_402, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_398])).
% 11.09/4.25  tff(c_540, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_94, c_533])).
% 11.09/4.25  tff(c_905, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_94, c_902])).
% 11.09/4.25  tff(c_911, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_540, c_905])).
% 11.09/4.25  tff(c_920, plain, (![A_22]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_22))=A_22 | ~v2_funct_1('#skF_2') | ~r1_tarski(A_22, '#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_911, c_38])).
% 11.09/4.25  tff(c_953, plain, (![A_178]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_178))=A_178 | ~r1_tarski(A_178, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_98, c_84, c_920])).
% 11.09/4.25  tff(c_970, plain, (k10_relat_1('#skF_2', k2_relat_1('#skF_2'))='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_402, c_953])).
% 11.09/4.25  tff(c_977, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_970])).
% 11.09/4.25  tff(c_1989, plain, (![B_237, F_236, A_235, D_238, C_234, E_233]: (k1_partfun1(A_235, B_237, C_234, D_238, E_233, F_236)=k5_relat_1(E_233, F_236) | ~m1_subset_1(F_236, k1_zfmisc_1(k2_zfmisc_1(C_234, D_238))) | ~v1_funct_1(F_236) | ~m1_subset_1(E_233, k1_zfmisc_1(k2_zfmisc_1(A_235, B_237))) | ~v1_funct_1(E_233))), inference(cnfTransformation, [status(thm)], [f_195])).
% 11.09/4.25  tff(c_1991, plain, (![A_235, B_237, E_233]: (k1_partfun1(A_235, B_237, '#skF_1', '#skF_1', E_233, '#skF_2')=k5_relat_1(E_233, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_233, k1_zfmisc_1(k2_zfmisc_1(A_235, B_237))) | ~v1_funct_1(E_233))), inference(resolution, [status(thm)], [c_94, c_1989])).
% 11.09/4.25  tff(c_2274, plain, (![A_253, B_254, E_255]: (k1_partfun1(A_253, B_254, '#skF_1', '#skF_1', E_255, '#skF_2')=k5_relat_1(E_255, '#skF_2') | ~m1_subset_1(E_255, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))) | ~v1_funct_1(E_255))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1991])).
% 11.09/4.25  tff(c_2280, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_2274])).
% 11.09/4.25  tff(c_2286, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_2280])).
% 11.09/4.25  tff(c_978, plain, (![D_179, C_180, A_181, B_182]: (D_179=C_180 | ~r2_relset_1(A_181, B_182, C_180, D_179) | ~m1_subset_1(D_179, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.09/4.25  tff(c_984, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_86, c_978])).
% 11.09/4.25  tff(c_995, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_984])).
% 11.09/4.25  tff(c_1040, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_995])).
% 11.09/4.25  tff(c_2359, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2286, c_1040])).
% 11.09/4.25  tff(c_2370, plain, (![B_259, A_260, E_262, F_257, C_261, D_258]: (m1_subset_1(k1_partfun1(A_260, B_259, C_261, D_258, E_262, F_257), k1_zfmisc_1(k2_zfmisc_1(A_260, D_258))) | ~m1_subset_1(F_257, k1_zfmisc_1(k2_zfmisc_1(C_261, D_258))) | ~v1_funct_1(F_257) | ~m1_subset_1(E_262, k1_zfmisc_1(k2_zfmisc_1(A_260, B_259))) | ~v1_funct_1(E_262))), inference(cnfTransformation, [status(thm)], [f_185])).
% 11.09/4.25  tff(c_2417, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2286, c_2370])).
% 11.09/4.25  tff(c_2444, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_98, c_94, c_2417])).
% 11.09/4.25  tff(c_2446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2359, c_2444])).
% 11.09/4.25  tff(c_2447, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_995])).
% 11.09/4.25  tff(c_3612, plain, (![B_322, E_318, A_320, F_321, C_319, D_323]: (k1_partfun1(A_320, B_322, C_319, D_323, E_318, F_321)=k5_relat_1(E_318, F_321) | ~m1_subset_1(F_321, k1_zfmisc_1(k2_zfmisc_1(C_319, D_323))) | ~v1_funct_1(F_321) | ~m1_subset_1(E_318, k1_zfmisc_1(k2_zfmisc_1(A_320, B_322))) | ~v1_funct_1(E_318))), inference(cnfTransformation, [status(thm)], [f_195])).
% 11.09/4.25  tff(c_3614, plain, (![A_320, B_322, E_318]: (k1_partfun1(A_320, B_322, '#skF_1', '#skF_1', E_318, '#skF_2')=k5_relat_1(E_318, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_318, k1_zfmisc_1(k2_zfmisc_1(A_320, B_322))) | ~v1_funct_1(E_318))), inference(resolution, [status(thm)], [c_94, c_3612])).
% 11.09/4.25  tff(c_3647, plain, (![A_325, B_326, E_327]: (k1_partfun1(A_325, B_326, '#skF_1', '#skF_1', E_327, '#skF_2')=k5_relat_1(E_327, '#skF_2') | ~m1_subset_1(E_327, k1_zfmisc_1(k2_zfmisc_1(A_325, B_326))) | ~v1_funct_1(E_327))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_3614])).
% 11.09/4.25  tff(c_3653, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_3647])).
% 11.09/4.25  tff(c_3659, plain, (k5_relat_1('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_2447, c_3653])).
% 11.09/4.25  tff(c_40, plain, (![B_26, A_24]: (k6_relat_1(k1_relat_1(B_26))=B_26 | k5_relat_1(A_24, B_26)!=A_24 | k2_relat_1(A_24)!=k1_relat_1(B_26) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.09/4.25  tff(c_99, plain, (![B_26, A_24]: (k6_partfun1(k1_relat_1(B_26))=B_26 | k5_relat_1(A_24, B_26)!=A_24 | k2_relat_1(A_24)!=k1_relat_1(B_26) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_40])).
% 11.09/4.25  tff(c_3665, plain, (k6_partfun1(k1_relat_1('#skF_2'))='#skF_2' | '#skF_2'!='#skF_3' | k2_relat_1('#skF_3')!=k1_relat_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3659, c_99])).
% 11.09/4.25  tff(c_3671, plain, (k6_partfun1('#skF_1')='#skF_2' | '#skF_2'!='#skF_3' | k2_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_218, c_92, c_215, c_98, c_911, c_911, c_3665])).
% 11.09/4.25  tff(c_3673, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_3671])).
% 11.09/4.25  tff(c_12, plain, (![B_12, A_10]: (k9_relat_1(B_12, k2_relat_1(A_10))=k2_relat_1(k5_relat_1(A_10, B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.09/4.25  tff(c_967, plain, (![A_10]: (k10_relat_1('#skF_2', k2_relat_1(k5_relat_1(A_10, '#skF_2')))=k2_relat_1(A_10) | ~r1_tarski(k2_relat_1(A_10), '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_12, c_953])).
% 11.09/4.25  tff(c_976, plain, (![A_10]: (k10_relat_1('#skF_2', k2_relat_1(k5_relat_1(A_10, '#skF_2')))=k2_relat_1(A_10) | ~r1_tarski(k2_relat_1(A_10), '#skF_1') | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_967])).
% 11.09/4.25  tff(c_3663, plain, (k10_relat_1('#skF_2', k2_relat_1('#skF_2'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3659, c_976])).
% 11.09/4.25  tff(c_3669, plain, (k10_relat_1('#skF_2', k2_relat_1('#skF_2'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_218, c_3663])).
% 11.09/4.25  tff(c_3787, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_3669])).
% 11.09/4.25  tff(c_3803, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_3787])).
% 11.09/4.25  tff(c_3807, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_218, c_323, c_3803])).
% 11.09/4.25  tff(c_3808, plain, (k10_relat_1('#skF_2', k2_relat_1('#skF_2'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_3669])).
% 11.09/4.25  tff(c_14, plain, (![A_13]: (k10_relat_1(A_13, k2_relat_1(A_13))=k1_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.09/4.25  tff(c_3874, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3808, c_14])).
% 11.09/4.25  tff(c_3881, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_215, c_911, c_3874])).
% 11.09/4.25  tff(c_3883, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3673, c_3881])).
% 11.09/4.25  tff(c_3885, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_3671])).
% 11.09/4.25  tff(c_3901, plain, (![A_4]: (r1_tarski('#skF_1', A_4) | ~v5_relat_1('#skF_3', A_4) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3885, c_6])).
% 11.09/4.25  tff(c_3956, plain, (![A_341]: (r1_tarski('#skF_1', A_341) | ~v5_relat_1('#skF_3', A_341))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_3901])).
% 11.09/4.25  tff(c_3959, plain, (r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_323, c_3956])).
% 11.09/4.25  tff(c_3963, plain, $false, inference(negUnitSimplification, [status(thm)], [c_977, c_3959])).
% 11.09/4.25  tff(c_3964, plain, (k10_relat_1('#skF_2', k2_relat_1('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_970])).
% 11.09/4.25  tff(c_8273, plain, (![D_555, C_551, B_554, E_550, F_553, A_552]: (k1_partfun1(A_552, B_554, C_551, D_555, E_550, F_553)=k5_relat_1(E_550, F_553) | ~m1_subset_1(F_553, k1_zfmisc_1(k2_zfmisc_1(C_551, D_555))) | ~v1_funct_1(F_553) | ~m1_subset_1(E_550, k1_zfmisc_1(k2_zfmisc_1(A_552, B_554))) | ~v1_funct_1(E_550))), inference(cnfTransformation, [status(thm)], [f_195])).
% 11.09/4.25  tff(c_8275, plain, (![A_552, B_554, E_550]: (k1_partfun1(A_552, B_554, '#skF_1', '#skF_1', E_550, '#skF_2')=k5_relat_1(E_550, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_550, k1_zfmisc_1(k2_zfmisc_1(A_552, B_554))) | ~v1_funct_1(E_550))), inference(resolution, [status(thm)], [c_94, c_8273])).
% 11.09/4.25  tff(c_8550, plain, (![A_570, B_571, E_572]: (k1_partfun1(A_570, B_571, '#skF_1', '#skF_1', E_572, '#skF_2')=k5_relat_1(E_572, '#skF_2') | ~m1_subset_1(E_572, k1_zfmisc_1(k2_zfmisc_1(A_570, B_571))) | ~v1_funct_1(E_572))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_8275])).
% 11.09/4.25  tff(c_8556, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_8550])).
% 11.09/4.25  tff(c_8562, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_8556])).
% 11.09/4.25  tff(c_7406, plain, (![D_507, C_508, A_509, B_510]: (D_507=C_508 | ~r2_relset_1(A_509, B_510, C_508, D_507) | ~m1_subset_1(D_507, k1_zfmisc_1(k2_zfmisc_1(A_509, B_510))) | ~m1_subset_1(C_508, k1_zfmisc_1(k2_zfmisc_1(A_509, B_510))))), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.09/4.25  tff(c_7412, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_86, c_7406])).
% 11.09/4.25  tff(c_7423, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_7412])).
% 11.09/4.25  tff(c_7437, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_7423])).
% 11.09/4.25  tff(c_8655, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8562, c_7437])).
% 11.09/4.25  tff(c_8661, plain, (![B_576, D_575, A_577, F_574, E_579, C_578]: (m1_subset_1(k1_partfun1(A_577, B_576, C_578, D_575, E_579, F_574), k1_zfmisc_1(k2_zfmisc_1(A_577, D_575))) | ~m1_subset_1(F_574, k1_zfmisc_1(k2_zfmisc_1(C_578, D_575))) | ~v1_funct_1(F_574) | ~m1_subset_1(E_579, k1_zfmisc_1(k2_zfmisc_1(A_577, B_576))) | ~v1_funct_1(E_579))), inference(cnfTransformation, [status(thm)], [f_185])).
% 11.09/4.25  tff(c_8708, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8562, c_8661])).
% 11.09/4.25  tff(c_8738, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_98, c_94, c_8708])).
% 11.09/4.25  tff(c_8750, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8655, c_8738])).
% 11.09/4.25  tff(c_8751, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_7423])).
% 11.09/4.25  tff(c_9595, plain, (![E_617, D_622, C_618, B_621, F_620, A_619]: (k1_partfun1(A_619, B_621, C_618, D_622, E_617, F_620)=k5_relat_1(E_617, F_620) | ~m1_subset_1(F_620, k1_zfmisc_1(k2_zfmisc_1(C_618, D_622))) | ~v1_funct_1(F_620) | ~m1_subset_1(E_617, k1_zfmisc_1(k2_zfmisc_1(A_619, B_621))) | ~v1_funct_1(E_617))), inference(cnfTransformation, [status(thm)], [f_195])).
% 11.09/4.25  tff(c_9597, plain, (![A_619, B_621, E_617]: (k1_partfun1(A_619, B_621, '#skF_1', '#skF_1', E_617, '#skF_2')=k5_relat_1(E_617, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_617, k1_zfmisc_1(k2_zfmisc_1(A_619, B_621))) | ~v1_funct_1(E_617))), inference(resolution, [status(thm)], [c_94, c_9595])).
% 11.09/4.25  tff(c_9958, plain, (![A_638, B_639, E_640]: (k1_partfun1(A_638, B_639, '#skF_1', '#skF_1', E_640, '#skF_2')=k5_relat_1(E_640, '#skF_2') | ~m1_subset_1(E_640, k1_zfmisc_1(k2_zfmisc_1(A_638, B_639))) | ~v1_funct_1(E_640))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_9597])).
% 11.09/4.25  tff(c_9964, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_9958])).
% 11.09/4.25  tff(c_9970, plain, (k5_relat_1('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_8751, c_9964])).
% 11.09/4.25  tff(c_9974, plain, (k10_relat_1('#skF_2', k2_relat_1('#skF_2'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9970, c_976])).
% 11.09/4.25  tff(c_9980, plain, (k2_relat_1('#skF_3')='#skF_1' | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_218, c_3964, c_9974])).
% 11.09/4.25  tff(c_9981, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_9816, c_9980])).
% 11.09/4.25  tff(c_9987, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_9981])).
% 11.09/4.25  tff(c_9991, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_218, c_323, c_9987])).
% 11.09/4.25  tff(c_9992, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_9814])).
% 11.09/4.25  tff(c_9993, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_9814])).
% 11.09/4.25  tff(c_10001, plain, (![B_12]: (k2_relat_1(k5_relat_1('#skF_3', B_12))=k9_relat_1(B_12, '#skF_1') | ~v1_relat_1(B_12) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_9993, c_12])).
% 11.09/4.25  tff(c_10233, plain, (![B_656]: (k2_relat_1(k5_relat_1('#skF_3', B_656))=k9_relat_1(B_656, '#skF_1') | ~v1_relat_1(B_656))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_10001])).
% 11.09/4.25  tff(c_10272, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_relat_1(k6_partfun1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_9992, c_10233])).
% 11.09/4.25  tff(c_10294, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_10272])).
% 11.09/4.25  tff(c_10505, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_10294])).
% 11.09/4.25  tff(c_10508, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_10505])).
% 11.09/4.25  tff(c_10512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_218, c_92, c_7300, c_10508])).
% 11.09/4.25  tff(c_10514, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_10294])).
% 11.09/4.25  tff(c_34, plain, (![A_21]: (v1_funct_1(k2_funct_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_95])).
% 11.09/4.25  tff(c_3965, plain, (r1_tarski('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_970])).
% 11.09/4.25  tff(c_492, plain, (![A_129]: (k2_relat_1(k2_funct_1(A_129))=k1_relat_1(A_129) | ~v2_funct_1(A_129) | ~v1_funct_1(A_129) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.09/4.25  tff(c_11299, plain, (![A_689]: (k10_relat_1(k2_funct_1(A_689), k1_relat_1(A_689))=k1_relat_1(k2_funct_1(A_689)) | ~v1_relat_1(k2_funct_1(A_689)) | ~v2_funct_1(A_689) | ~v1_funct_1(A_689) | ~v1_relat_1(A_689))), inference(superposition, [status(thm), theory('equality')], [c_492, c_14])).
% 11.09/4.25  tff(c_11308, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_914, c_11299])).
% 11.09/4.25  tff(c_11321, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_92, c_7300, c_10514, c_11308])).
% 11.09/4.25  tff(c_10513, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_10294])).
% 11.09/4.25  tff(c_44, plain, (![A_27]: (k1_relat_1(k2_funct_1(A_27))=k2_relat_1(A_27) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.09/4.25  tff(c_883, plain, (![B_171, A_172]: (k10_relat_1(B_171, k9_relat_1(B_171, A_172))=A_172 | ~v2_funct_1(B_171) | ~r1_tarski(A_172, k1_relat_1(B_171)) | ~v1_funct_1(B_171) | ~v1_relat_1(B_171))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.09/4.25  tff(c_13562, plain, (![A_770, A_771]: (k10_relat_1(k2_funct_1(A_770), k9_relat_1(k2_funct_1(A_770), A_771))=A_771 | ~v2_funct_1(k2_funct_1(A_770)) | ~r1_tarski(A_771, k2_relat_1(A_770)) | ~v1_funct_1(k2_funct_1(A_770)) | ~v1_relat_1(k2_funct_1(A_770)) | ~v2_funct_1(A_770) | ~v1_funct_1(A_770) | ~v1_relat_1(A_770))), inference(superposition, [status(thm), theory('equality')], [c_44, c_883])).
% 11.09/4.25  tff(c_13589, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_1')='#skF_1' | ~v2_funct_1(k2_funct_1('#skF_3')) | ~r1_tarski('#skF_1', k2_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10513, c_13562])).
% 11.09/4.25  tff(c_13607, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_92, c_7300, c_10514, c_3965, c_9993, c_11321, c_13589])).
% 11.09/4.25  tff(c_13608, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_13607])).
% 11.09/4.25  tff(c_13611, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_13608])).
% 11.09/4.25  tff(c_13615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_218, c_92, c_7300, c_13611])).
% 11.09/4.25  tff(c_13617, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_13607])).
% 11.09/4.25  tff(c_42, plain, (![A_27]: (k2_relat_1(k2_funct_1(A_27))=k1_relat_1(A_27) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.09/4.25  tff(c_10013, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9993, c_14])).
% 11.09/4.25  tff(c_10025, plain, (k10_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_218, c_914, c_10013])).
% 11.09/4.25  tff(c_9995, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9993, c_858])).
% 11.09/4.25  tff(c_10052, plain, (![B_641, C_642, A_643]: (k6_partfun1(B_641)=k5_relat_1(k2_funct_1(C_642), C_642) | k1_xboole_0=B_641 | ~v2_funct_1(C_642) | k2_relset_1(A_643, B_641, C_642)!=B_641 | ~m1_subset_1(C_642, k1_zfmisc_1(k2_zfmisc_1(A_643, B_641))) | ~v1_funct_2(C_642, A_643, B_641) | ~v1_funct_1(C_642))), inference(cnfTransformation, [status(thm)], [f_235])).
% 11.09/4.25  tff(c_10056, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_1', '#skF_3')!='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_10052])).
% 11.09/4.25  tff(c_10063, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | k2_relset_1('#skF_1', '#skF_1', '#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_7300, c_10056])).
% 11.09/4.25  tff(c_10064, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_1') | k2_relset_1('#skF_1', '#skF_1', '#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_241, c_10063])).
% 11.09/4.25  tff(c_10973, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9995, c_10064])).
% 11.09/4.25  tff(c_7315, plain, (![A_504]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_504))=A_504 | ~r1_tarski(A_504, '#skF_1'))), inference(splitRight, [status(thm)], [c_935])).
% 11.09/4.25  tff(c_7329, plain, (![A_10]: (k10_relat_1('#skF_3', k2_relat_1(k5_relat_1(A_10, '#skF_3')))=k2_relat_1(A_10) | ~r1_tarski(k2_relat_1(A_10), '#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_12, c_7315])).
% 11.09/4.25  tff(c_7338, plain, (![A_10]: (k10_relat_1('#skF_3', k2_relat_1(k5_relat_1(A_10, '#skF_3')))=k2_relat_1(A_10) | ~r1_tarski(k2_relat_1(A_10), '#skF_1') | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_7329])).
% 11.09/4.25  tff(c_10977, plain, (k10_relat_1('#skF_3', k2_relat_1(k6_partfun1('#skF_1')))=k2_relat_1(k2_funct_1('#skF_3')) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_10973, c_7338])).
% 11.09/4.25  tff(c_10983, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10514, c_10025, c_103, c_10977])).
% 11.09/4.25  tff(c_11205, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(splitLeft, [status(thm)], [c_10983])).
% 11.09/4.25  tff(c_11209, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_42, c_11205])).
% 11.09/4.25  tff(c_11215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_218, c_92, c_7300, c_3965, c_914, c_11209])).
% 11.09/4.25  tff(c_11216, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(splitRight, [status(thm)], [c_10983])).
% 11.09/4.25  tff(c_11311, plain, (k10_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_911, c_11299])).
% 11.09/4.25  tff(c_11323, plain, (k10_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_98, c_84, c_11311])).
% 11.09/4.25  tff(c_11449, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_11323])).
% 11.09/4.25  tff(c_11452, plain, (~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_11449])).
% 11.09/4.25  tff(c_11456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_215, c_98, c_84, c_11452])).
% 11.09/4.25  tff(c_11458, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_11323])).
% 11.09/4.25  tff(c_32, plain, (![A_21]: (v2_funct_1(k2_funct_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_95])).
% 11.09/4.25  tff(c_13616, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | k1_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(splitRight, [status(thm)], [c_13607])).
% 11.09/4.25  tff(c_13653, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_13616])).
% 11.09/4.25  tff(c_13656, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_13653])).
% 11.09/4.25  tff(c_13660, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_218, c_92, c_7300, c_13656])).
% 11.09/4.25  tff(c_13661, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(splitRight, [status(thm)], [c_13616])).
% 11.09/4.25  tff(c_10071, plain, (![A_644, B_645, E_646]: (k1_partfun1(A_644, B_645, '#skF_1', '#skF_1', E_646, '#skF_2')=k5_relat_1(E_646, '#skF_2') | ~m1_subset_1(E_646, k1_zfmisc_1(k2_zfmisc_1(A_644, B_645))) | ~v1_funct_1(E_646))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_9597])).
% 11.09/4.25  tff(c_10077, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_10071])).
% 11.09/4.25  tff(c_10083, plain, (k5_relat_1('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_8751, c_10077])).
% 11.09/4.25  tff(c_9005, plain, (![B_590, A_591]: (k5_relat_1(k2_funct_1(B_590), k2_funct_1(A_591))=k2_funct_1(k5_relat_1(A_591, B_590)) | ~v2_funct_1(B_590) | ~v2_funct_1(A_591) | ~v1_funct_1(B_590) | ~v1_relat_1(B_590) | ~v1_funct_1(A_591) | ~v1_relat_1(A_591))), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.09/4.25  tff(c_14753, plain, (![A_835, B_836]: (k6_partfun1(k1_relat_1(k2_funct_1(A_835)))=k2_funct_1(A_835) | k2_funct_1(k5_relat_1(A_835, B_836))!=k2_funct_1(B_836) | k2_relat_1(k2_funct_1(B_836))!=k1_relat_1(k2_funct_1(A_835)) | ~v1_funct_1(k2_funct_1(A_835)) | ~v1_relat_1(k2_funct_1(A_835)) | ~v1_funct_1(k2_funct_1(B_836)) | ~v1_relat_1(k2_funct_1(B_836)) | ~v2_funct_1(B_836) | ~v2_funct_1(A_835) | ~v1_funct_1(B_836) | ~v1_relat_1(B_836) | ~v1_funct_1(A_835) | ~v1_relat_1(A_835))), inference(superposition, [status(thm), theory('equality')], [c_9005, c_99])).
% 11.09/4.25  tff(c_14771, plain, (k6_partfun1(k1_relat_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3') | k2_relat_1(k2_funct_1('#skF_2'))!=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10083, c_14753])).
% 11.09/4.25  tff(c_14796, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k2_relat_1(k2_funct_1('#skF_2'))!='#skF_1' | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_92, c_215, c_98, c_7300, c_84, c_11458, c_10514, c_13617, c_13661, c_13661, c_14771])).
% 11.09/4.25  tff(c_14801, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_14796])).
% 11.09/4.25  tff(c_14804, plain, (~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_14801])).
% 11.09/4.25  tff(c_14808, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_215, c_98, c_84, c_14804])).
% 11.09/4.25  tff(c_14809, plain, (k2_relat_1(k2_funct_1('#skF_2'))!='#skF_1' | k6_partfun1('#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_14796])).
% 11.09/4.25  tff(c_14840, plain, (k2_relat_1(k2_funct_1('#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_14809])).
% 11.09/4.25  tff(c_14843, plain, (k1_relat_1('#skF_2')!='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_42, c_14840])).
% 11.09/4.25  tff(c_14846, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_215, c_98, c_84, c_911, c_14843])).
% 11.09/4.25  tff(c_14847, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_14809])).
% 11.09/4.25  tff(c_14900, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14847, c_10973])).
% 11.09/4.25  tff(c_15089, plain, (k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14900, c_99])).
% 11.09/4.25  tff(c_15104, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10514, c_13617, c_218, c_92, c_914, c_11216, c_14847, c_914, c_15089])).
% 11.09/4.25  tff(c_14902, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14847, c_82])).
% 11.09/4.25  tff(c_15106, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15104, c_14902])).
% 11.09/4.25  tff(c_15126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_482, c_15106])).
% 11.09/4.25  tff(c_15128, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_162])).
% 11.09/4.25  tff(c_20, plain, (![A_16]: (k1_relat_1(A_16)!=k1_xboole_0 | k1_xboole_0=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.09/4.25  tff(c_233, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_218, c_20])).
% 11.09/4.25  tff(c_16011, plain, (k1_relat_1('#skF_3')!='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15128, c_15128, c_233])).
% 11.09/4.25  tff(c_16012, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_16011])).
% 11.09/4.25  tff(c_16622, plain, (![A_1002, B_1003, C_1004]: (k1_relset_1(A_1002, B_1003, C_1004)=k1_relat_1(C_1004) | ~m1_subset_1(C_1004, k1_zfmisc_1(k2_zfmisc_1(A_1002, B_1003))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 11.09/4.25  tff(c_16631, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_16622])).
% 11.09/4.25  tff(c_17829, plain, (![A_1060, B_1061]: (k1_relset_1(A_1060, A_1060, B_1061)=A_1060 | ~m1_subset_1(B_1061, k1_zfmisc_1(k2_zfmisc_1(A_1060, A_1060))) | ~v1_funct_2(B_1061, A_1060, A_1060) | ~v1_funct_1(B_1061))), inference(cnfTransformation, [status(thm)], [f_243])).
% 11.09/4.25  tff(c_17835, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_17829])).
% 11.09/4.25  tff(c_17841, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_16631, c_17835])).
% 11.09/4.25  tff(c_17843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16012, c_17841])).
% 11.09/4.25  tff(c_17844, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_16011])).
% 11.09/4.25  tff(c_15127, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_162])).
% 11.09/4.25  tff(c_16010, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15128, c_15127])).
% 11.09/4.25  tff(c_17846, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17844, c_16010])).
% 11.09/4.25  tff(c_165, plain, (![A_82]: (k2_relat_1(k1_xboole_0)=A_82 | k1_xboole_0!=A_82)), inference(superposition, [status(thm), theory('equality')], [c_156, c_103])).
% 11.09/4.25  tff(c_15198, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15128, c_15128, c_165])).
% 11.09/4.25  tff(c_225, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_215, c_20])).
% 11.09/4.25  tff(c_15193, plain, (k1_relat_1('#skF_2')!='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15128, c_15128, c_225])).
% 11.09/4.25  tff(c_15194, plain, (k1_relat_1('#skF_2')!='#skF_1'), inference(splitLeft, [status(thm)], [c_15193])).
% 11.09/4.25  tff(c_15581, plain, (![A_899, B_900, C_901]: (k1_relset_1(A_899, B_900, C_901)=k1_relat_1(C_901) | ~m1_subset_1(C_901, k1_zfmisc_1(k2_zfmisc_1(A_899, B_900))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 11.09/4.25  tff(c_15588, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_94, c_15581])).
% 11.09/4.25  tff(c_15920, plain, (![A_937, B_938]: (k1_relset_1(A_937, A_937, B_938)=A_937 | ~m1_subset_1(B_938, k1_zfmisc_1(k2_zfmisc_1(A_937, A_937))) | ~v1_funct_2(B_938, A_937, A_937) | ~v1_funct_1(B_938))), inference(cnfTransformation, [status(thm)], [f_243])).
% 11.09/4.25  tff(c_15923, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_94, c_15920])).
% 11.09/4.25  tff(c_15929, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_15588, c_15923])).
% 11.09/4.25  tff(c_15931, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15194, c_15929])).
% 11.09/4.25  tff(c_15932, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_15193])).
% 11.09/4.25  tff(c_18, plain, (![A_16]: (k2_relat_1(A_16)!=k1_xboole_0 | k1_xboole_0=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.09/4.25  tff(c_226, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_215, c_18])).
% 11.09/4.25  tff(c_15139, plain, (k2_relat_1('#skF_2')!='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15128, c_15128, c_226])).
% 11.09/4.25  tff(c_15140, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(splitLeft, [status(thm)], [c_15139])).
% 11.09/4.25  tff(c_15934, plain, (k2_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15932, c_15140])).
% 11.09/4.25  tff(c_15956, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15198, c_15934])).
% 11.09/4.25  tff(c_15957, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_15139])).
% 11.09/4.25  tff(c_15961, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_15957, c_94])).
% 11.09/4.25  tff(c_18124, plain, (![A_1101, B_1102, D_1103]: (r2_relset_1(A_1101, B_1102, D_1103, D_1103) | ~m1_subset_1(D_1103, k1_zfmisc_1(k2_zfmisc_1(A_1101, B_1102))))), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.09/4.25  tff(c_18126, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_15961, c_18124])).
% 11.09/4.25  tff(c_18130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17846, c_18126])).
% 11.09/4.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.09/4.25  
% 11.09/4.25  Inference rules
% 11.09/4.25  ----------------------
% 11.09/4.25  #Ref     : 51
% 11.09/4.25  #Sup     : 3875
% 11.09/4.25  #Fact    : 0
% 11.09/4.25  #Define  : 0
% 11.09/4.25  #Split   : 118
% 11.09/4.25  #Chain   : 0
% 11.09/4.25  #Close   : 0
% 11.09/4.25  
% 11.09/4.25  Ordering : KBO
% 11.09/4.25  
% 11.09/4.25  Simplification rules
% 11.09/4.25  ----------------------
% 11.09/4.25  #Subsume      : 2583
% 11.09/4.25  #Demod        : 3645
% 11.09/4.25  #Tautology    : 1161
% 11.09/4.25  #SimpNegUnit  : 579
% 11.09/4.25  #BackRed      : 225
% 11.09/4.25  
% 11.09/4.25  #Partial instantiations: 0
% 11.09/4.25  #Strategies tried      : 1
% 11.09/4.25  
% 11.09/4.25  Timing (in seconds)
% 11.09/4.25  ----------------------
% 11.09/4.25  Preprocessing        : 0.42
% 11.09/4.25  Parsing              : 0.23
% 11.09/4.25  CNF conversion       : 0.03
% 11.09/4.25  Main loop            : 2.95
% 11.09/4.25  Inferencing          : 0.86
% 11.09/4.25  Reduction            : 1.22
% 11.09/4.25  Demodulation         : 0.91
% 11.09/4.25  BG Simplification    : 0.09
% 11.09/4.26  Subsumption          : 0.58
% 11.09/4.26  Abstraction          : 0.12
% 11.09/4.26  MUC search           : 0.00
% 11.09/4.26  Cooper               : 0.00
% 11.09/4.26  Total                : 3.47
% 11.09/4.26  Index Insertion      : 0.00
% 11.09/4.26  Index Deletion       : 0.00
% 11.09/4.26  Index Matching       : 0.00
% 11.09/4.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
