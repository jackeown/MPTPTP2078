%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1058+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:21 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   50 (  54 expanded)
%              Number of leaves         :   28 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 (  67 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_32,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_30,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_28,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_36,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

tff(c_22,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_3] : k6_relat_1(A_3) = k6_partfun1(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6,plain,(
    ! [A_2] : v1_relat_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_30,plain,(
    ! [A_2] : v1_relat_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( k5_relat_1(k6_relat_1(A_16),B_17) = k7_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_29,plain,(
    ! [A_16,B_17] :
      ( k5_relat_1(k6_partfun1(A_16),B_17) = k7_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_20])).

tff(c_79,plain,(
    ! [B_35,C_36,A_37] :
      ( k10_relat_1(k5_relat_1(B_35,C_36),A_37) = k10_relat_1(B_35,k10_relat_1(C_36,A_37))
      | ~ v1_relat_1(C_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_88,plain,(
    ! [A_16,B_17,A_37] :
      ( k10_relat_1(k6_partfun1(A_16),k10_relat_1(B_17,A_37)) = k10_relat_1(k7_relat_1(B_17,A_16),A_37)
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(k6_partfun1(A_16))
      | ~ v1_relat_1(B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_79])).

tff(c_156,plain,(
    ! [A_53,B_54,A_55] :
      ( k10_relat_1(k6_partfun1(A_53),k10_relat_1(B_54,A_55)) = k10_relat_1(k7_relat_1(B_54,A_53),A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_88])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1(k6_partfun1(A_1),k1_zfmisc_1(k2_zfmisc_1(A_1,A_1))) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_93,plain,(
    ! [A_38,B_39,C_40,D_41] :
      ( k8_relset_1(A_38,B_39,C_40,D_41) = k10_relat_1(C_40,D_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_100,plain,(
    ! [A_1,D_41] : k8_relset_1(A_1,A_1,k6_partfun1(A_1),D_41) = k10_relat_1(k6_partfun1(A_1),D_41) ),
    inference(resolution,[status(thm)],[c_4,c_93])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_63,plain,(
    ! [A_31,B_32] :
      ( k8_relset_1(A_31,A_31,k6_partfun1(A_31),B_32) = B_32
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_68,plain,(
    ! [B_15,A_14] :
      ( k8_relset_1(B_15,B_15,k6_partfun1(B_15),A_14) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_18,c_63])).

tff(c_101,plain,(
    ! [B_15,A_14] :
      ( k10_relat_1(k6_partfun1(B_15),A_14) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_68])).

tff(c_249,plain,(
    ! [B_62,A_63,A_64] :
      ( k10_relat_1(k7_relat_1(B_62,A_63),A_64) = k10_relat_1(B_62,A_64)
      | ~ r1_tarski(k10_relat_1(B_62,A_64),A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_101])).

tff(c_270,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_249])).

tff(c_280,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_270])).

tff(c_282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_280])).

%------------------------------------------------------------------------------
