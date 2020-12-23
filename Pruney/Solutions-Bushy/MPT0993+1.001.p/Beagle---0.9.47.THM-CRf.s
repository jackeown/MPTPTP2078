%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0993+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:12 EST 2020

% Result     : Theorem 1.31s
% Output     : CNFRefutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   36 (  43 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  63 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k5_relset_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_34,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( r1_tarski(B,C)
       => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_30,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(c_10,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_17,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( k5_relset_1(A_13,B_14,C_15,D_16) = k7_relat_1(C_15,D_16)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_20,plain,(
    ! [D_16] : k5_relset_1('#skF_1','#skF_2','#skF_4',D_16) = k7_relat_1('#skF_4',D_16) ),
    inference(resolution,[status(thm)],[c_12,c_17])).

tff(c_46,plain,(
    ! [B_23,A_24,D_25,C_26] :
      ( r2_relset_1(B_23,A_24,k5_relset_1(B_23,A_24,D_25,C_26),D_25)
      | ~ r1_tarski(B_23,C_26)
      | ~ m1_subset_1(D_25,k1_zfmisc_1(k2_zfmisc_1(B_23,A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_48,plain,(
    ! [C_26] :
      ( r2_relset_1('#skF_1','#skF_2',k5_relset_1('#skF_1','#skF_2','#skF_4',C_26),'#skF_4')
      | ~ r1_tarski('#skF_1',C_26) ) ),
    inference(resolution,[status(thm)],[c_12,c_46])).

tff(c_51,plain,(
    ! [C_27] :
      ( r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4',C_27),'#skF_4')
      | ~ r1_tarski('#skF_1',C_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_48])).

tff(c_16,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [A_18,B_19,C_20,D_21] :
      ( k2_partfun1(A_18,B_19,C_20,D_21) = k7_relat_1(C_20,D_21)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_32,plain,(
    ! [D_21] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_21) = k7_relat_1('#skF_4',D_21)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_30])).

tff(c_35,plain,(
    ! [D_21] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_21) = k7_relat_1('#skF_4',D_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_32])).

tff(c_8,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_8])).

tff(c_54,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_36])).

tff(c_58,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_54])).

%------------------------------------------------------------------------------
