%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1054+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:20 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 115 expanded)
%              Number of leaves         :   35 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  111 ( 183 expanded)
%              Number of equality atoms :   18 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v8_relat_2 > v4_relat_2 > v3_relat_2 > v1_relat_2 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v3_relat_2,type,(
    v3_relat_2: $i > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_78,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v3_relat_2(k6_relat_1(A))
      & v4_relat_2(k6_relat_1(A))
      & v8_relat_2(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v3_relat_2(A)
        & v8_relat_2(A) )
     => ( v1_relat_1(A)
        & v1_relat_2(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_partfun1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ( ( v1_relat_2(B)
          & v1_funct_1(B)
          & v1_partfun1(B,A)
          & v1_funct_2(B,A,A) )
       => ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,A)
        & v3_funct_2(C,A,A)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( r1_tarski(B,A)
       => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
          & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

tff(c_46,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_71,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_75,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_71])).

tff(c_32,plain,(
    ! [A_10] : k6_relat_1(A_10) = k6_partfun1(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    ! [A_15,B_16] :
      ( k9_relat_1(k6_relat_1(A_15),B_16) = B_16
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_94,plain,(
    ! [A_36,B_37] :
      ( k9_relat_1(k6_partfun1(A_36),B_37) = B_37
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36])).

tff(c_106,plain,(
    k9_relat_1(k6_partfun1('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_48,c_94])).

tff(c_22,plain,(
    ! [A_8] : v1_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_54,plain,(
    ! [A_8] : v1_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_22])).

tff(c_16,plain,(
    ! [A_7] : v1_partfun1(k6_partfun1(A_7),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    ! [A_7] : m1_subset_1(k6_partfun1(A_7),k1_zfmisc_1(k2_zfmisc_1(A_7,A_7))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_176,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_funct_2(C_52,A_53,B_54)
      | ~ v1_partfun1(C_52,A_53)
      | ~ v1_funct_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_183,plain,(
    ! [A_7] :
      ( v1_funct_2(k6_partfun1(A_7),A_7,A_7)
      | ~ v1_partfun1(k6_partfun1(A_7),A_7)
      | ~ v1_funct_1(k6_partfun1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_18,c_176])).

tff(c_187,plain,(
    ! [A_7] : v1_funct_2(k6_partfun1(A_7),A_7,A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_16,c_183])).

tff(c_24,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_53,plain,(
    ! [A_9] : v1_relat_1(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24])).

tff(c_26,plain,(
    ! [A_9] : v3_relat_2(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_52,plain,(
    ! [A_9] : v3_relat_2(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26])).

tff(c_30,plain,(
    ! [A_9] : v8_relat_2(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    ! [A_9] : v8_relat_2(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30])).

tff(c_87,plain,(
    ! [A_35] :
      ( v1_relat_2(A_35)
      | ~ v8_relat_2(A_35)
      | ~ v3_relat_2(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_90,plain,(
    ! [A_9] :
      ( v1_relat_2(k6_partfun1(A_9))
      | ~ v3_relat_2(k6_partfun1(A_9))
      | ~ v1_relat_1(k6_partfun1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_50,c_87])).

tff(c_93,plain,(
    ! [A_9] : v1_relat_2(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_52,c_90])).

tff(c_189,plain,(
    ! [B_56,A_57] :
      ( v3_funct_2(B_56,A_57,A_57)
      | ~ v1_funct_2(B_56,A_57,A_57)
      | ~ v1_partfun1(B_56,A_57)
      | ~ v1_funct_1(B_56)
      | ~ v1_relat_2(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k2_zfmisc_1(A_57,A_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_196,plain,(
    ! [A_7] :
      ( v3_funct_2(k6_partfun1(A_7),A_7,A_7)
      | ~ v1_funct_2(k6_partfun1(A_7),A_7,A_7)
      | ~ v1_partfun1(k6_partfun1(A_7),A_7)
      | ~ v1_funct_1(k6_partfun1(A_7))
      | ~ v1_relat_2(k6_partfun1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_18,c_189])).

tff(c_200,plain,(
    ! [A_7] : v3_funct_2(k6_partfun1(A_7),A_7,A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_54,c_16,c_187,c_196])).

tff(c_133,plain,(
    ! [A_41,B_42,C_43,D_44] :
      ( k7_relset_1(A_41,B_42,C_43,D_44) = k9_relat_1(C_43,D_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_140,plain,(
    ! [A_7,D_44] : k7_relset_1(A_7,A_7,k6_partfun1(A_7),D_44) = k9_relat_1(k6_partfun1(A_7),D_44) ),
    inference(resolution,[status(thm)],[c_18,c_133])).

tff(c_249,plain,(
    ! [A_74,C_75,B_76] :
      ( k8_relset_1(A_74,A_74,C_75,k7_relset_1(A_74,A_74,C_75,B_76)) = B_76
      | ~ r1_tarski(B_76,A_74)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_74,A_74)))
      | ~ v3_funct_2(C_75,A_74,A_74)
      | ~ v1_funct_2(C_75,A_74,A_74)
      | ~ v1_funct_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_254,plain,(
    ! [A_7,B_76] :
      ( k8_relset_1(A_7,A_7,k6_partfun1(A_7),k7_relset_1(A_7,A_7,k6_partfun1(A_7),B_76)) = B_76
      | ~ r1_tarski(B_76,A_7)
      | ~ v3_funct_2(k6_partfun1(A_7),A_7,A_7)
      | ~ v1_funct_2(k6_partfun1(A_7),A_7,A_7)
      | ~ v1_funct_1(k6_partfun1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_18,c_249])).

tff(c_259,plain,(
    ! [A_77,B_78] :
      ( k8_relset_1(A_77,A_77,k6_partfun1(A_77),k9_relat_1(k6_partfun1(A_77),B_78)) = B_78
      | ~ r1_tarski(B_78,A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_187,c_200,c_140,c_254])).

tff(c_283,plain,
    ( k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_259])).

tff(c_291,plain,(
    k8_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_283])).

tff(c_293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_291])).

%------------------------------------------------------------------------------
