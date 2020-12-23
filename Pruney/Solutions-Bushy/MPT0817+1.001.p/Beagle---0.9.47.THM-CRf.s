%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0817+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:53 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :   54 (  75 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   89 ( 135 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( r1_tarski(k1_relat_1(D),B)
         => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(c_27,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_31,plain,(
    ~ r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_27,c_22])).

tff(c_24,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_41,plain,(
    ! [C_23,A_24,B_25] :
      ( v1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_41])).

tff(c_89,plain,(
    ! [A_39] :
      ( r1_tarski(A_39,k2_zfmisc_1(k1_relat_1(A_39),k2_relat_1(A_39)))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_68,plain,(
    ! [C_33,B_34,A_35] :
      ( v5_relat_1(C_33,B_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_35,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    ! [A_17,B_34,A_35] :
      ( v5_relat_1(A_17,B_34)
      | ~ r1_tarski(A_17,k2_zfmisc_1(A_35,B_34)) ) ),
    inference(resolution,[status(thm)],[c_20,c_68])).

tff(c_100,plain,(
    ! [A_39] :
      ( v5_relat_1(A_39,k2_relat_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_89,c_76])).

tff(c_77,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_68])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_104,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_tarski(A_41,C_42)
      | ~ r1_tarski(B_43,C_42)
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_318,plain,(
    ! [A_81,A_82,B_83] :
      ( r1_tarski(A_81,A_82)
      | ~ r1_tarski(A_81,k2_relat_1(B_83))
      | ~ v5_relat_1(B_83,A_82)
      | ~ v1_relat_1(B_83) ) ),
    inference(resolution,[status(thm)],[c_10,c_104])).

tff(c_964,plain,(
    ! [B_178,A_179,B_180] :
      ( r1_tarski(k2_relat_1(B_178),A_179)
      | ~ v5_relat_1(B_180,A_179)
      | ~ v1_relat_1(B_180)
      | ~ v5_relat_1(B_178,k2_relat_1(B_180))
      | ~ v1_relat_1(B_178) ) ),
    inference(resolution,[status(thm)],[c_10,c_318])).

tff(c_984,plain,(
    ! [B_178] :
      ( r1_tarski(k2_relat_1(B_178),'#skF_3')
      | ~ v1_relat_1('#skF_4')
      | ~ v5_relat_1(B_178,k2_relat_1('#skF_4'))
      | ~ v1_relat_1(B_178) ) ),
    inference(resolution,[status(thm)],[c_77,c_964])).

tff(c_997,plain,(
    ! [B_181] :
      ( r1_tarski(k2_relat_1(B_181),'#skF_3')
      | ~ v5_relat_1(B_181,k2_relat_1('#skF_4'))
      | ~ v1_relat_1(B_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_984])).

tff(c_1017,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_997])).

tff(c_1026,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1017])).

tff(c_16,plain,(
    ! [A_16] :
      ( r1_tarski(A_16,k2_zfmisc_1(k1_relat_1(A_16),k2_relat_1(A_16)))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_158,plain,(
    ! [A_52,C_53,B_54,D_55] :
      ( r1_tarski(k2_zfmisc_1(A_52,C_53),k2_zfmisc_1(B_54,D_55))
      | ~ r1_tarski(C_53,D_55)
      | ~ r1_tarski(A_52,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    ! [A_13,C_15,B_14] :
      ( r1_tarski(A_13,C_15)
      | ~ r1_tarski(B_14,C_15)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_438,plain,(
    ! [C_110,A_109,A_111,D_112,B_113] :
      ( r1_tarski(A_111,k2_zfmisc_1(B_113,D_112))
      | ~ r1_tarski(A_111,k2_zfmisc_1(A_109,C_110))
      | ~ r1_tarski(C_110,D_112)
      | ~ r1_tarski(A_109,B_113) ) ),
    inference(resolution,[status(thm)],[c_158,c_14])).

tff(c_455,plain,(
    ! [A_16,B_113,D_112] :
      ( r1_tarski(A_16,k2_zfmisc_1(B_113,D_112))
      | ~ r1_tarski(k2_relat_1(A_16),D_112)
      | ~ r1_tarski(k1_relat_1(A_16),B_113)
      | ~ v1_relat_1(A_16) ) ),
    inference(resolution,[status(thm)],[c_16,c_438])).

tff(c_1030,plain,(
    ! [B_113] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_113,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_113)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1026,c_455])).

tff(c_1212,plain,(
    ! [B_192] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_192,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1030])).

tff(c_1227,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_1212])).

tff(c_1234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_1227])).

%------------------------------------------------------------------------------
