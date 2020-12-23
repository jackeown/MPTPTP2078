%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:52 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 121 expanded)
%              Number of leaves         :   35 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :  118 ( 190 expanded)
%              Number of equality atoms :   25 (  28 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_84,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_72,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1024,plain,(
    ! [A_157,B_158,C_159,D_160] :
      ( r2_relset_1(A_157,B_158,C_159,C_159)
      | ~ m1_subset_1(D_160,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158)))
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1058,plain,(
    ! [C_162] :
      ( r2_relset_1('#skF_1','#skF_2',C_162,C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_34,c_1024])).

tff(c_1081,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_1058])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_750,plain,(
    ! [B_125,A_126] :
      ( v1_relat_1(B_125)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(A_126))
      | ~ v1_relat_1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_759,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_750])).

tff(c_766,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_759])).

tff(c_783,plain,(
    ! [A_134,B_135,C_136] :
      ( k2_relset_1(A_134,B_135,C_136) = k2_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_796,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_783])).

tff(c_848,plain,(
    ! [A_145,B_146,C_147] :
      ( m1_subset_1(k2_relset_1(A_145,B_146,C_147),k1_zfmisc_1(B_146))
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_868,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_848])).

tff(c_876,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_868])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_884,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_876,c_2])).

tff(c_30,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_relat_1(A_10)) = B_11
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_35,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_partfun1(A_10)) = B_11
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_12])).

tff(c_887,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_884,c_35])).

tff(c_893,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_766,c_887])).

tff(c_28,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1141,plain,(
    ! [C_169,F_172,E_171,D_174,A_173,B_170] :
      ( k4_relset_1(A_173,B_170,C_169,D_174,E_171,F_172) = k5_relat_1(E_171,F_172)
      | ~ m1_subset_1(F_172,k1_zfmisc_1(k2_zfmisc_1(C_169,D_174)))
      | ~ m1_subset_1(E_171,k1_zfmisc_1(k2_zfmisc_1(A_173,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1712,plain,(
    ! [A_237,B_238,A_239,E_240] :
      ( k4_relset_1(A_237,B_238,A_239,A_239,E_240,k6_partfun1(A_239)) = k5_relat_1(E_240,k6_partfun1(A_239))
      | ~ m1_subset_1(E_240,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(resolution,[status(thm)],[c_28,c_1141])).

tff(c_1738,plain,(
    ! [A_239] : k4_relset_1('#skF_1','#skF_2',A_239,A_239,'#skF_3',k6_partfun1(A_239)) = k5_relat_1('#skF_3',k6_partfun1(A_239)) ),
    inference(resolution,[status(thm)],[c_34,c_1712])).

tff(c_360,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( r2_relset_1(A_81,B_82,C_83,C_83)
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_394,plain,(
    ! [C_86] :
      ( r2_relset_1('#skF_1','#skF_2',C_86,C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_34,c_360])).

tff(c_417,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_394])).

tff(c_65,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_74,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_65])).

tff(c_81,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_74])).

tff(c_98,plain,(
    ! [A_55,B_56,C_57] :
      ( k1_relset_1(A_55,B_56,C_57) = k1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_111,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_98])).

tff(c_267,plain,(
    ! [A_75,B_76,C_77] :
      ( m1_subset_1(k1_relset_1(A_75,B_76,C_77),k1_zfmisc_1(A_75))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_287,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_267])).

tff(c_295,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_287])).

tff(c_303,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_295,c_2])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k5_relat_1(k6_relat_1(A_8),B_9) = B_9
      | ~ r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_36,plain,(
    ! [A_8,B_9] :
      ( k5_relat_1(k6_partfun1(A_8),B_9) = B_9
      | ~ r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10])).

tff(c_306,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_303,c_36])).

tff(c_312,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_306])).

tff(c_457,plain,(
    ! [A_95,D_96,B_92,C_91,F_94,E_93] :
      ( k4_relset_1(A_95,B_92,C_91,D_96,E_93,F_94) = k5_relat_1(E_93,F_94)
      | ~ m1_subset_1(F_94,k1_zfmisc_1(k2_zfmisc_1(C_91,D_96)))
      | ~ m1_subset_1(E_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_543,plain,(
    ! [A_105,B_106,E_107] :
      ( k4_relset_1(A_105,B_106,'#skF_1','#skF_2',E_107,'#skF_3') = k5_relat_1(E_107,'#skF_3')
      | ~ m1_subset_1(E_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(resolution,[status(thm)],[c_34,c_457])).

tff(c_574,plain,(
    ! [A_34] : k4_relset_1(A_34,A_34,'#skF_1','#skF_2',k6_partfun1(A_34),'#skF_3') = k5_relat_1(k6_partfun1(A_34),'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_543])).

tff(c_32,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_64,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_744,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_64])).

tff(c_747,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_312,c_744])).

tff(c_748,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1739,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1738,c_748])).

tff(c_1742,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_893,c_1739])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:28:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.58  
% 3.53/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.58  %$ r2_relset_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.53/1.58  
% 3.53/1.58  %Foreground sorts:
% 3.53/1.58  
% 3.53/1.58  
% 3.53/1.58  %Background operators:
% 3.53/1.58  
% 3.53/1.58  
% 3.53/1.58  %Foreground operators:
% 3.53/1.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.53/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.58  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.53/1.58  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.53/1.58  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.53/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.58  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.53/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.53/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.53/1.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.53/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.58  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.53/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.53/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.53/1.58  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.53/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.53/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.58  
% 3.53/1.60  tff(f_91, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 3.53/1.60  tff(f_78, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.53/1.60  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.53/1.60  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.53/1.60  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.53/1.60  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.53/1.60  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.53/1.60  tff(f_84, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.53/1.60  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.53/1.60  tff(f_82, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.53/1.60  tff(f_72, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.53/1.60  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.53/1.60  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.53/1.60  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 3.53/1.60  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.53/1.60  tff(c_1024, plain, (![A_157, B_158, C_159, D_160]: (r2_relset_1(A_157, B_158, C_159, C_159) | ~m1_subset_1(D_160, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.53/1.60  tff(c_1058, plain, (![C_162]: (r2_relset_1('#skF_1', '#skF_2', C_162, C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_34, c_1024])).
% 3.53/1.60  tff(c_1081, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_1058])).
% 3.53/1.60  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.53/1.60  tff(c_750, plain, (![B_125, A_126]: (v1_relat_1(B_125) | ~m1_subset_1(B_125, k1_zfmisc_1(A_126)) | ~v1_relat_1(A_126))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.53/1.60  tff(c_759, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_750])).
% 3.53/1.60  tff(c_766, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_759])).
% 3.53/1.60  tff(c_783, plain, (![A_134, B_135, C_136]: (k2_relset_1(A_134, B_135, C_136)=k2_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.53/1.60  tff(c_796, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_783])).
% 3.53/1.60  tff(c_848, plain, (![A_145, B_146, C_147]: (m1_subset_1(k2_relset_1(A_145, B_146, C_147), k1_zfmisc_1(B_146)) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.53/1.60  tff(c_868, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_796, c_848])).
% 3.53/1.60  tff(c_876, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_868])).
% 3.53/1.60  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.53/1.60  tff(c_884, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_876, c_2])).
% 3.53/1.60  tff(c_30, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.53/1.60  tff(c_12, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_relat_1(A_10))=B_11 | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.53/1.60  tff(c_35, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_partfun1(A_10))=B_11 | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_12])).
% 3.53/1.60  tff(c_887, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_884, c_35])).
% 3.53/1.60  tff(c_893, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_766, c_887])).
% 3.53/1.60  tff(c_28, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.53/1.60  tff(c_1141, plain, (![C_169, F_172, E_171, D_174, A_173, B_170]: (k4_relset_1(A_173, B_170, C_169, D_174, E_171, F_172)=k5_relat_1(E_171, F_172) | ~m1_subset_1(F_172, k1_zfmisc_1(k2_zfmisc_1(C_169, D_174))) | ~m1_subset_1(E_171, k1_zfmisc_1(k2_zfmisc_1(A_173, B_170))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.53/1.60  tff(c_1712, plain, (![A_237, B_238, A_239, E_240]: (k4_relset_1(A_237, B_238, A_239, A_239, E_240, k6_partfun1(A_239))=k5_relat_1(E_240, k6_partfun1(A_239)) | ~m1_subset_1(E_240, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(resolution, [status(thm)], [c_28, c_1141])).
% 3.53/1.60  tff(c_1738, plain, (![A_239]: (k4_relset_1('#skF_1', '#skF_2', A_239, A_239, '#skF_3', k6_partfun1(A_239))=k5_relat_1('#skF_3', k6_partfun1(A_239)))), inference(resolution, [status(thm)], [c_34, c_1712])).
% 3.53/1.60  tff(c_360, plain, (![A_81, B_82, C_83, D_84]: (r2_relset_1(A_81, B_82, C_83, C_83) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.53/1.60  tff(c_394, plain, (![C_86]: (r2_relset_1('#skF_1', '#skF_2', C_86, C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_34, c_360])).
% 3.53/1.60  tff(c_417, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_394])).
% 3.53/1.60  tff(c_65, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.53/1.60  tff(c_74, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_65])).
% 3.53/1.60  tff(c_81, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_74])).
% 3.53/1.60  tff(c_98, plain, (![A_55, B_56, C_57]: (k1_relset_1(A_55, B_56, C_57)=k1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.53/1.60  tff(c_111, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_98])).
% 3.53/1.60  tff(c_267, plain, (![A_75, B_76, C_77]: (m1_subset_1(k1_relset_1(A_75, B_76, C_77), k1_zfmisc_1(A_75)) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.53/1.60  tff(c_287, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_111, c_267])).
% 3.53/1.60  tff(c_295, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_287])).
% 3.53/1.60  tff(c_303, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_295, c_2])).
% 3.53/1.60  tff(c_10, plain, (![A_8, B_9]: (k5_relat_1(k6_relat_1(A_8), B_9)=B_9 | ~r1_tarski(k1_relat_1(B_9), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.53/1.60  tff(c_36, plain, (![A_8, B_9]: (k5_relat_1(k6_partfun1(A_8), B_9)=B_9 | ~r1_tarski(k1_relat_1(B_9), A_8) | ~v1_relat_1(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_10])).
% 3.53/1.60  tff(c_306, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_303, c_36])).
% 3.53/1.60  tff(c_312, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_306])).
% 3.53/1.60  tff(c_457, plain, (![A_95, D_96, B_92, C_91, F_94, E_93]: (k4_relset_1(A_95, B_92, C_91, D_96, E_93, F_94)=k5_relat_1(E_93, F_94) | ~m1_subset_1(F_94, k1_zfmisc_1(k2_zfmisc_1(C_91, D_96))) | ~m1_subset_1(E_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_92))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.53/1.60  tff(c_543, plain, (![A_105, B_106, E_107]: (k4_relset_1(A_105, B_106, '#skF_1', '#skF_2', E_107, '#skF_3')=k5_relat_1(E_107, '#skF_3') | ~m1_subset_1(E_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(resolution, [status(thm)], [c_34, c_457])).
% 3.53/1.60  tff(c_574, plain, (![A_34]: (k4_relset_1(A_34, A_34, '#skF_1', '#skF_2', k6_partfun1(A_34), '#skF_3')=k5_relat_1(k6_partfun1(A_34), '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_543])).
% 3.53/1.60  tff(c_32, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.53/1.60  tff(c_64, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 3.53/1.60  tff(c_744, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_574, c_64])).
% 3.53/1.60  tff(c_747, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_417, c_312, c_744])).
% 3.53/1.60  tff(c_748, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 3.53/1.60  tff(c_1739, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1738, c_748])).
% 3.53/1.60  tff(c_1742, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1081, c_893, c_1739])).
% 3.53/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.60  
% 3.53/1.60  Inference rules
% 3.53/1.60  ----------------------
% 3.53/1.60  #Ref     : 0
% 3.53/1.60  #Sup     : 370
% 3.53/1.60  #Fact    : 0
% 3.53/1.60  #Define  : 0
% 3.53/1.60  #Split   : 5
% 3.53/1.60  #Chain   : 0
% 3.53/1.60  #Close   : 0
% 3.53/1.60  
% 3.53/1.60  Ordering : KBO
% 3.53/1.60  
% 3.53/1.60  Simplification rules
% 3.53/1.60  ----------------------
% 3.53/1.60  #Subsume      : 39
% 3.53/1.60  #Demod        : 109
% 3.53/1.60  #Tautology    : 90
% 3.53/1.60  #SimpNegUnit  : 0
% 3.53/1.60  #BackRed      : 3
% 3.53/1.60  
% 3.53/1.60  #Partial instantiations: 0
% 3.53/1.60  #Strategies tried      : 1
% 3.53/1.60  
% 3.53/1.60  Timing (in seconds)
% 3.53/1.60  ----------------------
% 3.53/1.60  Preprocessing        : 0.32
% 3.53/1.60  Parsing              : 0.17
% 3.53/1.60  CNF conversion       : 0.02
% 3.53/1.60  Main loop            : 0.51
% 3.53/1.60  Inferencing          : 0.20
% 3.53/1.60  Reduction            : 0.16
% 3.53/1.60  Demodulation         : 0.12
% 3.53/1.60  BG Simplification    : 0.03
% 3.53/1.60  Subsumption          : 0.07
% 3.53/1.60  Abstraction          : 0.04
% 3.53/1.60  MUC search           : 0.00
% 3.53/1.60  Cooper               : 0.00
% 3.53/1.60  Total                : 0.87
% 3.53/1.61  Index Insertion      : 0.00
% 3.53/1.61  Index Deletion       : 0.00
% 3.53/1.61  Index Matching       : 0.00
% 3.53/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
