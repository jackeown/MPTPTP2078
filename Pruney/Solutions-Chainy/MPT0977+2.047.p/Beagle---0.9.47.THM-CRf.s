%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:51 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 115 expanded)
%              Number of leaves         :   35 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  113 ( 178 expanded)
%              Number of equality atoms :   26 (  30 expanded)
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

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_86,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_72,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_764,plain,(
    ! [A_138,B_139,D_140] :
      ( r2_relset_1(A_138,B_139,D_140,D_140)
      | ~ m1_subset_1(D_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_774,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_764])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_732,plain,(
    ! [B_131,A_132] :
      ( v1_relat_1(B_131)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(A_132))
      | ~ v1_relat_1(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_741,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_732])).

tff(c_748,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_741])).

tff(c_824,plain,(
    ! [A_154,B_155,C_156] :
      ( k2_relset_1(A_154,B_155,C_156) = k2_relat_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_837,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_824])).

tff(c_907,plain,(
    ! [A_161,B_162,C_163] :
      ( m1_subset_1(k2_relset_1(A_161,B_162,C_163),k1_zfmisc_1(B_162))
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_930,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_837,c_907])).

tff(c_939,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_930])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_947,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_939,c_2])).

tff(c_32,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_relat_1(A_10)) = B_11
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_37,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_partfun1(A_10)) = B_11
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12])).

tff(c_950,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_947,c_37])).

tff(c_956,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_748,c_950])).

tff(c_30,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1618,plain,(
    ! [B_237,E_238,F_239,C_236,A_240,D_241] :
      ( k4_relset_1(A_240,B_237,C_236,D_241,E_238,F_239) = k5_relat_1(E_238,F_239)
      | ~ m1_subset_1(F_239,k1_zfmisc_1(k2_zfmisc_1(C_236,D_241)))
      | ~ m1_subset_1(E_238,k1_zfmisc_1(k2_zfmisc_1(A_240,B_237))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2168,plain,(
    ! [A_294,B_295,A_296,E_297] :
      ( k4_relset_1(A_294,B_295,A_296,A_296,E_297,k6_partfun1(A_296)) = k5_relat_1(E_297,k6_partfun1(A_296))
      | ~ m1_subset_1(E_297,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295))) ) ),
    inference(resolution,[status(thm)],[c_30,c_1618])).

tff(c_2194,plain,(
    ! [A_296] : k4_relset_1('#skF_1','#skF_2',A_296,A_296,'#skF_3',k6_partfun1(A_296)) = k5_relat_1('#skF_3',k6_partfun1(A_296)) ),
    inference(resolution,[status(thm)],[c_36,c_2168])).

tff(c_98,plain,(
    ! [A_51,B_52,D_53] :
      ( r2_relset_1(A_51,B_52,D_53,D_53)
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_108,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_98])).

tff(c_67,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_76,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_67])).

tff(c_83,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_76])).

tff(c_159,plain,(
    ! [A_69,B_70,C_71] :
      ( k1_relset_1(A_69,B_70,C_71) = k1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_172,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_159])).

tff(c_253,plain,(
    ! [A_79,B_80,C_81] :
      ( m1_subset_1(k1_relset_1(A_79,B_80,C_81),k1_zfmisc_1(A_79))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_276,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_253])).

tff(c_285,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_276])).

tff(c_293,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_285,c_2])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k5_relat_1(k6_relat_1(A_8),B_9) = B_9
      | ~ r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,(
    ! [A_8,B_9] :
      ( k5_relat_1(k6_partfun1(A_8),B_9) = B_9
      | ~ r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_10])).

tff(c_296,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_293,c_38])).

tff(c_302,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_296])).

tff(c_419,plain,(
    ! [A_95,D_96,B_92,C_91,F_94,E_93] :
      ( k4_relset_1(A_95,B_92,C_91,D_96,E_93,F_94) = k5_relat_1(E_93,F_94)
      | ~ m1_subset_1(F_94,k1_zfmisc_1(k2_zfmisc_1(C_91,D_96)))
      | ~ m1_subset_1(E_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_553,plain,(
    ! [A_109,B_110,E_111] :
      ( k4_relset_1(A_109,B_110,'#skF_1','#skF_2',E_111,'#skF_3') = k5_relat_1(E_111,'#skF_3')
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(resolution,[status(thm)],[c_36,c_419])).

tff(c_584,plain,(
    ! [A_34] : k4_relset_1(A_34,A_34,'#skF_1','#skF_2',k6_partfun1(A_34),'#skF_3') = k5_relat_1(k6_partfun1(A_34),'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_553])).

tff(c_34,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_66,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_726,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_66])).

tff(c_729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_302,c_726])).

tff(c_730,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_2252,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2194,c_730])).

tff(c_2255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_956,c_2252])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:45:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.12/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.94  
% 4.47/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.94  %$ r2_relset_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.47/1.94  
% 4.47/1.94  %Foreground sorts:
% 4.47/1.94  
% 4.47/1.94  
% 4.47/1.94  %Background operators:
% 4.47/1.94  
% 4.47/1.94  
% 4.47/1.94  %Foreground operators:
% 4.47/1.94  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.47/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.47/1.94  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.47/1.94  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.47/1.94  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.47/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.47/1.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.47/1.94  tff('#skF_2', type, '#skF_2': $i).
% 4.47/1.94  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.47/1.94  tff('#skF_3', type, '#skF_3': $i).
% 4.47/1.94  tff('#skF_1', type, '#skF_1': $i).
% 4.47/1.94  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.47/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.47/1.94  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.47/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.47/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.47/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.47/1.94  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.47/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.47/1.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.47/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.47/1.94  
% 4.47/1.96  tff(f_93, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 4.47/1.96  tff(f_80, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.47/1.96  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.47/1.96  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.47/1.96  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.47/1.96  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.47/1.96  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.47/1.96  tff(f_86, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.47/1.96  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 4.47/1.96  tff(f_84, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.47/1.96  tff(f_72, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 4.47/1.96  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.47/1.96  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.47/1.96  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 4.47/1.96  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.47/1.96  tff(c_764, plain, (![A_138, B_139, D_140]: (r2_relset_1(A_138, B_139, D_140, D_140) | ~m1_subset_1(D_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.47/1.96  tff(c_774, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_764])).
% 4.47/1.96  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.47/1.96  tff(c_732, plain, (![B_131, A_132]: (v1_relat_1(B_131) | ~m1_subset_1(B_131, k1_zfmisc_1(A_132)) | ~v1_relat_1(A_132))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.47/1.96  tff(c_741, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_732])).
% 4.47/1.96  tff(c_748, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_741])).
% 4.47/1.96  tff(c_824, plain, (![A_154, B_155, C_156]: (k2_relset_1(A_154, B_155, C_156)=k2_relat_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.47/1.96  tff(c_837, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_824])).
% 4.47/1.96  tff(c_907, plain, (![A_161, B_162, C_163]: (m1_subset_1(k2_relset_1(A_161, B_162, C_163), k1_zfmisc_1(B_162)) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.47/1.96  tff(c_930, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_837, c_907])).
% 4.47/1.96  tff(c_939, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_930])).
% 4.47/1.96  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.47/1.96  tff(c_947, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_939, c_2])).
% 4.47/1.96  tff(c_32, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.47/1.96  tff(c_12, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_relat_1(A_10))=B_11 | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.47/1.96  tff(c_37, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_partfun1(A_10))=B_11 | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12])).
% 4.47/1.96  tff(c_950, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_947, c_37])).
% 4.47/1.96  tff(c_956, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_748, c_950])).
% 4.47/1.96  tff(c_30, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.47/1.96  tff(c_1618, plain, (![B_237, E_238, F_239, C_236, A_240, D_241]: (k4_relset_1(A_240, B_237, C_236, D_241, E_238, F_239)=k5_relat_1(E_238, F_239) | ~m1_subset_1(F_239, k1_zfmisc_1(k2_zfmisc_1(C_236, D_241))) | ~m1_subset_1(E_238, k1_zfmisc_1(k2_zfmisc_1(A_240, B_237))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.47/1.96  tff(c_2168, plain, (![A_294, B_295, A_296, E_297]: (k4_relset_1(A_294, B_295, A_296, A_296, E_297, k6_partfun1(A_296))=k5_relat_1(E_297, k6_partfun1(A_296)) | ~m1_subset_1(E_297, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))))), inference(resolution, [status(thm)], [c_30, c_1618])).
% 4.47/1.96  tff(c_2194, plain, (![A_296]: (k4_relset_1('#skF_1', '#skF_2', A_296, A_296, '#skF_3', k6_partfun1(A_296))=k5_relat_1('#skF_3', k6_partfun1(A_296)))), inference(resolution, [status(thm)], [c_36, c_2168])).
% 4.47/1.96  tff(c_98, plain, (![A_51, B_52, D_53]: (r2_relset_1(A_51, B_52, D_53, D_53) | ~m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.47/1.96  tff(c_108, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_98])).
% 4.47/1.96  tff(c_67, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.47/1.96  tff(c_76, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_67])).
% 4.47/1.96  tff(c_83, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_76])).
% 4.47/1.96  tff(c_159, plain, (![A_69, B_70, C_71]: (k1_relset_1(A_69, B_70, C_71)=k1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.47/1.96  tff(c_172, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_159])).
% 4.47/1.96  tff(c_253, plain, (![A_79, B_80, C_81]: (m1_subset_1(k1_relset_1(A_79, B_80, C_81), k1_zfmisc_1(A_79)) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.47/1.96  tff(c_276, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_172, c_253])).
% 4.47/1.96  tff(c_285, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_276])).
% 4.47/1.96  tff(c_293, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_285, c_2])).
% 4.47/1.96  tff(c_10, plain, (![A_8, B_9]: (k5_relat_1(k6_relat_1(A_8), B_9)=B_9 | ~r1_tarski(k1_relat_1(B_9), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.47/1.96  tff(c_38, plain, (![A_8, B_9]: (k5_relat_1(k6_partfun1(A_8), B_9)=B_9 | ~r1_tarski(k1_relat_1(B_9), A_8) | ~v1_relat_1(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_10])).
% 4.47/1.96  tff(c_296, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_293, c_38])).
% 4.47/1.96  tff(c_302, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_296])).
% 4.47/1.96  tff(c_419, plain, (![A_95, D_96, B_92, C_91, F_94, E_93]: (k4_relset_1(A_95, B_92, C_91, D_96, E_93, F_94)=k5_relat_1(E_93, F_94) | ~m1_subset_1(F_94, k1_zfmisc_1(k2_zfmisc_1(C_91, D_96))) | ~m1_subset_1(E_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_92))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.47/1.96  tff(c_553, plain, (![A_109, B_110, E_111]: (k4_relset_1(A_109, B_110, '#skF_1', '#skF_2', E_111, '#skF_3')=k5_relat_1(E_111, '#skF_3') | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(resolution, [status(thm)], [c_36, c_419])).
% 4.47/1.96  tff(c_584, plain, (![A_34]: (k4_relset_1(A_34, A_34, '#skF_1', '#skF_2', k6_partfun1(A_34), '#skF_3')=k5_relat_1(k6_partfun1(A_34), '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_553])).
% 4.47/1.96  tff(c_34, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.47/1.96  tff(c_66, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_34])).
% 4.47/1.96  tff(c_726, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_584, c_66])).
% 4.47/1.96  tff(c_729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_302, c_726])).
% 4.47/1.96  tff(c_730, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 4.47/1.96  tff(c_2252, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2194, c_730])).
% 4.47/1.96  tff(c_2255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_774, c_956, c_2252])).
% 4.47/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.96  
% 4.47/1.96  Inference rules
% 4.47/1.96  ----------------------
% 4.47/1.96  #Ref     : 0
% 4.47/1.96  #Sup     : 468
% 4.47/1.96  #Fact    : 0
% 4.47/1.96  #Define  : 0
% 4.47/1.96  #Split   : 6
% 4.47/1.96  #Chain   : 0
% 4.47/1.96  #Close   : 0
% 4.47/1.96  
% 4.47/1.96  Ordering : KBO
% 4.47/1.96  
% 4.47/1.96  Simplification rules
% 4.47/1.96  ----------------------
% 4.47/1.96  #Subsume      : 51
% 4.47/1.96  #Demod        : 148
% 4.47/1.96  #Tautology    : 109
% 4.47/1.96  #SimpNegUnit  : 0
% 4.47/1.96  #BackRed      : 6
% 4.47/1.96  
% 4.47/1.96  #Partial instantiations: 0
% 4.47/1.96  #Strategies tried      : 1
% 4.47/1.96  
% 4.47/1.96  Timing (in seconds)
% 4.47/1.96  ----------------------
% 4.47/1.96  Preprocessing        : 0.36
% 4.47/1.96  Parsing              : 0.19
% 4.47/1.96  CNF conversion       : 0.02
% 4.47/1.96  Main loop            : 0.75
% 4.47/1.96  Inferencing          : 0.28
% 4.47/1.96  Reduction            : 0.24
% 4.47/1.96  Demodulation         : 0.18
% 4.47/1.96  BG Simplification    : 0.04
% 4.47/1.96  Subsumption          : 0.11
% 4.47/1.96  Abstraction          : 0.05
% 4.47/1.96  MUC search           : 0.00
% 4.47/1.96  Cooper               : 0.00
% 4.47/1.96  Total                : 1.15
% 4.47/1.96  Index Insertion      : 0.00
% 4.47/1.96  Index Deletion       : 0.00
% 4.47/1.96  Index Matching       : 0.00
% 4.47/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
