%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:36 EST 2020

% Result     : Theorem 9.85s
% Output     : CNFRefutation 9.85s
% Verified   : 
% Statistics : Number of formulae       :  178 (2520 expanded)
%              Number of leaves         :   50 ( 742 expanded)
%              Depth                    :   16
%              Number of atoms          :  272 (6479 expanded)
%              Number of equality atoms :   71 ( 752 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_203,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ~ v1_xboole_0(D)
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,A,D)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,D))) )
           => ( ( r1_tarski(B,A)
                & r1_tarski(k7_relset_1(A,D,E,B),C) )
             => ( v1_funct_1(k2_partfun1(A,D,E,B))
                & v1_funct_2(k2_partfun1(A,D,E,B),B,C)
                & m1_subset_1(k2_partfun1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_118,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_182,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_176,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_168,axiom,(
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

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(c_34,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_90,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_220,plain,(
    ! [B_106,A_107] :
      ( v1_relat_1(B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_107))
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_226,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_6')) ),
    inference(resolution,[status(thm)],[c_90,c_220])).

tff(c_230,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_226])).

tff(c_38,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_28,A_27)),A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_9779,plain,(
    ! [A_832,B_833,C_834,D_835] :
      ( k7_relset_1(A_832,B_833,C_834,D_835) = k9_relat_1(C_834,D_835)
      | ~ m1_subset_1(C_834,k1_zfmisc_1(k2_zfmisc_1(A_832,B_833))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_9788,plain,(
    ! [D_835] : k7_relset_1('#skF_3','#skF_6','#skF_7',D_835) = k9_relat_1('#skF_7',D_835) ),
    inference(resolution,[status(thm)],[c_90,c_9779])).

tff(c_86,plain,(
    r1_tarski(k7_relset_1('#skF_3','#skF_6','#skF_7','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_9848,plain,(
    r1_tarski(k9_relat_1('#skF_7','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9788,c_86])).

tff(c_36,plain,(
    ! [B_26,A_25] :
      ( k2_relat_1(k7_relat_1(B_26,A_25)) = k9_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_94,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_11509,plain,(
    ! [A_942,B_943,C_944,D_945] :
      ( k2_partfun1(A_942,B_943,C_944,D_945) = k7_relat_1(C_944,D_945)
      | ~ m1_subset_1(C_944,k1_zfmisc_1(k2_zfmisc_1(A_942,B_943)))
      | ~ v1_funct_1(C_944) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_11520,plain,(
    ! [D_945] :
      ( k2_partfun1('#skF_3','#skF_6','#skF_7',D_945) = k7_relat_1('#skF_7',D_945)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_90,c_11509])).

tff(c_11525,plain,(
    ! [D_945] : k2_partfun1('#skF_3','#skF_6','#skF_7',D_945) = k7_relat_1('#skF_7',D_945) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_11520])).

tff(c_40,plain,(
    ! [B_30,A_29] :
      ( r1_tarski(k7_relat_1(B_30,A_29),B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_242,plain,(
    ! [A_111,B_112] :
      ( v1_relat_1(A_111)
      | ~ v1_relat_1(B_112)
      | ~ r1_tarski(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_24,c_220])).

tff(c_262,plain,(
    ! [B_30,A_29] :
      ( v1_relat_1(k7_relat_1(B_30,A_29))
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_40,c_242])).

tff(c_11367,plain,(
    ! [A_920,B_921,C_922,D_923] :
      ( k2_partfun1(A_920,B_921,C_922,D_923) = k7_relat_1(C_922,D_923)
      | ~ m1_subset_1(C_922,k1_zfmisc_1(k2_zfmisc_1(A_920,B_921)))
      | ~ v1_funct_1(C_922) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_11378,plain,(
    ! [D_923] :
      ( k2_partfun1('#skF_3','#skF_6','#skF_7',D_923) = k7_relat_1('#skF_7',D_923)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_90,c_11367])).

tff(c_11383,plain,(
    ! [D_923] : k2_partfun1('#skF_3','#skF_6','#skF_7',D_923) = k7_relat_1('#skF_7',D_923) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_11378])).

tff(c_10904,plain,(
    ! [C_897,A_898,B_899] :
      ( m1_subset_1(C_897,k1_zfmisc_1(k2_zfmisc_1(A_898,B_899)))
      | ~ r1_tarski(k2_relat_1(C_897),B_899)
      | ~ r1_tarski(k1_relat_1(C_897),A_898)
      | ~ v1_relat_1(C_897) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1121,plain,(
    ! [A_227,B_228,C_229,D_230] :
      ( v1_funct_1(k2_partfun1(A_227,B_228,C_229,D_230))
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_227,B_228)))
      | ~ v1_funct_1(C_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1126,plain,(
    ! [D_230] :
      ( v1_funct_1(k2_partfun1('#skF_3','#skF_6','#skF_7',D_230))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_90,c_1121])).

tff(c_1130,plain,(
    ! [D_230] : v1_funct_1(k2_partfun1('#skF_3','#skF_6','#skF_7',D_230)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1126])).

tff(c_84,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),'#skF_4','#skF_5')
    | ~ v1_funct_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_265,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_1284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_265])).

tff(c_1285,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),'#skF_4','#skF_5')
    | ~ m1_subset_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_8778,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1285])).

tff(c_10962,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')),'#skF_5')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(resolution,[status(thm)],[c_10904,c_8778])).

tff(c_11290,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_10962])).

tff(c_11384,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_7','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11383,c_11290])).

tff(c_11401,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_262,c_11384])).

tff(c_11405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_11401])).

tff(c_11406,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')),'#skF_4')
    | ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_10962])).

tff(c_11793,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_7','#skF_4')),'#skF_4')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_7','#skF_4')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11525,c_11525,c_11406])).

tff(c_11794,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_7','#skF_4')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_11793])).

tff(c_11797,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_7','#skF_4'),'#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_11794])).

tff(c_11803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_9848,c_11797])).

tff(c_11804,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_7','#skF_4')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_11793])).

tff(c_11850,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_11804])).

tff(c_11862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_11850])).

tff(c_11864,plain,(
    m1_subset_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1285])).

tff(c_16666,plain,(
    ! [C_1290,B_1291,A_1292] :
      ( v1_xboole_0(C_1290)
      | ~ m1_subset_1(C_1290,k1_zfmisc_1(k2_zfmisc_1(B_1291,A_1292)))
      | ~ v1_xboole_0(A_1292) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_16677,plain,
    ( v1_xboole_0(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_11864,c_16666])).

tff(c_16680,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_16677])).

tff(c_96,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_88,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_92,plain,(
    v1_funct_2('#skF_7','#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_17032,plain,(
    ! [A_1306,B_1307,C_1308] :
      ( k1_relset_1(A_1306,B_1307,C_1308) = k1_relat_1(C_1308)
      | ~ m1_subset_1(C_1308,k1_zfmisc_1(k2_zfmisc_1(A_1306,B_1307))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_17048,plain,(
    k1_relset_1('#skF_3','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_90,c_17032])).

tff(c_19494,plain,(
    ! [B_1432,A_1433,C_1434] :
      ( k1_xboole_0 = B_1432
      | k1_relset_1(A_1433,B_1432,C_1434) = A_1433
      | ~ v1_funct_2(C_1434,A_1433,B_1432)
      | ~ m1_subset_1(C_1434,k1_zfmisc_1(k2_zfmisc_1(A_1433,B_1432))) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_19516,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_3','#skF_6','#skF_7') = '#skF_3'
    | ~ v1_funct_2('#skF_7','#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_90,c_19494])).

tff(c_19525,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_17048,c_19516])).

tff(c_19526,plain,(
    k1_relat_1('#skF_7') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_19525])).

tff(c_42,plain,(
    ! [B_32,A_31] :
      ( k1_relat_1(k7_relat_1(B_32,A_31)) = A_31
      | ~ r1_tarski(A_31,k1_relat_1(B_32))
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_19546,plain,(
    ! [A_31] :
      ( k1_relat_1(k7_relat_1('#skF_7',A_31)) = A_31
      | ~ r1_tarski(A_31,'#skF_3')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19526,c_42])).

tff(c_20031,plain,(
    ! [A_1455] :
      ( k1_relat_1(k7_relat_1('#skF_7',A_1455)) = A_1455
      | ~ r1_tarski(A_1455,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_19546])).

tff(c_18713,plain,(
    ! [A_1394,B_1395,C_1396,D_1397] :
      ( k2_partfun1(A_1394,B_1395,C_1396,D_1397) = k7_relat_1(C_1396,D_1397)
      | ~ m1_subset_1(C_1396,k1_zfmisc_1(k2_zfmisc_1(A_1394,B_1395)))
      | ~ v1_funct_1(C_1396) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_18726,plain,(
    ! [D_1397] :
      ( k2_partfun1('#skF_3','#skF_6','#skF_7',D_1397) = k7_relat_1('#skF_7',D_1397)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_90,c_18713])).

tff(c_18733,plain,(
    ! [D_1397] : k2_partfun1('#skF_3','#skF_6','#skF_7',D_1397) = k7_relat_1('#skF_7',D_1397) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_18726])).

tff(c_11863,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),'#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1285])).

tff(c_18745,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_7','#skF_4'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18733,c_11863])).

tff(c_17046,plain,(
    k1_relset_1('#skF_4','#skF_5',k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) = k1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(resolution,[status(thm)],[c_11864,c_17032])).

tff(c_18737,plain,(
    k1_relset_1('#skF_4','#skF_5',k7_relat_1('#skF_7','#skF_4')) = k1_relat_1(k7_relat_1('#skF_7','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18733,c_18733,c_17046])).

tff(c_18744,plain,(
    m1_subset_1(k7_relat_1('#skF_7','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18733,c_11864])).

tff(c_19263,plain,(
    ! [B_1421,C_1422,A_1423] :
      ( k1_xboole_0 = B_1421
      | v1_funct_2(C_1422,A_1423,B_1421)
      | k1_relset_1(A_1423,B_1421,C_1422) != A_1423
      | ~ m1_subset_1(C_1422,k1_zfmisc_1(k2_zfmisc_1(A_1423,B_1421))) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_19266,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_funct_2(k7_relat_1('#skF_7','#skF_4'),'#skF_4','#skF_5')
    | k1_relset_1('#skF_4','#skF_5',k7_relat_1('#skF_7','#skF_4')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_18744,c_19263])).

tff(c_19287,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_funct_2(k7_relat_1('#skF_7','#skF_4'),'#skF_4','#skF_5')
    | k1_relat_1(k7_relat_1('#skF_7','#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18737,c_19266])).

tff(c_19288,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1(k7_relat_1('#skF_7','#skF_4')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_18745,c_19287])).

tff(c_19294,plain,(
    k1_relat_1(k7_relat_1('#skF_7','#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_19288])).

tff(c_20047,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20031,c_19294])).

tff(c_20153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_20047])).

tff(c_20154,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_19525])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20208,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20154,c_12])).

tff(c_20210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_20208])).

tff(c_20211,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_19288])).

tff(c_20262,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20211,c_12])).

tff(c_20265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16680,c_20262])).

tff(c_20266,plain,(
    v1_xboole_0(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_16677])).

tff(c_20267,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_16677])).

tff(c_11882,plain,(
    ! [A_960,B_961] :
      ( r2_hidden('#skF_2'(A_960,B_961),A_960)
      | r1_tarski(A_960,B_961) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_11893,plain,(
    ! [A_962,B_963] :
      ( ~ v1_xboole_0(A_962)
      | r1_tarski(A_962,B_963) ) ),
    inference(resolution,[status(thm)],[c_11882,c_2])).

tff(c_20,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_11907,plain,(
    ! [A_962] :
      ( k1_xboole_0 = A_962
      | ~ v1_xboole_0(A_962) ) ),
    inference(resolution,[status(thm)],[c_11893,c_20])).

tff(c_20347,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_20267,c_11907])).

tff(c_20484,plain,(
    ! [A_1464] :
      ( A_1464 = '#skF_5'
      | ~ v1_xboole_0(A_1464) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20347,c_11907])).

tff(c_20494,plain,(
    k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_20266,c_20484])).

tff(c_20669,plain,(
    ~ v1_funct_2('#skF_5','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20494,c_11863])).

tff(c_20668,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20494,c_11864])).

tff(c_66,plain,(
    ! [A_60] :
      ( v1_funct_2(k1_xboole_0,A_60,k1_xboole_0)
      | k1_xboole_0 = A_60
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_60,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_20546,plain,(
    ! [A_60] :
      ( v1_funct_2('#skF_5',A_60,'#skF_5')
      | A_60 = '#skF_5'
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_60,'#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20347,c_20347,c_20347,c_20347,c_20347,c_66])).

tff(c_20705,plain,
    ( v1_funct_2('#skF_5','#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20668,c_20546])).

tff(c_20735,plain,(
    '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_20669,c_20705])).

tff(c_20758,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20735,c_20735,c_20669])).

tff(c_113,plain,(
    ! [B_79,A_80] :
      ( r1_tarski(k7_relat_1(B_79,A_80),B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_118,plain,(
    ! [A_80] :
      ( k7_relat_1(k1_xboole_0,A_80) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_113,c_20])).

tff(c_119,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_172,plain,(
    ! [A_96,B_97] :
      ( r2_hidden('#skF_2'(A_96,B_97),A_96)
      | r1_tarski(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_177,plain,(
    ! [A_98,B_99] :
      ( ~ v1_xboole_0(A_98)
      | r1_tarski(A_98,B_99) ) ),
    inference(resolution,[status(thm)],[c_172,c_2])).

tff(c_130,plain,(
    ! [C_85,A_86,B_87] :
      ( v1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_138,plain,(
    ! [A_13,A_86,B_87] :
      ( v1_relat_1(A_13)
      | ~ r1_tarski(A_13,k2_zfmisc_1(A_86,B_87)) ) ),
    inference(resolution,[status(thm)],[c_24,c_130])).

tff(c_188,plain,(
    ! [A_100] :
      ( v1_relat_1(A_100)
      | ~ v1_xboole_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_177,c_138])).

tff(c_191,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_188])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_191])).

tff(c_197,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_196,plain,(
    ! [A_80] : k7_relat_1(k1_xboole_0,A_80) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_15974,plain,(
    ! [B_1207,A_1208] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_1207,A_1208)),A_1208)
      | ~ v1_relat_1(B_1207) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_15993,plain,(
    ! [A_80] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_80)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_15974])).

tff(c_16008,plain,(
    ! [A_1212] : r1_tarski(k1_relat_1(k1_xboole_0),A_1212) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_15993])).

tff(c_16029,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16008,c_20])).

tff(c_20362,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20347,c_20347,c_16029])).

tff(c_20462,plain,(
    ! [A_1461,B_1462,C_1463] :
      ( k1_relset_1(A_1461,B_1462,C_1463) = k1_relat_1(C_1463)
      | ~ m1_subset_1(C_1463,k1_zfmisc_1(k2_zfmisc_1(A_1461,B_1462))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_20473,plain,(
    k1_relset_1('#skF_4','#skF_5',k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) = k1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(resolution,[status(thm)],[c_11864,c_20462])).

tff(c_20661,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20494,c_20494,c_20473])).

tff(c_20670,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20362,c_20661])).

tff(c_20757,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20735,c_20735,c_20735,c_20670])).

tff(c_20753,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20735,c_20735,c_20668])).

tff(c_20772,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20735,c_20347])).

tff(c_70,plain,(
    ! [C_62,B_61] :
      ( v1_funct_2(C_62,k1_xboole_0,B_61)
      | k1_relset_1(k1_xboole_0,B_61,C_62) != k1_xboole_0
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_20991,plain,(
    ! [C_62,B_61] :
      ( v1_funct_2(C_62,'#skF_4',B_61)
      | k1_relset_1('#skF_4',B_61,C_62) != '#skF_4'
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_61))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20772,c_20772,c_20772,c_20772,c_70])).

tff(c_21075,plain,
    ( v1_funct_2('#skF_4','#skF_4','#skF_4')
    | k1_relset_1('#skF_4','#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_20753,c_20991])).

tff(c_21108,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20757,c_21075])).

tff(c_21110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20758,c_21108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:16:24 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.85/3.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.85/3.58  
% 9.85/3.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.85/3.59  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 9.85/3.59  
% 9.85/3.59  %Foreground sorts:
% 9.85/3.59  
% 9.85/3.59  
% 9.85/3.59  %Background operators:
% 9.85/3.59  
% 9.85/3.59  
% 9.85/3.59  %Foreground operators:
% 9.85/3.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.85/3.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.85/3.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.85/3.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.85/3.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.85/3.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.85/3.59  tff('#skF_7', type, '#skF_7': $i).
% 9.85/3.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.85/3.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.85/3.59  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 9.85/3.59  tff('#skF_5', type, '#skF_5': $i).
% 9.85/3.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.85/3.59  tff('#skF_6', type, '#skF_6': $i).
% 9.85/3.59  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.85/3.59  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.85/3.59  tff('#skF_3', type, '#skF_3': $i).
% 9.85/3.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.85/3.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.85/3.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.85/3.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.85/3.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.85/3.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.85/3.59  tff('#skF_4', type, '#skF_4': $i).
% 9.85/3.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.85/3.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.85/3.59  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.85/3.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.85/3.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.85/3.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.85/3.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.85/3.59  
% 9.85/3.61  tff(f_75, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.85/3.61  tff(f_203, negated_conjecture, ~(![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_funct_2)).
% 9.85/3.61  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.85/3.61  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 9.85/3.61  tff(f_118, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 9.85/3.61  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 9.85/3.61  tff(f_182, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.85/3.61  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 9.85/3.61  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.85/3.61  tff(f_126, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 9.85/3.61  tff(f_176, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 9.85/3.61  tff(f_110, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 9.85/3.61  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.85/3.61  tff(f_168, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.85/3.61  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 9.85/3.61  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.85/3.61  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.85/3.61  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.85/3.61  tff(f_49, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 9.85/3.61  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.85/3.61  tff(c_34, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.85/3.61  tff(c_90, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.85/3.61  tff(c_220, plain, (![B_106, A_107]: (v1_relat_1(B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(A_107)) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.85/3.61  tff(c_226, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_6'))), inference(resolution, [status(thm)], [c_90, c_220])).
% 9.85/3.61  tff(c_230, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_226])).
% 9.85/3.61  tff(c_38, plain, (![B_28, A_27]: (r1_tarski(k1_relat_1(k7_relat_1(B_28, A_27)), A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.85/3.61  tff(c_9779, plain, (![A_832, B_833, C_834, D_835]: (k7_relset_1(A_832, B_833, C_834, D_835)=k9_relat_1(C_834, D_835) | ~m1_subset_1(C_834, k1_zfmisc_1(k2_zfmisc_1(A_832, B_833))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.85/3.61  tff(c_9788, plain, (![D_835]: (k7_relset_1('#skF_3', '#skF_6', '#skF_7', D_835)=k9_relat_1('#skF_7', D_835))), inference(resolution, [status(thm)], [c_90, c_9779])).
% 9.85/3.61  tff(c_86, plain, (r1_tarski(k7_relset_1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.85/3.61  tff(c_9848, plain, (r1_tarski(k9_relat_1('#skF_7', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9788, c_86])).
% 9.85/3.61  tff(c_36, plain, (![B_26, A_25]: (k2_relat_1(k7_relat_1(B_26, A_25))=k9_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.85/3.61  tff(c_94, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.85/3.61  tff(c_11509, plain, (![A_942, B_943, C_944, D_945]: (k2_partfun1(A_942, B_943, C_944, D_945)=k7_relat_1(C_944, D_945) | ~m1_subset_1(C_944, k1_zfmisc_1(k2_zfmisc_1(A_942, B_943))) | ~v1_funct_1(C_944))), inference(cnfTransformation, [status(thm)], [f_182])).
% 9.85/3.61  tff(c_11520, plain, (![D_945]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_945)=k7_relat_1('#skF_7', D_945) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_90, c_11509])).
% 9.85/3.61  tff(c_11525, plain, (![D_945]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_945)=k7_relat_1('#skF_7', D_945))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_11520])).
% 9.85/3.61  tff(c_40, plain, (![B_30, A_29]: (r1_tarski(k7_relat_1(B_30, A_29), B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.85/3.61  tff(c_24, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.85/3.61  tff(c_242, plain, (![A_111, B_112]: (v1_relat_1(A_111) | ~v1_relat_1(B_112) | ~r1_tarski(A_111, B_112))), inference(resolution, [status(thm)], [c_24, c_220])).
% 9.85/3.61  tff(c_262, plain, (![B_30, A_29]: (v1_relat_1(k7_relat_1(B_30, A_29)) | ~v1_relat_1(B_30))), inference(resolution, [status(thm)], [c_40, c_242])).
% 9.85/3.61  tff(c_11367, plain, (![A_920, B_921, C_922, D_923]: (k2_partfun1(A_920, B_921, C_922, D_923)=k7_relat_1(C_922, D_923) | ~m1_subset_1(C_922, k1_zfmisc_1(k2_zfmisc_1(A_920, B_921))) | ~v1_funct_1(C_922))), inference(cnfTransformation, [status(thm)], [f_182])).
% 9.85/3.61  tff(c_11378, plain, (![D_923]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_923)=k7_relat_1('#skF_7', D_923) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_90, c_11367])).
% 9.85/3.61  tff(c_11383, plain, (![D_923]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_923)=k7_relat_1('#skF_7', D_923))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_11378])).
% 9.85/3.61  tff(c_10904, plain, (![C_897, A_898, B_899]: (m1_subset_1(C_897, k1_zfmisc_1(k2_zfmisc_1(A_898, B_899))) | ~r1_tarski(k2_relat_1(C_897), B_899) | ~r1_tarski(k1_relat_1(C_897), A_898) | ~v1_relat_1(C_897))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.85/3.61  tff(c_1121, plain, (![A_227, B_228, C_229, D_230]: (v1_funct_1(k2_partfun1(A_227, B_228, C_229, D_230)) | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(A_227, B_228))) | ~v1_funct_1(C_229))), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.85/3.61  tff(c_1126, plain, (![D_230]: (v1_funct_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_230)) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_90, c_1121])).
% 9.85/3.61  tff(c_1130, plain, (![D_230]: (v1_funct_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_230)))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1126])).
% 9.85/3.61  tff(c_84, plain, (~m1_subset_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), '#skF_4', '#skF_5') | ~v1_funct_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.85/3.61  tff(c_265, plain, (~v1_funct_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(splitLeft, [status(thm)], [c_84])).
% 9.85/3.61  tff(c_1284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1130, c_265])).
% 9.85/3.61  tff(c_1285, plain, (~v1_funct_2(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), '#skF_4', '#skF_5') | ~m1_subset_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_84])).
% 9.85/3.61  tff(c_8778, plain, (~m1_subset_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_1285])).
% 9.85/3.61  tff(c_10962, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), '#skF_5') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), '#skF_4') | ~v1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(resolution, [status(thm)], [c_10904, c_8778])).
% 9.85/3.61  tff(c_11290, plain, (~v1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(splitLeft, [status(thm)], [c_10962])).
% 9.85/3.61  tff(c_11384, plain, (~v1_relat_1(k7_relat_1('#skF_7', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11383, c_11290])).
% 9.85/3.61  tff(c_11401, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_262, c_11384])).
% 9.85/3.61  tff(c_11405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_230, c_11401])).
% 9.85/3.61  tff(c_11406, plain, (~r1_tarski(k1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), '#skF_4') | ~r1_tarski(k2_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), '#skF_5')), inference(splitRight, [status(thm)], [c_10962])).
% 9.85/3.61  tff(c_11793, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_7', '#skF_4')), '#skF_4') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_7', '#skF_4')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11525, c_11525, c_11406])).
% 9.85/3.61  tff(c_11794, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_7', '#skF_4')), '#skF_5')), inference(splitLeft, [status(thm)], [c_11793])).
% 9.85/3.61  tff(c_11797, plain, (~r1_tarski(k9_relat_1('#skF_7', '#skF_4'), '#skF_5') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_36, c_11794])).
% 9.85/3.61  tff(c_11803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_230, c_9848, c_11797])).
% 9.85/3.61  tff(c_11804, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_7', '#skF_4')), '#skF_4')), inference(splitRight, [status(thm)], [c_11793])).
% 9.85/3.61  tff(c_11850, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_38, c_11804])).
% 9.85/3.61  tff(c_11862, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_230, c_11850])).
% 9.85/3.61  tff(c_11864, plain, (m1_subset_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_1285])).
% 9.85/3.61  tff(c_16666, plain, (![C_1290, B_1291, A_1292]: (v1_xboole_0(C_1290) | ~m1_subset_1(C_1290, k1_zfmisc_1(k2_zfmisc_1(B_1291, A_1292))) | ~v1_xboole_0(A_1292))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.85/3.61  tff(c_16677, plain, (v1_xboole_0(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_11864, c_16666])).
% 9.85/3.61  tff(c_16680, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_16677])).
% 9.85/3.61  tff(c_96, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.85/3.61  tff(c_88, plain, (r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.85/3.61  tff(c_92, plain, (v1_funct_2('#skF_7', '#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.85/3.61  tff(c_17032, plain, (![A_1306, B_1307, C_1308]: (k1_relset_1(A_1306, B_1307, C_1308)=k1_relat_1(C_1308) | ~m1_subset_1(C_1308, k1_zfmisc_1(k2_zfmisc_1(A_1306, B_1307))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.85/3.61  tff(c_17048, plain, (k1_relset_1('#skF_3', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_90, c_17032])).
% 9.85/3.61  tff(c_19494, plain, (![B_1432, A_1433, C_1434]: (k1_xboole_0=B_1432 | k1_relset_1(A_1433, B_1432, C_1434)=A_1433 | ~v1_funct_2(C_1434, A_1433, B_1432) | ~m1_subset_1(C_1434, k1_zfmisc_1(k2_zfmisc_1(A_1433, B_1432))))), inference(cnfTransformation, [status(thm)], [f_168])).
% 9.85/3.61  tff(c_19516, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_3', '#skF_6', '#skF_7')='#skF_3' | ~v1_funct_2('#skF_7', '#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_90, c_19494])).
% 9.85/3.61  tff(c_19525, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_17048, c_19516])).
% 9.85/3.61  tff(c_19526, plain, (k1_relat_1('#skF_7')='#skF_3'), inference(splitLeft, [status(thm)], [c_19525])).
% 9.85/3.61  tff(c_42, plain, (![B_32, A_31]: (k1_relat_1(k7_relat_1(B_32, A_31))=A_31 | ~r1_tarski(A_31, k1_relat_1(B_32)) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.85/3.61  tff(c_19546, plain, (![A_31]: (k1_relat_1(k7_relat_1('#skF_7', A_31))=A_31 | ~r1_tarski(A_31, '#skF_3') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_19526, c_42])).
% 9.85/3.61  tff(c_20031, plain, (![A_1455]: (k1_relat_1(k7_relat_1('#skF_7', A_1455))=A_1455 | ~r1_tarski(A_1455, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_19546])).
% 9.85/3.61  tff(c_18713, plain, (![A_1394, B_1395, C_1396, D_1397]: (k2_partfun1(A_1394, B_1395, C_1396, D_1397)=k7_relat_1(C_1396, D_1397) | ~m1_subset_1(C_1396, k1_zfmisc_1(k2_zfmisc_1(A_1394, B_1395))) | ~v1_funct_1(C_1396))), inference(cnfTransformation, [status(thm)], [f_182])).
% 9.85/3.61  tff(c_18726, plain, (![D_1397]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_1397)=k7_relat_1('#skF_7', D_1397) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_90, c_18713])).
% 9.85/3.61  tff(c_18733, plain, (![D_1397]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_1397)=k7_relat_1('#skF_7', D_1397))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_18726])).
% 9.85/3.61  tff(c_11863, plain, (~v1_funct_2(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_1285])).
% 9.85/3.61  tff(c_18745, plain, (~v1_funct_2(k7_relat_1('#skF_7', '#skF_4'), '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18733, c_11863])).
% 9.85/3.61  tff(c_17046, plain, (k1_relset_1('#skF_4', '#skF_5', k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))=k1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(resolution, [status(thm)], [c_11864, c_17032])).
% 9.85/3.61  tff(c_18737, plain, (k1_relset_1('#skF_4', '#skF_5', k7_relat_1('#skF_7', '#skF_4'))=k1_relat_1(k7_relat_1('#skF_7', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18733, c_18733, c_17046])).
% 9.85/3.61  tff(c_18744, plain, (m1_subset_1(k7_relat_1('#skF_7', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_18733, c_11864])).
% 9.85/3.61  tff(c_19263, plain, (![B_1421, C_1422, A_1423]: (k1_xboole_0=B_1421 | v1_funct_2(C_1422, A_1423, B_1421) | k1_relset_1(A_1423, B_1421, C_1422)!=A_1423 | ~m1_subset_1(C_1422, k1_zfmisc_1(k2_zfmisc_1(A_1423, B_1421))))), inference(cnfTransformation, [status(thm)], [f_168])).
% 9.85/3.61  tff(c_19266, plain, (k1_xboole_0='#skF_5' | v1_funct_2(k7_relat_1('#skF_7', '#skF_4'), '#skF_4', '#skF_5') | k1_relset_1('#skF_4', '#skF_5', k7_relat_1('#skF_7', '#skF_4'))!='#skF_4'), inference(resolution, [status(thm)], [c_18744, c_19263])).
% 9.85/3.61  tff(c_19287, plain, (k1_xboole_0='#skF_5' | v1_funct_2(k7_relat_1('#skF_7', '#skF_4'), '#skF_4', '#skF_5') | k1_relat_1(k7_relat_1('#skF_7', '#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18737, c_19266])).
% 9.85/3.61  tff(c_19288, plain, (k1_xboole_0='#skF_5' | k1_relat_1(k7_relat_1('#skF_7', '#skF_4'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_18745, c_19287])).
% 9.85/3.61  tff(c_19294, plain, (k1_relat_1(k7_relat_1('#skF_7', '#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_19288])).
% 9.85/3.61  tff(c_20047, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20031, c_19294])).
% 9.85/3.61  tff(c_20153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_20047])).
% 9.85/3.61  tff(c_20154, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_19525])).
% 9.85/3.61  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.85/3.61  tff(c_20208, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20154, c_12])).
% 9.85/3.61  tff(c_20210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_20208])).
% 9.85/3.61  tff(c_20211, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_19288])).
% 9.85/3.61  tff(c_20262, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20211, c_12])).
% 9.85/3.61  tff(c_20265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16680, c_20262])).
% 9.85/3.61  tff(c_20266, plain, (v1_xboole_0(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(splitRight, [status(thm)], [c_16677])).
% 9.85/3.61  tff(c_20267, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_16677])).
% 9.85/3.61  tff(c_11882, plain, (![A_960, B_961]: (r2_hidden('#skF_2'(A_960, B_961), A_960) | r1_tarski(A_960, B_961))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.85/3.61  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.85/3.61  tff(c_11893, plain, (![A_962, B_963]: (~v1_xboole_0(A_962) | r1_tarski(A_962, B_963))), inference(resolution, [status(thm)], [c_11882, c_2])).
% 9.85/3.61  tff(c_20, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.85/3.61  tff(c_11907, plain, (![A_962]: (k1_xboole_0=A_962 | ~v1_xboole_0(A_962))), inference(resolution, [status(thm)], [c_11893, c_20])).
% 9.85/3.61  tff(c_20347, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_20267, c_11907])).
% 9.85/3.61  tff(c_20484, plain, (![A_1464]: (A_1464='#skF_5' | ~v1_xboole_0(A_1464))), inference(demodulation, [status(thm), theory('equality')], [c_20347, c_11907])).
% 9.85/3.61  tff(c_20494, plain, (k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_20266, c_20484])).
% 9.85/3.61  tff(c_20669, plain, (~v1_funct_2('#skF_5', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20494, c_11863])).
% 9.85/3.61  tff(c_20668, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_20494, c_11864])).
% 9.85/3.61  tff(c_66, plain, (![A_60]: (v1_funct_2(k1_xboole_0, A_60, k1_xboole_0) | k1_xboole_0=A_60 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_60, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_168])).
% 9.85/3.61  tff(c_20546, plain, (![A_60]: (v1_funct_2('#skF_5', A_60, '#skF_5') | A_60='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_60, '#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_20347, c_20347, c_20347, c_20347, c_20347, c_66])).
% 9.85/3.61  tff(c_20705, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_20668, c_20546])).
% 9.85/3.61  tff(c_20735, plain, ('#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_20669, c_20705])).
% 9.85/3.61  tff(c_20758, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20735, c_20735, c_20669])).
% 9.85/3.61  tff(c_113, plain, (![B_79, A_80]: (r1_tarski(k7_relat_1(B_79, A_80), B_79) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.85/3.61  tff(c_118, plain, (![A_80]: (k7_relat_1(k1_xboole_0, A_80)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_113, c_20])).
% 9.85/3.61  tff(c_119, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_118])).
% 9.85/3.61  tff(c_172, plain, (![A_96, B_97]: (r2_hidden('#skF_2'(A_96, B_97), A_96) | r1_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.85/3.61  tff(c_177, plain, (![A_98, B_99]: (~v1_xboole_0(A_98) | r1_tarski(A_98, B_99))), inference(resolution, [status(thm)], [c_172, c_2])).
% 9.85/3.61  tff(c_130, plain, (![C_85, A_86, B_87]: (v1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.85/3.61  tff(c_138, plain, (![A_13, A_86, B_87]: (v1_relat_1(A_13) | ~r1_tarski(A_13, k2_zfmisc_1(A_86, B_87)))), inference(resolution, [status(thm)], [c_24, c_130])).
% 9.85/3.61  tff(c_188, plain, (![A_100]: (v1_relat_1(A_100) | ~v1_xboole_0(A_100))), inference(resolution, [status(thm)], [c_177, c_138])).
% 9.85/3.61  tff(c_191, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_188])).
% 9.85/3.61  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_191])).
% 9.85/3.61  tff(c_197, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_118])).
% 9.85/3.61  tff(c_196, plain, (![A_80]: (k7_relat_1(k1_xboole_0, A_80)=k1_xboole_0)), inference(splitRight, [status(thm)], [c_118])).
% 9.85/3.61  tff(c_15974, plain, (![B_1207, A_1208]: (r1_tarski(k1_relat_1(k7_relat_1(B_1207, A_1208)), A_1208) | ~v1_relat_1(B_1207))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.85/3.61  tff(c_15993, plain, (![A_80]: (r1_tarski(k1_relat_1(k1_xboole_0), A_80) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_196, c_15974])).
% 9.85/3.61  tff(c_16008, plain, (![A_1212]: (r1_tarski(k1_relat_1(k1_xboole_0), A_1212))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_15993])).
% 9.85/3.61  tff(c_16029, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_16008, c_20])).
% 9.85/3.61  tff(c_20362, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_20347, c_20347, c_16029])).
% 9.85/3.61  tff(c_20462, plain, (![A_1461, B_1462, C_1463]: (k1_relset_1(A_1461, B_1462, C_1463)=k1_relat_1(C_1463) | ~m1_subset_1(C_1463, k1_zfmisc_1(k2_zfmisc_1(A_1461, B_1462))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.85/3.61  tff(c_20473, plain, (k1_relset_1('#skF_4', '#skF_5', k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))=k1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(resolution, [status(thm)], [c_11864, c_20462])).
% 9.85/3.61  tff(c_20661, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20494, c_20494, c_20473])).
% 9.85/3.61  tff(c_20670, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_20362, c_20661])).
% 9.85/3.61  tff(c_20757, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20735, c_20735, c_20735, c_20670])).
% 9.85/3.61  tff(c_20753, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_20735, c_20735, c_20668])).
% 9.85/3.61  tff(c_20772, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20735, c_20347])).
% 9.85/3.61  tff(c_70, plain, (![C_62, B_61]: (v1_funct_2(C_62, k1_xboole_0, B_61) | k1_relset_1(k1_xboole_0, B_61, C_62)!=k1_xboole_0 | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_61))))), inference(cnfTransformation, [status(thm)], [f_168])).
% 9.85/3.61  tff(c_20991, plain, (![C_62, B_61]: (v1_funct_2(C_62, '#skF_4', B_61) | k1_relset_1('#skF_4', B_61, C_62)!='#skF_4' | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_61))))), inference(demodulation, [status(thm), theory('equality')], [c_20772, c_20772, c_20772, c_20772, c_70])).
% 9.85/3.61  tff(c_21075, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4') | k1_relset_1('#skF_4', '#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_20753, c_20991])).
% 9.85/3.61  tff(c_21108, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20757, c_21075])).
% 9.85/3.61  tff(c_21110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20758, c_21108])).
% 9.85/3.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.85/3.61  
% 9.85/3.61  Inference rules
% 9.85/3.61  ----------------------
% 9.85/3.61  #Ref     : 0
% 9.85/3.61  #Sup     : 4543
% 9.85/3.61  #Fact    : 0
% 9.85/3.61  #Define  : 0
% 9.85/3.61  #Split   : 61
% 9.85/3.61  #Chain   : 0
% 9.85/3.61  #Close   : 0
% 9.85/3.61  
% 9.85/3.61  Ordering : KBO
% 9.85/3.61  
% 9.85/3.61  Simplification rules
% 9.85/3.61  ----------------------
% 9.85/3.61  #Subsume      : 851
% 9.85/3.61  #Demod        : 4221
% 9.85/3.61  #Tautology    : 2050
% 9.85/3.61  #SimpNegUnit  : 108
% 9.85/3.61  #BackRed      : 468
% 9.85/3.61  
% 9.85/3.61  #Partial instantiations: 0
% 9.85/3.61  #Strategies tried      : 1
% 9.85/3.61  
% 9.85/3.61  Timing (in seconds)
% 9.85/3.61  ----------------------
% 9.85/3.61  Preprocessing        : 0.40
% 9.85/3.61  Parsing              : 0.21
% 9.85/3.61  CNF conversion       : 0.03
% 9.85/3.61  Main loop            : 2.42
% 9.85/3.61  Inferencing          : 0.74
% 9.85/3.61  Reduction            : 0.90
% 9.85/3.61  Demodulation         : 0.64
% 9.85/3.61  BG Simplification    : 0.08
% 9.85/3.61  Subsumption          : 0.52
% 9.85/3.61  Abstraction          : 0.09
% 9.85/3.61  MUC search           : 0.00
% 9.85/3.61  Cooper               : 0.00
% 9.85/3.61  Total                : 2.87
% 9.85/3.61  Index Insertion      : 0.00
% 9.85/3.61  Index Deletion       : 0.00
% 9.85/3.61  Index Matching       : 0.00
% 9.85/3.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
