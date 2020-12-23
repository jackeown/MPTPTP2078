%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:50 EST 2020

% Result     : Theorem 7.20s
% Output     : CNFRefutation 7.52s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 281 expanded)
%              Number of leaves         :   47 ( 113 expanded)
%              Depth                    :   15
%              Number of atoms          :  189 ( 604 expanded)
%              Number of equality atoms :   85 ( 205 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k4_mcart_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_124,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_140,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_62,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_163,plain,(
    ! [C_94,A_95,B_96] :
      ( v1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_171,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_163])).

tff(c_44,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k9_relat_1(B_25,A_24),k2_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_48,plain,(
    ! [A_26] :
      ( k1_relat_1(A_26) != k1_xboole_0
      | k1_xboole_0 = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_188,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_171,c_48])).

tff(c_200,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_76,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_348,plain,(
    ! [B_152,A_153] :
      ( k1_tarski(k1_funct_1(B_152,A_153)) = k2_relat_1(B_152)
      | k1_tarski(A_153) != k1_relat_1(B_152)
      | ~ v1_funct_1(B_152)
      | ~ v1_relat_1(B_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_68,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_354,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k2_relat_1('#skF_6'))
    | k1_tarski('#skF_3') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_68])).

tff(c_381,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k2_relat_1('#skF_6'))
    | k1_tarski('#skF_3') != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_76,c_354])).

tff(c_423,plain,(
    k1_tarski('#skF_3') != k1_relat_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_381])).

tff(c_233,plain,(
    ! [C_111,A_112,B_113] :
      ( v4_relat_1(C_111,A_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_241,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_233])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_705,plain,(
    ! [A_195,B_196,C_197,D_198] :
      ( k1_enumset1(A_195,B_196,C_197) = D_198
      | k2_tarski(A_195,C_197) = D_198
      | k2_tarski(B_196,C_197) = D_198
      | k2_tarski(A_195,B_196) = D_198
      | k1_tarski(C_197) = D_198
      | k1_tarski(B_196) = D_198
      | k1_tarski(A_195) = D_198
      | k1_xboole_0 = D_198
      | ~ r1_tarski(D_198,k1_enumset1(A_195,B_196,C_197)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_733,plain,(
    ! [A_3,B_4,D_198] :
      ( k1_enumset1(A_3,A_3,B_4) = D_198
      | k2_tarski(A_3,B_4) = D_198
      | k2_tarski(A_3,B_4) = D_198
      | k2_tarski(A_3,A_3) = D_198
      | k1_tarski(B_4) = D_198
      | k1_tarski(A_3) = D_198
      | k1_tarski(A_3) = D_198
      | k1_xboole_0 = D_198
      | ~ r1_tarski(D_198,k2_tarski(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_705])).

tff(c_5262,plain,(
    ! [A_385,B_386,D_387] :
      ( k2_tarski(A_385,B_386) = D_387
      | k2_tarski(A_385,B_386) = D_387
      | k2_tarski(A_385,B_386) = D_387
      | k1_tarski(A_385) = D_387
      | k1_tarski(B_386) = D_387
      | k1_tarski(A_385) = D_387
      | k1_tarski(A_385) = D_387
      | k1_xboole_0 = D_387
      | ~ r1_tarski(D_387,k2_tarski(A_385,B_386)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_733])).

tff(c_5386,plain,(
    ! [A_392,B_393,B_394] :
      ( k2_tarski(A_392,B_393) = k1_relat_1(B_394)
      | k1_tarski(B_393) = k1_relat_1(B_394)
      | k1_tarski(A_392) = k1_relat_1(B_394)
      | k1_relat_1(B_394) = k1_xboole_0
      | ~ v4_relat_1(B_394,k2_tarski(A_392,B_393))
      | ~ v1_relat_1(B_394) ) ),
    inference(resolution,[status(thm)],[c_34,c_5262])).

tff(c_5393,plain,(
    ! [A_2,B_394] :
      ( k2_tarski(A_2,A_2) = k1_relat_1(B_394)
      | k1_tarski(A_2) = k1_relat_1(B_394)
      | k1_tarski(A_2) = k1_relat_1(B_394)
      | k1_relat_1(B_394) = k1_xboole_0
      | ~ v4_relat_1(B_394,k1_tarski(A_2))
      | ~ v1_relat_1(B_394) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_5386])).

tff(c_5398,plain,(
    ! [A_395,B_396] :
      ( k1_tarski(A_395) = k1_relat_1(B_396)
      | k1_tarski(A_395) = k1_relat_1(B_396)
      | k1_tarski(A_395) = k1_relat_1(B_396)
      | k1_relat_1(B_396) = k1_xboole_0
      | ~ v4_relat_1(B_396,k1_tarski(A_395))
      | ~ v1_relat_1(B_396) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_5393])).

tff(c_5408,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_241,c_5398])).

tff(c_5414,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_5408])).

tff(c_5416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_423,c_5414])).

tff(c_5418,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_381])).

tff(c_5422,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5418,c_72])).

tff(c_60,plain,(
    ! [A_37,B_38,C_39,D_40] :
      ( k7_relset_1(A_37,B_38,C_39,D_40) = k9_relat_1(C_39,D_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_5512,plain,(
    ! [D_40] : k7_relset_1(k1_relat_1('#skF_6'),'#skF_4','#skF_6',D_40) = k9_relat_1('#skF_6',D_40) ),
    inference(resolution,[status(thm)],[c_5422,c_60])).

tff(c_5417,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_381])).

tff(c_5637,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_6'),'#skF_4','#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5418,c_5417])).

tff(c_5639,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5512,c_5637])).

tff(c_5675,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_5639])).

tff(c_5679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_5675])).

tff(c_5680,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_5688,plain,(
    ! [A_1] : r1_tarski('#skF_6',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5680,c_2])).

tff(c_62,plain,(
    ! [A_41] :
      ( r2_hidden('#skF_2'(A_41),A_41)
      | k1_xboole_0 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_5686,plain,(
    ! [A_41] :
      ( r2_hidden('#skF_2'(A_41),A_41)
      | A_41 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5680,c_62])).

tff(c_5825,plain,(
    ! [A_479,B_480,C_481] :
      ( r2_hidden('#skF_1'(A_479,B_480,C_481),B_480)
      | ~ r2_hidden(A_479,k9_relat_1(C_481,B_480))
      | ~ v1_relat_1(C_481) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_52,plain,(
    ! [B_30,A_29] :
      ( ~ r1_tarski(B_30,A_29)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_5840,plain,(
    ! [B_482,A_483,C_484] :
      ( ~ r1_tarski(B_482,'#skF_1'(A_483,B_482,C_484))
      | ~ r2_hidden(A_483,k9_relat_1(C_484,B_482))
      | ~ v1_relat_1(C_484) ) ),
    inference(resolution,[status(thm)],[c_5825,c_52])).

tff(c_5865,plain,(
    ! [A_488,C_489] :
      ( ~ r2_hidden(A_488,k9_relat_1(C_489,'#skF_6'))
      | ~ v1_relat_1(C_489) ) ),
    inference(resolution,[status(thm)],[c_5688,c_5840])).

tff(c_5876,plain,(
    ! [C_490] :
      ( ~ v1_relat_1(C_490)
      | k9_relat_1(C_490,'#skF_6') = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_5686,c_5865])).

tff(c_5880,plain,(
    k9_relat_1('#skF_6','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_171,c_5876])).

tff(c_5848,plain,(
    ! [A_483,C_484] :
      ( ~ r2_hidden(A_483,k9_relat_1(C_484,'#skF_6'))
      | ~ v1_relat_1(C_484) ) ),
    inference(resolution,[status(thm)],[c_5688,c_5840])).

tff(c_5884,plain,(
    ! [A_483] :
      ( ~ r2_hidden(A_483,'#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5880,c_5848])).

tff(c_5891,plain,(
    ! [A_483] : ~ r2_hidden(A_483,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_5884])).

tff(c_5681,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_5696,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5680,c_5681])).

tff(c_5849,plain,(
    ! [A_485,B_486,C_487] :
      ( r2_hidden('#skF_1'(A_485,B_486,C_487),k1_relat_1(C_487))
      | ~ r2_hidden(A_485,k9_relat_1(C_487,B_486))
      | ~ v1_relat_1(C_487) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_5859,plain,(
    ! [A_485,B_486] :
      ( r2_hidden('#skF_1'(A_485,B_486,'#skF_6'),'#skF_6')
      | ~ r2_hidden(A_485,k9_relat_1('#skF_6',B_486))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5696,c_5849])).

tff(c_5864,plain,(
    ! [A_485,B_486] :
      ( r2_hidden('#skF_1'(A_485,B_486,'#skF_6'),'#skF_6')
      | ~ r2_hidden(A_485,k9_relat_1('#skF_6',B_486)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_5859])).

tff(c_5908,plain,(
    ! [A_492,B_493] : ~ r2_hidden(A_492,k9_relat_1('#skF_6',B_493)) ),
    inference(negUnitSimplification,[status(thm)],[c_5891,c_5864])).

tff(c_5920,plain,(
    ! [B_493] : k9_relat_1('#skF_6',B_493) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_5686,c_5908])).

tff(c_28,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_5687,plain,(
    ! [A_12] : m1_subset_1('#skF_6',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5680,c_28])).

tff(c_6037,plain,(
    ! [A_502,B_503,C_504,D_505] :
      ( k7_relset_1(A_502,B_503,C_504,D_505) = k9_relat_1(C_504,D_505)
      | ~ m1_subset_1(C_504,k1_zfmisc_1(k2_zfmisc_1(A_502,B_503))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_6040,plain,(
    ! [A_502,B_503,D_505] : k7_relset_1(A_502,B_503,'#skF_6',D_505) = k9_relat_1('#skF_6',D_505) ),
    inference(resolution,[status(thm)],[c_5687,c_6037])).

tff(c_6042,plain,(
    ! [A_502,B_503,D_505] : k7_relset_1(A_502,B_503,'#skF_6',D_505) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5920,c_6040])).

tff(c_6043,plain,(
    ~ r1_tarski('#skF_6',k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6042,c_68])).

tff(c_6046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5688,c_6043])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:27:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.20/2.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.20/2.47  
% 7.20/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.20/2.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k4_mcart_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 7.20/2.47  
% 7.20/2.47  %Foreground sorts:
% 7.20/2.47  
% 7.20/2.47  
% 7.20/2.47  %Background operators:
% 7.20/2.47  
% 7.20/2.47  
% 7.20/2.47  %Foreground operators:
% 7.20/2.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.20/2.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.20/2.47  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.20/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.20/2.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.20/2.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.20/2.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.20/2.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.20/2.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.20/2.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.20/2.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.20/2.47  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 7.20/2.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.20/2.47  tff('#skF_5', type, '#skF_5': $i).
% 7.20/2.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.20/2.47  tff('#skF_6', type, '#skF_6': $i).
% 7.20/2.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.20/2.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.20/2.47  tff('#skF_3', type, '#skF_3': $i).
% 7.20/2.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.20/2.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.20/2.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.20/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.20/2.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.20/2.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.20/2.47  tff('#skF_4', type, '#skF_4': $i).
% 7.20/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.20/2.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.20/2.47  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 7.20/2.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.20/2.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.20/2.47  
% 7.20/2.49  tff(f_152, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 7.20/2.49  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.20/2.49  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 7.20/2.49  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 7.20/2.49  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 7.20/2.49  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.20/2.49  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.20/2.49  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 7.20/2.49  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.20/2.49  tff(f_60, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 7.20/2.49  tff(f_124, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 7.20/2.49  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.20/2.49  tff(f_140, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 7.20/2.49  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 7.20/2.49  tff(f_110, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.20/2.49  tff(f_62, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 7.20/2.49  tff(c_72, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.20/2.49  tff(c_163, plain, (![C_94, A_95, B_96]: (v1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.20/2.49  tff(c_171, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_72, c_163])).
% 7.20/2.49  tff(c_44, plain, (![B_25, A_24]: (r1_tarski(k9_relat_1(B_25, A_24), k2_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.20/2.49  tff(c_48, plain, (![A_26]: (k1_relat_1(A_26)!=k1_xboole_0 | k1_xboole_0=A_26 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.20/2.49  tff(c_188, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_171, c_48])).
% 7.20/2.49  tff(c_200, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_188])).
% 7.20/2.49  tff(c_76, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.20/2.49  tff(c_348, plain, (![B_152, A_153]: (k1_tarski(k1_funct_1(B_152, A_153))=k2_relat_1(B_152) | k1_tarski(A_153)!=k1_relat_1(B_152) | ~v1_funct_1(B_152) | ~v1_relat_1(B_152))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.20/2.49  tff(c_68, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.20/2.49  tff(c_354, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k2_relat_1('#skF_6')) | k1_tarski('#skF_3')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_348, c_68])).
% 7.20/2.49  tff(c_381, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k2_relat_1('#skF_6')) | k1_tarski('#skF_3')!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_76, c_354])).
% 7.20/2.49  tff(c_423, plain, (k1_tarski('#skF_3')!=k1_relat_1('#skF_6')), inference(splitLeft, [status(thm)], [c_381])).
% 7.20/2.49  tff(c_233, plain, (![C_111, A_112, B_113]: (v4_relat_1(C_111, A_112) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.20/2.49  tff(c_241, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_72, c_233])).
% 7.20/2.49  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.20/2.49  tff(c_34, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.20/2.49  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.20/2.49  tff(c_705, plain, (![A_195, B_196, C_197, D_198]: (k1_enumset1(A_195, B_196, C_197)=D_198 | k2_tarski(A_195, C_197)=D_198 | k2_tarski(B_196, C_197)=D_198 | k2_tarski(A_195, B_196)=D_198 | k1_tarski(C_197)=D_198 | k1_tarski(B_196)=D_198 | k1_tarski(A_195)=D_198 | k1_xboole_0=D_198 | ~r1_tarski(D_198, k1_enumset1(A_195, B_196, C_197)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.20/2.49  tff(c_733, plain, (![A_3, B_4, D_198]: (k1_enumset1(A_3, A_3, B_4)=D_198 | k2_tarski(A_3, B_4)=D_198 | k2_tarski(A_3, B_4)=D_198 | k2_tarski(A_3, A_3)=D_198 | k1_tarski(B_4)=D_198 | k1_tarski(A_3)=D_198 | k1_tarski(A_3)=D_198 | k1_xboole_0=D_198 | ~r1_tarski(D_198, k2_tarski(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_705])).
% 7.20/2.49  tff(c_5262, plain, (![A_385, B_386, D_387]: (k2_tarski(A_385, B_386)=D_387 | k2_tarski(A_385, B_386)=D_387 | k2_tarski(A_385, B_386)=D_387 | k1_tarski(A_385)=D_387 | k1_tarski(B_386)=D_387 | k1_tarski(A_385)=D_387 | k1_tarski(A_385)=D_387 | k1_xboole_0=D_387 | ~r1_tarski(D_387, k2_tarski(A_385, B_386)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_733])).
% 7.20/2.49  tff(c_5386, plain, (![A_392, B_393, B_394]: (k2_tarski(A_392, B_393)=k1_relat_1(B_394) | k1_tarski(B_393)=k1_relat_1(B_394) | k1_tarski(A_392)=k1_relat_1(B_394) | k1_relat_1(B_394)=k1_xboole_0 | ~v4_relat_1(B_394, k2_tarski(A_392, B_393)) | ~v1_relat_1(B_394))), inference(resolution, [status(thm)], [c_34, c_5262])).
% 7.20/2.49  tff(c_5393, plain, (![A_2, B_394]: (k2_tarski(A_2, A_2)=k1_relat_1(B_394) | k1_tarski(A_2)=k1_relat_1(B_394) | k1_tarski(A_2)=k1_relat_1(B_394) | k1_relat_1(B_394)=k1_xboole_0 | ~v4_relat_1(B_394, k1_tarski(A_2)) | ~v1_relat_1(B_394))), inference(superposition, [status(thm), theory('equality')], [c_4, c_5386])).
% 7.20/2.49  tff(c_5398, plain, (![A_395, B_396]: (k1_tarski(A_395)=k1_relat_1(B_396) | k1_tarski(A_395)=k1_relat_1(B_396) | k1_tarski(A_395)=k1_relat_1(B_396) | k1_relat_1(B_396)=k1_xboole_0 | ~v4_relat_1(B_396, k1_tarski(A_395)) | ~v1_relat_1(B_396))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_5393])).
% 7.20/2.49  tff(c_5408, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_241, c_5398])).
% 7.20/2.49  tff(c_5414, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_171, c_5408])).
% 7.20/2.49  tff(c_5416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_200, c_423, c_5414])).
% 7.20/2.49  tff(c_5418, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_381])).
% 7.20/2.49  tff(c_5422, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5418, c_72])).
% 7.20/2.49  tff(c_60, plain, (![A_37, B_38, C_39, D_40]: (k7_relset_1(A_37, B_38, C_39, D_40)=k9_relat_1(C_39, D_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.20/2.49  tff(c_5512, plain, (![D_40]: (k7_relset_1(k1_relat_1('#skF_6'), '#skF_4', '#skF_6', D_40)=k9_relat_1('#skF_6', D_40))), inference(resolution, [status(thm)], [c_5422, c_60])).
% 7.20/2.49  tff(c_5417, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_381])).
% 7.20/2.49  tff(c_5637, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_6'), '#skF_4', '#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5418, c_5417])).
% 7.20/2.49  tff(c_5639, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5512, c_5637])).
% 7.20/2.49  tff(c_5675, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_5639])).
% 7.20/2.49  tff(c_5679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_171, c_5675])).
% 7.20/2.49  tff(c_5680, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_188])).
% 7.20/2.49  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.20/2.49  tff(c_5688, plain, (![A_1]: (r1_tarski('#skF_6', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_5680, c_2])).
% 7.20/2.49  tff(c_62, plain, (![A_41]: (r2_hidden('#skF_2'(A_41), A_41) | k1_xboole_0=A_41)), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.20/2.49  tff(c_5686, plain, (![A_41]: (r2_hidden('#skF_2'(A_41), A_41) | A_41='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5680, c_62])).
% 7.20/2.49  tff(c_5825, plain, (![A_479, B_480, C_481]: (r2_hidden('#skF_1'(A_479, B_480, C_481), B_480) | ~r2_hidden(A_479, k9_relat_1(C_481, B_480)) | ~v1_relat_1(C_481))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.20/2.49  tff(c_52, plain, (![B_30, A_29]: (~r1_tarski(B_30, A_29) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.20/2.49  tff(c_5840, plain, (![B_482, A_483, C_484]: (~r1_tarski(B_482, '#skF_1'(A_483, B_482, C_484)) | ~r2_hidden(A_483, k9_relat_1(C_484, B_482)) | ~v1_relat_1(C_484))), inference(resolution, [status(thm)], [c_5825, c_52])).
% 7.20/2.49  tff(c_5865, plain, (![A_488, C_489]: (~r2_hidden(A_488, k9_relat_1(C_489, '#skF_6')) | ~v1_relat_1(C_489))), inference(resolution, [status(thm)], [c_5688, c_5840])).
% 7.20/2.49  tff(c_5876, plain, (![C_490]: (~v1_relat_1(C_490) | k9_relat_1(C_490, '#skF_6')='#skF_6')), inference(resolution, [status(thm)], [c_5686, c_5865])).
% 7.20/2.49  tff(c_5880, plain, (k9_relat_1('#skF_6', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_171, c_5876])).
% 7.20/2.49  tff(c_5848, plain, (![A_483, C_484]: (~r2_hidden(A_483, k9_relat_1(C_484, '#skF_6')) | ~v1_relat_1(C_484))), inference(resolution, [status(thm)], [c_5688, c_5840])).
% 7.20/2.49  tff(c_5884, plain, (![A_483]: (~r2_hidden(A_483, '#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5880, c_5848])).
% 7.20/2.49  tff(c_5891, plain, (![A_483]: (~r2_hidden(A_483, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_5884])).
% 7.20/2.49  tff(c_5681, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_188])).
% 7.20/2.49  tff(c_5696, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5680, c_5681])).
% 7.20/2.49  tff(c_5849, plain, (![A_485, B_486, C_487]: (r2_hidden('#skF_1'(A_485, B_486, C_487), k1_relat_1(C_487)) | ~r2_hidden(A_485, k9_relat_1(C_487, B_486)) | ~v1_relat_1(C_487))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.20/2.49  tff(c_5859, plain, (![A_485, B_486]: (r2_hidden('#skF_1'(A_485, B_486, '#skF_6'), '#skF_6') | ~r2_hidden(A_485, k9_relat_1('#skF_6', B_486)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5696, c_5849])).
% 7.20/2.49  tff(c_5864, plain, (![A_485, B_486]: (r2_hidden('#skF_1'(A_485, B_486, '#skF_6'), '#skF_6') | ~r2_hidden(A_485, k9_relat_1('#skF_6', B_486)))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_5859])).
% 7.20/2.49  tff(c_5908, plain, (![A_492, B_493]: (~r2_hidden(A_492, k9_relat_1('#skF_6', B_493)))), inference(negUnitSimplification, [status(thm)], [c_5891, c_5864])).
% 7.20/2.49  tff(c_5920, plain, (![B_493]: (k9_relat_1('#skF_6', B_493)='#skF_6')), inference(resolution, [status(thm)], [c_5686, c_5908])).
% 7.20/2.49  tff(c_28, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.20/2.49  tff(c_5687, plain, (![A_12]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_5680, c_28])).
% 7.20/2.49  tff(c_6037, plain, (![A_502, B_503, C_504, D_505]: (k7_relset_1(A_502, B_503, C_504, D_505)=k9_relat_1(C_504, D_505) | ~m1_subset_1(C_504, k1_zfmisc_1(k2_zfmisc_1(A_502, B_503))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.20/2.49  tff(c_6040, plain, (![A_502, B_503, D_505]: (k7_relset_1(A_502, B_503, '#skF_6', D_505)=k9_relat_1('#skF_6', D_505))), inference(resolution, [status(thm)], [c_5687, c_6037])).
% 7.20/2.49  tff(c_6042, plain, (![A_502, B_503, D_505]: (k7_relset_1(A_502, B_503, '#skF_6', D_505)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5920, c_6040])).
% 7.20/2.49  tff(c_6043, plain, (~r1_tarski('#skF_6', k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_6042, c_68])).
% 7.20/2.49  tff(c_6046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5688, c_6043])).
% 7.52/2.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.52/2.50  
% 7.52/2.50  Inference rules
% 7.52/2.50  ----------------------
% 7.52/2.50  #Ref     : 0
% 7.52/2.50  #Sup     : 1318
% 7.52/2.50  #Fact    : 0
% 7.52/2.50  #Define  : 0
% 7.52/2.50  #Split   : 4
% 7.52/2.50  #Chain   : 0
% 7.52/2.50  #Close   : 0
% 7.52/2.50  
% 7.52/2.50  Ordering : KBO
% 7.52/2.50  
% 7.52/2.50  Simplification rules
% 7.52/2.50  ----------------------
% 7.52/2.50  #Subsume      : 730
% 7.52/2.50  #Demod        : 680
% 7.52/2.50  #Tautology    : 387
% 7.52/2.50  #SimpNegUnit  : 20
% 7.52/2.50  #BackRed      : 20
% 7.52/2.50  
% 7.52/2.50  #Partial instantiations: 0
% 7.52/2.50  #Strategies tried      : 1
% 7.52/2.50  
% 7.52/2.50  Timing (in seconds)
% 7.52/2.50  ----------------------
% 7.52/2.50  Preprocessing        : 0.34
% 7.52/2.50  Parsing              : 0.18
% 7.52/2.50  CNF conversion       : 0.02
% 7.52/2.50  Main loop            : 1.38
% 7.52/2.50  Inferencing          : 0.39
% 7.52/2.50  Reduction            : 0.37
% 7.52/2.50  Demodulation         : 0.29
% 7.52/2.50  BG Simplification    : 0.04
% 7.52/2.50  Subsumption          : 0.53
% 7.52/2.50  Abstraction          : 0.05
% 7.52/2.50  MUC search           : 0.00
% 7.52/2.50  Cooper               : 0.00
% 7.52/2.50  Total                : 1.77
% 7.52/2.50  Index Insertion      : 0.00
% 7.52/2.50  Index Deletion       : 0.00
% 7.52/2.50  Index Matching       : 0.00
% 7.52/2.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
