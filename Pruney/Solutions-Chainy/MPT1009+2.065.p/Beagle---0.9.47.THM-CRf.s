%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:51 EST 2020

% Result     : Theorem 5.37s
% Output     : CNFRefutation 5.48s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 173 expanded)
%              Number of leaves         :   41 (  76 expanded)
%              Depth                    :    9
%              Number of atoms          :  146 ( 349 expanded)
%              Number of equality atoms :   78 ( 141 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_82,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_155,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_168,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_155])).

tff(c_38,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k9_relat_1(B_20,A_19),k2_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    ! [A_22] :
      ( k1_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_176,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_168,c_44])).

tff(c_189,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2398,plain,(
    ! [B_258,A_259] :
      ( k1_tarski(k1_funct_1(B_258,A_259)) = k2_relat_1(B_258)
      | k1_tarski(A_259) != k1_relat_1(B_258)
      | ~ v1_funct_1(B_258)
      | ~ v1_relat_1(B_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2366,plain,(
    ! [A_250,B_251,C_252,D_253] :
      ( k7_relset_1(A_250,B_251,C_252,D_253) = k9_relat_1(C_252,D_253)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2376,plain,(
    ! [D_253] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_253) = k9_relat_1('#skF_4',D_253) ),
    inference(resolution,[status(thm)],[c_60,c_2366])).

tff(c_56,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2388,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2376,c_56])).

tff(c_2404,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2398,c_2388])).

tff(c_2431,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_64,c_2404])).

tff(c_2433,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2431])).

tff(c_249,plain,(
    ! [C_93,A_94,B_95] :
      ( v4_relat_1(C_93,A_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_262,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_249])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2441,plain,(
    ! [A_263,B_264,C_265,D_266] :
      ( k1_enumset1(A_263,B_264,C_265) = D_266
      | k2_tarski(A_263,C_265) = D_266
      | k2_tarski(B_264,C_265) = D_266
      | k2_tarski(A_263,B_264) = D_266
      | k1_tarski(C_265) = D_266
      | k1_tarski(B_264) = D_266
      | k1_tarski(A_263) = D_266
      | k1_xboole_0 = D_266
      | ~ r1_tarski(D_266,k1_enumset1(A_263,B_264,C_265)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2463,plain,(
    ! [A_2,B_3,D_266] :
      ( k1_enumset1(A_2,A_2,B_3) = D_266
      | k2_tarski(A_2,B_3) = D_266
      | k2_tarski(A_2,B_3) = D_266
      | k2_tarski(A_2,A_2) = D_266
      | k1_tarski(B_3) = D_266
      | k1_tarski(A_2) = D_266
      | k1_tarski(A_2) = D_266
      | k1_xboole_0 = D_266
      | ~ r1_tarski(D_266,k2_tarski(A_2,B_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2441])).

tff(c_2568,plain,(
    ! [A_302,B_303,D_304] :
      ( k2_tarski(A_302,B_303) = D_304
      | k2_tarski(A_302,B_303) = D_304
      | k2_tarski(A_302,B_303) = D_304
      | k1_tarski(A_302) = D_304
      | k1_tarski(B_303) = D_304
      | k1_tarski(A_302) = D_304
      | k1_tarski(A_302) = D_304
      | k1_xboole_0 = D_304
      | ~ r1_tarski(D_304,k2_tarski(A_302,B_303)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_2463])).

tff(c_2607,plain,(
    ! [A_305,B_306,B_307] :
      ( k2_tarski(A_305,B_306) = k1_relat_1(B_307)
      | k1_tarski(B_306) = k1_relat_1(B_307)
      | k1_tarski(A_305) = k1_relat_1(B_307)
      | k1_relat_1(B_307) = k1_xboole_0
      | ~ v4_relat_1(B_307,k2_tarski(A_305,B_306))
      | ~ v1_relat_1(B_307) ) ),
    inference(resolution,[status(thm)],[c_36,c_2568])).

tff(c_2614,plain,(
    ! [A_1,B_307] :
      ( k2_tarski(A_1,A_1) = k1_relat_1(B_307)
      | k1_tarski(A_1) = k1_relat_1(B_307)
      | k1_tarski(A_1) = k1_relat_1(B_307)
      | k1_relat_1(B_307) = k1_xboole_0
      | ~ v4_relat_1(B_307,k1_tarski(A_1))
      | ~ v1_relat_1(B_307) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2607])).

tff(c_2619,plain,(
    ! [A_308,B_309] :
      ( k1_tarski(A_308) = k1_relat_1(B_309)
      | k1_tarski(A_308) = k1_relat_1(B_309)
      | k1_tarski(A_308) = k1_relat_1(B_309)
      | k1_relat_1(B_309) = k1_xboole_0
      | ~ v4_relat_1(B_309,k1_tarski(A_308))
      | ~ v1_relat_1(B_309) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2614])).

tff(c_2625,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_262,c_2619])).

tff(c_2632,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_2625])).

tff(c_2634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_2433,c_2632])).

tff(c_2635,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2431])).

tff(c_2770,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_2635])).

tff(c_2774,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_2770])).

tff(c_2775,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_26,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_86,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_98,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(resolution,[status(thm)],[c_26,c_86])).

tff(c_2779,plain,(
    ! [A_11] : r1_tarski('#skF_4',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2775,c_98])).

tff(c_40,plain,(
    ! [A_21] : k9_relat_1(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2781,plain,(
    ! [A_21] : k9_relat_1('#skF_4',A_21) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2775,c_2775,c_40])).

tff(c_2782,plain,(
    ! [A_11] : m1_subset_1('#skF_4',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2775,c_26])).

tff(c_2957,plain,(
    ! [A_360,B_361,C_362,D_363] :
      ( k7_relset_1(A_360,B_361,C_362,D_363) = k9_relat_1(C_362,D_363)
      | ~ m1_subset_1(C_362,k1_zfmisc_1(k2_zfmisc_1(A_360,B_361))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2960,plain,(
    ! [A_360,B_361,D_363] : k7_relset_1(A_360,B_361,'#skF_4',D_363) = k9_relat_1('#skF_4',D_363) ),
    inference(resolution,[status(thm)],[c_2782,c_2957])).

tff(c_2965,plain,(
    ! [A_360,B_361,D_363] : k7_relset_1(A_360,B_361,'#skF_4',D_363) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2781,c_2960])).

tff(c_2967,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2965,c_56])).

tff(c_2970,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2779,c_2967])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.37/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.37/2.07  
% 5.37/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.37/2.08  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.37/2.08  
% 5.37/2.08  %Foreground sorts:
% 5.37/2.08  
% 5.37/2.08  
% 5.37/2.08  %Background operators:
% 5.37/2.08  
% 5.37/2.08  
% 5.37/2.08  %Foreground operators:
% 5.37/2.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.37/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.37/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.37/2.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.37/2.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.37/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.37/2.08  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.37/2.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.37/2.08  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.37/2.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.37/2.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.37/2.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.37/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.37/2.08  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.37/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.37/2.08  tff('#skF_1', type, '#skF_1': $i).
% 5.37/2.08  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.37/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.37/2.08  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.37/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.37/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.37/2.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.37/2.08  tff('#skF_4', type, '#skF_4': $i).
% 5.37/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.37/2.08  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.37/2.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.37/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.37/2.08  
% 5.48/2.09  tff(f_124, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 5.48/2.09  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.48/2.09  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 5.48/2.09  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.48/2.09  tff(f_98, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 5.48/2.09  tff(f_112, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.48/2.09  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.48/2.09  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.48/2.09  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.48/2.09  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.48/2.09  tff(f_58, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 5.48/2.09  tff(f_60, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.48/2.09  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.48/2.09  tff(f_82, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 5.48/2.09  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.48/2.09  tff(c_155, plain, (![C_71, A_72, B_73]: (v1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.48/2.09  tff(c_168, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_155])).
% 5.48/2.09  tff(c_38, plain, (![B_20, A_19]: (r1_tarski(k9_relat_1(B_20, A_19), k2_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.48/2.09  tff(c_44, plain, (![A_22]: (k1_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.48/2.09  tff(c_176, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_168, c_44])).
% 5.48/2.09  tff(c_189, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_176])).
% 5.48/2.09  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.48/2.09  tff(c_2398, plain, (![B_258, A_259]: (k1_tarski(k1_funct_1(B_258, A_259))=k2_relat_1(B_258) | k1_tarski(A_259)!=k1_relat_1(B_258) | ~v1_funct_1(B_258) | ~v1_relat_1(B_258))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.48/2.09  tff(c_2366, plain, (![A_250, B_251, C_252, D_253]: (k7_relset_1(A_250, B_251, C_252, D_253)=k9_relat_1(C_252, D_253) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.48/2.09  tff(c_2376, plain, (![D_253]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_253)=k9_relat_1('#skF_4', D_253))), inference(resolution, [status(thm)], [c_60, c_2366])).
% 5.48/2.09  tff(c_56, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.48/2.09  tff(c_2388, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2376, c_56])).
% 5.48/2.09  tff(c_2404, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2398, c_2388])).
% 5.48/2.09  tff(c_2431, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_64, c_2404])).
% 5.48/2.09  tff(c_2433, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2431])).
% 5.48/2.09  tff(c_249, plain, (![C_93, A_94, B_95]: (v4_relat_1(C_93, A_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.48/2.09  tff(c_262, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_249])).
% 5.48/2.09  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.48/2.09  tff(c_36, plain, (![B_18, A_17]: (r1_tarski(k1_relat_1(B_18), A_17) | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.48/2.09  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.48/2.09  tff(c_2441, plain, (![A_263, B_264, C_265, D_266]: (k1_enumset1(A_263, B_264, C_265)=D_266 | k2_tarski(A_263, C_265)=D_266 | k2_tarski(B_264, C_265)=D_266 | k2_tarski(A_263, B_264)=D_266 | k1_tarski(C_265)=D_266 | k1_tarski(B_264)=D_266 | k1_tarski(A_263)=D_266 | k1_xboole_0=D_266 | ~r1_tarski(D_266, k1_enumset1(A_263, B_264, C_265)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.48/2.09  tff(c_2463, plain, (![A_2, B_3, D_266]: (k1_enumset1(A_2, A_2, B_3)=D_266 | k2_tarski(A_2, B_3)=D_266 | k2_tarski(A_2, B_3)=D_266 | k2_tarski(A_2, A_2)=D_266 | k1_tarski(B_3)=D_266 | k1_tarski(A_2)=D_266 | k1_tarski(A_2)=D_266 | k1_xboole_0=D_266 | ~r1_tarski(D_266, k2_tarski(A_2, B_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2441])).
% 5.48/2.09  tff(c_2568, plain, (![A_302, B_303, D_304]: (k2_tarski(A_302, B_303)=D_304 | k2_tarski(A_302, B_303)=D_304 | k2_tarski(A_302, B_303)=D_304 | k1_tarski(A_302)=D_304 | k1_tarski(B_303)=D_304 | k1_tarski(A_302)=D_304 | k1_tarski(A_302)=D_304 | k1_xboole_0=D_304 | ~r1_tarski(D_304, k2_tarski(A_302, B_303)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_2463])).
% 5.48/2.09  tff(c_2607, plain, (![A_305, B_306, B_307]: (k2_tarski(A_305, B_306)=k1_relat_1(B_307) | k1_tarski(B_306)=k1_relat_1(B_307) | k1_tarski(A_305)=k1_relat_1(B_307) | k1_relat_1(B_307)=k1_xboole_0 | ~v4_relat_1(B_307, k2_tarski(A_305, B_306)) | ~v1_relat_1(B_307))), inference(resolution, [status(thm)], [c_36, c_2568])).
% 5.48/2.09  tff(c_2614, plain, (![A_1, B_307]: (k2_tarski(A_1, A_1)=k1_relat_1(B_307) | k1_tarski(A_1)=k1_relat_1(B_307) | k1_tarski(A_1)=k1_relat_1(B_307) | k1_relat_1(B_307)=k1_xboole_0 | ~v4_relat_1(B_307, k1_tarski(A_1)) | ~v1_relat_1(B_307))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2607])).
% 5.48/2.09  tff(c_2619, plain, (![A_308, B_309]: (k1_tarski(A_308)=k1_relat_1(B_309) | k1_tarski(A_308)=k1_relat_1(B_309) | k1_tarski(A_308)=k1_relat_1(B_309) | k1_relat_1(B_309)=k1_xboole_0 | ~v4_relat_1(B_309, k1_tarski(A_308)) | ~v1_relat_1(B_309))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2614])).
% 5.48/2.09  tff(c_2625, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_262, c_2619])).
% 5.48/2.09  tff(c_2632, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_168, c_2625])).
% 5.48/2.09  tff(c_2634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_2433, c_2632])).
% 5.48/2.09  tff(c_2635, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2431])).
% 5.48/2.09  tff(c_2770, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_2635])).
% 5.48/2.09  tff(c_2774, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_168, c_2770])).
% 5.48/2.09  tff(c_2775, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_176])).
% 5.48/2.09  tff(c_26, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.48/2.09  tff(c_86, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.48/2.09  tff(c_98, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(resolution, [status(thm)], [c_26, c_86])).
% 5.48/2.09  tff(c_2779, plain, (![A_11]: (r1_tarski('#skF_4', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_2775, c_98])).
% 5.48/2.09  tff(c_40, plain, (![A_21]: (k9_relat_1(k1_xboole_0, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.48/2.09  tff(c_2781, plain, (![A_21]: (k9_relat_1('#skF_4', A_21)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2775, c_2775, c_40])).
% 5.48/2.09  tff(c_2782, plain, (![A_11]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_2775, c_26])).
% 5.48/2.09  tff(c_2957, plain, (![A_360, B_361, C_362, D_363]: (k7_relset_1(A_360, B_361, C_362, D_363)=k9_relat_1(C_362, D_363) | ~m1_subset_1(C_362, k1_zfmisc_1(k2_zfmisc_1(A_360, B_361))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.48/2.09  tff(c_2960, plain, (![A_360, B_361, D_363]: (k7_relset_1(A_360, B_361, '#skF_4', D_363)=k9_relat_1('#skF_4', D_363))), inference(resolution, [status(thm)], [c_2782, c_2957])).
% 5.48/2.09  tff(c_2965, plain, (![A_360, B_361, D_363]: (k7_relset_1(A_360, B_361, '#skF_4', D_363)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2781, c_2960])).
% 5.48/2.09  tff(c_2967, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2965, c_56])).
% 5.48/2.09  tff(c_2970, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2779, c_2967])).
% 5.48/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.48/2.09  
% 5.48/2.09  Inference rules
% 5.48/2.09  ----------------------
% 5.48/2.09  #Ref     : 0
% 5.48/2.09  #Sup     : 485
% 5.48/2.09  #Fact    : 6
% 5.48/2.09  #Define  : 0
% 5.48/2.09  #Split   : 8
% 5.48/2.09  #Chain   : 0
% 5.48/2.09  #Close   : 0
% 5.48/2.09  
% 5.48/2.09  Ordering : KBO
% 5.48/2.09  
% 5.48/2.09  Simplification rules
% 5.48/2.09  ----------------------
% 5.48/2.09  #Subsume      : 36
% 5.48/2.09  #Demod        : 1377
% 5.48/2.09  #Tautology    : 261
% 5.48/2.09  #SimpNegUnit  : 39
% 5.48/2.09  #BackRed      : 180
% 5.48/2.09  
% 5.48/2.09  #Partial instantiations: 0
% 5.48/2.09  #Strategies tried      : 1
% 5.48/2.09  
% 5.48/2.09  Timing (in seconds)
% 5.48/2.09  ----------------------
% 5.48/2.09  Preprocessing        : 0.41
% 5.48/2.09  Parsing              : 0.21
% 5.48/2.09  CNF conversion       : 0.02
% 5.48/2.09  Main loop            : 0.89
% 5.48/2.09  Inferencing          : 0.29
% 5.48/2.09  Reduction            : 0.35
% 5.48/2.09  Demodulation         : 0.26
% 5.48/2.09  BG Simplification    : 0.04
% 5.48/2.09  Subsumption          : 0.15
% 5.48/2.09  Abstraction          : 0.05
% 5.48/2.09  MUC search           : 0.00
% 5.48/2.09  Cooper               : 0.00
% 5.48/2.09  Total                : 1.33
% 5.48/2.09  Index Insertion      : 0.00
% 5.48/2.09  Index Deletion       : 0.00
% 5.48/2.10  Index Matching       : 0.00
% 5.48/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
