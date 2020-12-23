%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:37 EST 2020

% Result     : Theorem 8.46s
% Output     : CNFRefutation 8.46s
% Verified   : 
% Statistics : Number of formulae       :  201 (1081 expanded)
%              Number of leaves         :   47 ( 332 expanded)
%              Depth                    :   15
%              Number of atoms          :  319 (3103 expanded)
%              Number of equality atoms :  106 ( 647 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_156,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_121,axiom,(
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

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_135,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_63,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_129,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_72,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_150,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_163,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_150])).

tff(c_76,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_8031,plain,(
    ! [A_711,B_712,C_713] :
      ( k1_relset_1(A_711,B_712,C_713) = k1_relat_1(C_713)
      | ~ m1_subset_1(C_713,k1_zfmisc_1(k2_zfmisc_1(A_711,B_712))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8050,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_8031])).

tff(c_9155,plain,(
    ! [B_837,A_838,C_839] :
      ( k1_xboole_0 = B_837
      | k1_relset_1(A_838,B_837,C_839) = A_838
      | ~ v1_funct_2(C_839,A_838,B_837)
      | ~ m1_subset_1(C_839,k1_zfmisc_1(k2_zfmisc_1(A_838,B_837))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_9168,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_9155])).

tff(c_9182,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_8050,c_9168])).

tff(c_9184,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9182])).

tff(c_36,plain,(
    ! [B_21,A_20] :
      ( k1_relat_1(k7_relat_1(B_21,A_20)) = A_20
      | ~ r1_tarski(A_20,k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_9210,plain,(
    ! [A_20] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_20)) = A_20
      | ~ r1_tarski(A_20,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9184,c_36])).

tff(c_9564,plain,(
    ! [A_862] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_862)) = A_862
      | ~ r1_tarski(A_862,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_9210])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_8768,plain,(
    ! [A_795,B_796,C_797,D_798] :
      ( k2_partfun1(A_795,B_796,C_797,D_798) = k7_relat_1(C_797,D_798)
      | ~ m1_subset_1(C_797,k1_zfmisc_1(k2_zfmisc_1(A_795,B_796)))
      | ~ v1_funct_1(C_797) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_8775,plain,(
    ! [D_798] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_798) = k7_relat_1('#skF_5',D_798)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_8768])).

tff(c_8786,plain,(
    ! [D_798] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_798) = k7_relat_1('#skF_5',D_798) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_8775])).

tff(c_34,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_19,A_18)),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3111,plain,(
    ! [A_336,B_337,C_338,D_339] :
      ( k2_partfun1(A_336,B_337,C_338,D_339) = k7_relat_1(C_338,D_339)
      | ~ m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(A_336,B_337)))
      | ~ v1_funct_1(C_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3118,plain,(
    ! [D_339] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_339) = k7_relat_1('#skF_5',D_339)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_3111])).

tff(c_3127,plain,(
    ! [D_339] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_339) = k7_relat_1('#skF_5',D_339) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3118])).

tff(c_1785,plain,(
    ! [A_237,B_238,C_239,D_240] :
      ( k7_relset_1(A_237,B_238,C_239,D_240) = k9_relat_1(C_239,D_240)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1796,plain,(
    ! [D_240] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_240) = k9_relat_1('#skF_5',D_240) ),
    inference(resolution,[status(thm)],[c_74,c_1785])).

tff(c_70,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1798,plain,(
    r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1796,c_70])).

tff(c_32,plain,(
    ! [B_17,A_16] :
      ( k2_relat_1(k7_relat_1(B_17,A_16)) = k9_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3044,plain,(
    ! [A_330,B_331,C_332,D_333] :
      ( k2_partfun1(A_330,B_331,C_332,D_333) = k7_relat_1(C_332,D_333)
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(A_330,B_331)))
      | ~ v1_funct_1(C_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3051,plain,(
    ! [D_333] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_333) = k7_relat_1('#skF_5',D_333)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_3044])).

tff(c_3060,plain,(
    ! [D_333] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_333) = k7_relat_1('#skF_5',D_333) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3051])).

tff(c_30,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2166,plain,(
    ! [A_282,B_283,C_284,D_285] :
      ( k2_partfun1(A_282,B_283,C_284,D_285) = k7_relat_1(C_284,D_285)
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283)))
      | ~ v1_funct_1(C_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2173,plain,(
    ! [D_285] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_285) = k7_relat_1('#skF_5',D_285)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_2166])).

tff(c_2182,plain,(
    ! [D_285] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_285) = k7_relat_1('#skF_5',D_285) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2173])).

tff(c_2867,plain,(
    ! [A_318,B_319,C_320,D_321] :
      ( m1_subset_1(k2_partfun1(A_318,B_319,C_320,D_321),k1_zfmisc_1(k2_zfmisc_1(A_318,B_319)))
      | ~ m1_subset_1(C_320,k1_zfmisc_1(k2_zfmisc_1(A_318,B_319)))
      | ~ v1_funct_1(C_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2900,plain,(
    ! [D_285] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_285),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2182,c_2867])).

tff(c_2924,plain,(
    ! [D_322] : m1_subset_1(k7_relat_1('#skF_5',D_322),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_2900])).

tff(c_24,plain,(
    ! [B_11,A_9] :
      ( v1_relat_1(B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_9))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2948,plain,(
    ! [D_322] :
      ( v1_relat_1(k7_relat_1('#skF_5',D_322))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2924,c_24])).

tff(c_2969,plain,(
    ! [D_322] : v1_relat_1(k7_relat_1('#skF_5',D_322)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2948])).

tff(c_1862,plain,(
    ! [C_250,A_251,B_252] :
      ( m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252)))
      | ~ r1_tarski(k2_relat_1(C_250),B_252)
      | ~ r1_tarski(k1_relat_1(C_250),A_251)
      | ~ v1_relat_1(C_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_913,plain,(
    ! [A_143,B_144,C_145,D_146] :
      ( v1_funct_1(k2_partfun1(A_143,B_144,C_145,D_146))
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144)))
      | ~ v1_funct_1(C_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_918,plain,(
    ! [D_146] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_146))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_913])).

tff(c_926,plain,(
    ! [D_146] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_146)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_918])).

tff(c_68,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_164,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_929,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_926,c_164])).

tff(c_930,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1002,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_930])).

tff(c_1897,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1862,c_1002])).

tff(c_2085,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1897])).

tff(c_2183,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2182,c_2085])).

tff(c_2975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2969,c_2183])).

tff(c_2976,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1897])).

tff(c_2978,plain,(
    ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2976])).

tff(c_3061,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3060,c_2978])).

tff(c_3088,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3061])).

tff(c_3091,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_1798,c_3088])).

tff(c_3092,plain,(
    ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2976])).

tff(c_3130,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3127,c_3092])).

tff(c_3177,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_3130])).

tff(c_3184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_3177])).

tff(c_3185,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_930])).

tff(c_8797,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8786,c_3185])).

tff(c_3186,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_930])).

tff(c_8048,plain,(
    k1_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) = k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3186,c_8031])).

tff(c_8791,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = k1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8786,c_8786,c_8048])).

tff(c_8796,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8786,c_3186])).

tff(c_9008,plain,(
    ! [B_814,C_815,A_816] :
      ( k1_xboole_0 = B_814
      | v1_funct_2(C_815,A_816,B_814)
      | k1_relset_1(A_816,B_814,C_815) != A_816
      | ~ m1_subset_1(C_815,k1_zfmisc_1(k2_zfmisc_1(A_816,B_814))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_9011,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_8796,c_9008])).

tff(c_9029,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8791,c_9011])).

tff(c_9030,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_8797,c_9029])).

tff(c_9036,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_9030])).

tff(c_9573,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9564,c_9036])).

tff(c_9666,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_9573])).

tff(c_9667,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9182])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_9717,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9667,c_2])).

tff(c_9719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_9717])).

tff(c_9720,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9030])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9764,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9720,c_10])).

tff(c_16,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_9763,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9720,c_9720,c_16])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_7659,plain,(
    r1_tarski(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_3186,c_20])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7936,plain,
    ( k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2') = k2_zfmisc_1('#skF_2','#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_7659,c_4])).

tff(c_8204,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_7936])).

tff(c_8790,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8786,c_8204])).

tff(c_9926,plain,(
    ~ r1_tarski('#skF_3',k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9763,c_8790])).

tff(c_9930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9764,c_9926])).

tff(c_9931,plain,(
    k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2') = k2_zfmisc_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_7936])).

tff(c_9939,plain,(
    ~ v1_funct_2(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9931,c_3185])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10162,plain,(
    ! [A_893,B_894,A_895] :
      ( k1_relset_1(A_893,B_894,A_895) = k1_relat_1(A_895)
      | ~ r1_tarski(A_895,k2_zfmisc_1(A_893,B_894)) ) ),
    inference(resolution,[status(thm)],[c_22,c_8031])).

tff(c_10192,plain,(
    ! [A_893,B_894] : k1_relset_1(A_893,B_894,k2_zfmisc_1(A_893,B_894)) = k1_relat_1(k2_zfmisc_1(A_893,B_894)) ),
    inference(resolution,[status(thm)],[c_8,c_10162])).

tff(c_9938,plain,(
    m1_subset_1(k2_zfmisc_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9931,c_3186])).

tff(c_10932,plain,(
    ! [B_956,C_957,A_958] :
      ( k1_xboole_0 = B_956
      | v1_funct_2(C_957,A_958,B_956)
      | k1_relset_1(A_958,B_956,C_957) != A_958
      | ~ m1_subset_1(C_957,k1_zfmisc_1(k2_zfmisc_1(A_958,B_956))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_10938,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k2_zfmisc_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_9938,c_10932])).

tff(c_10954,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_2','#skF_3')
    | k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10192,c_10938])).

tff(c_10955,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_9939,c_10954])).

tff(c_11174,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_10955])).

tff(c_10347,plain,(
    ! [A_919,B_920,C_921,D_922] :
      ( k2_partfun1(A_919,B_920,C_921,D_922) = k7_relat_1(C_921,D_922)
      | ~ m1_subset_1(C_921,k1_zfmisc_1(k2_zfmisc_1(A_919,B_920)))
      | ~ v1_funct_1(C_921) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_10354,plain,(
    ! [D_922] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_922) = k7_relat_1('#skF_5',D_922)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_10347])).

tff(c_10367,plain,(
    ! [D_923] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_923) = k7_relat_1('#skF_5',D_923) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_10354])).

tff(c_10373,plain,(
    k7_relat_1('#skF_5','#skF_2') = k2_zfmisc_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10367,c_9931])).

tff(c_10738,plain,(
    ! [B_951,A_952,C_953] :
      ( k1_xboole_0 = B_951
      | k1_relset_1(A_952,B_951,C_953) = A_952
      | ~ v1_funct_2(C_953,A_952,B_951)
      | ~ m1_subset_1(C_953,k1_zfmisc_1(k2_zfmisc_1(A_952,B_951))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_10751,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_10738])).

tff(c_10764,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_8050,c_10751])).

tff(c_10766,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_10764])).

tff(c_10792,plain,(
    ! [A_20] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_20)) = A_20
      | ~ r1_tarski(A_20,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10766,c_36])).

tff(c_11407,plain,(
    ! [A_978] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_978)) = A_978
      | ~ r1_tarski(A_978,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_10792])).

tff(c_11496,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10373,c_11407])).

tff(c_11559,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_11496])).

tff(c_11561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11174,c_11559])).

tff(c_11562,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10955])).

tff(c_95,plain,(
    ! [A_53,B_54] : v1_relat_1(k2_zfmisc_1(A_53,B_54)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_97,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_95])).

tff(c_18,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_7473,plain,(
    ! [C_666,A_667,B_668] :
      ( v4_relat_1(C_666,A_667)
      | ~ m1_subset_1(C_666,k1_zfmisc_1(k2_zfmisc_1(A_667,B_668))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_7533,plain,(
    ! [A_677,A_678,B_679] :
      ( v4_relat_1(A_677,A_678)
      | ~ r1_tarski(A_677,k2_zfmisc_1(A_678,B_679)) ) ),
    inference(resolution,[status(thm)],[c_22,c_7473])).

tff(c_7563,plain,(
    ! [A_678,B_679] : v4_relat_1(k2_zfmisc_1(A_678,B_679),A_678) ),
    inference(resolution,[status(thm)],[c_8,c_7533])).

tff(c_7496,plain,(
    ! [B_671,A_672] :
      ( r1_tarski(k1_relat_1(B_671),A_672)
      | ~ v4_relat_1(B_671,A_672)
      | ~ v1_relat_1(B_671) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7576,plain,(
    ! [B_683] :
      ( k1_relat_1(B_683) = k1_xboole_0
      | ~ v4_relat_1(B_683,k1_xboole_0)
      | ~ v1_relat_1(B_683) ) ),
    inference(resolution,[status(thm)],[c_7496,c_12])).

tff(c_7580,plain,(
    ! [B_679] :
      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_679)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,B_679)) ) ),
    inference(resolution,[status(thm)],[c_7563,c_7576])).

tff(c_7591,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_18,c_18,c_7580])).

tff(c_50,plain,(
    ! [A_38] :
      ( v1_funct_2(k1_xboole_0,A_38,k1_xboole_0)
      | k1_xboole_0 = A_38
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_38,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_83,plain,(
    ! [A_38] :
      ( v1_funct_2(k1_xboole_0,A_38,k1_xboole_0)
      | k1_xboole_0 = A_38
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_50])).

tff(c_7668,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_7671,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_7668])).

tff(c_7675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_7671])).

tff(c_7677,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_8055,plain,(
    ! [B_714,C_715] :
      ( k1_relset_1(k1_xboole_0,B_714,C_715) = k1_relat_1(C_715)
      | ~ m1_subset_1(C_715,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_8031])).

tff(c_8057,plain,(
    ! [B_714] : k1_relset_1(k1_xboole_0,B_714,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_7677,c_8055])).

tff(c_8062,plain,(
    ! [B_714] : k1_relset_1(k1_xboole_0,B_714,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7591,c_8057])).

tff(c_54,plain,(
    ! [C_40,B_39] :
      ( v1_funct_2(C_40,k1_xboole_0,B_39)
      | k1_relset_1(k1_xboole_0,B_39,C_40) != k1_xboole_0
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_10066,plain,(
    ! [C_883,B_884] :
      ( v1_funct_2(C_883,k1_xboole_0,B_884)
      | k1_relset_1(k1_xboole_0,B_884,C_883) != k1_xboole_0
      | ~ m1_subset_1(C_883,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_54])).

tff(c_10068,plain,(
    ! [B_884] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_884)
      | k1_relset_1(k1_xboole_0,B_884,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7677,c_10066])).

tff(c_10074,plain,(
    ! [B_884] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_884) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8062,c_10068])).

tff(c_11578,plain,(
    ! [B_884] : v1_funct_2('#skF_3','#skF_3',B_884) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11562,c_11562,c_10074])).

tff(c_11598,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11562,c_11562,c_7591])).

tff(c_11611,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11562,c_11562,c_16])).

tff(c_11563,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_10955])).

tff(c_12095,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11598,c_11611,c_11563])).

tff(c_11731,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11611,c_9939])).

tff(c_12096,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12095,c_11731])).

tff(c_12104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11578,c_12096])).

tff(c_12105,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10764])).

tff(c_12179,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12105,c_2])).

tff(c_12181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_12179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:51:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.46/2.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.46/2.93  
% 8.46/2.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.46/2.93  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.46/2.93  
% 8.46/2.93  %Foreground sorts:
% 8.46/2.93  
% 8.46/2.93  
% 8.46/2.93  %Background operators:
% 8.46/2.93  
% 8.46/2.93  
% 8.46/2.93  %Foreground operators:
% 8.46/2.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.46/2.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.46/2.93  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.46/2.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.46/2.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.46/2.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.46/2.93  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 8.46/2.93  tff('#skF_5', type, '#skF_5': $i).
% 8.46/2.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.46/2.93  tff('#skF_2', type, '#skF_2': $i).
% 8.46/2.93  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.46/2.93  tff('#skF_3', type, '#skF_3': $i).
% 8.46/2.93  tff('#skF_1', type, '#skF_1': $i).
% 8.46/2.93  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.46/2.93  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.46/2.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.46/2.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.46/2.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.46/2.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.46/2.93  tff('#skF_4', type, '#skF_4': $i).
% 8.46/2.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.46/2.93  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.46/2.93  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.46/2.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.46/2.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.46/2.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.46/2.93  
% 8.46/2.95  tff(f_156, negated_conjecture, ~(![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_funct_2)).
% 8.46/2.95  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.46/2.95  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.46/2.95  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.46/2.95  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 8.46/2.95  tff(f_135, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.46/2.95  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 8.46/2.95  tff(f_95, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 8.46/2.95  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 8.46/2.95  tff(f_63, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.46/2.95  tff(f_129, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 8.46/2.95  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.46/2.95  tff(f_103, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 8.46/2.95  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.46/2.95  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.46/2.95  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.46/2.95  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.46/2.95  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.46/2.95  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.46/2.95  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 8.46/2.95  tff(f_38, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 8.46/2.95  tff(c_80, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.46/2.95  tff(c_72, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.46/2.95  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.46/2.95  tff(c_150, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.46/2.95  tff(c_163, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_150])).
% 8.46/2.95  tff(c_76, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.46/2.95  tff(c_8031, plain, (![A_711, B_712, C_713]: (k1_relset_1(A_711, B_712, C_713)=k1_relat_1(C_713) | ~m1_subset_1(C_713, k1_zfmisc_1(k2_zfmisc_1(A_711, B_712))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.46/2.95  tff(c_8050, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_8031])).
% 8.46/2.95  tff(c_9155, plain, (![B_837, A_838, C_839]: (k1_xboole_0=B_837 | k1_relset_1(A_838, B_837, C_839)=A_838 | ~v1_funct_2(C_839, A_838, B_837) | ~m1_subset_1(C_839, k1_zfmisc_1(k2_zfmisc_1(A_838, B_837))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.46/2.95  tff(c_9168, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_9155])).
% 8.46/2.95  tff(c_9182, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_8050, c_9168])).
% 8.46/2.95  tff(c_9184, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_9182])).
% 8.46/2.95  tff(c_36, plain, (![B_21, A_20]: (k1_relat_1(k7_relat_1(B_21, A_20))=A_20 | ~r1_tarski(A_20, k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.46/2.95  tff(c_9210, plain, (![A_20]: (k1_relat_1(k7_relat_1('#skF_5', A_20))=A_20 | ~r1_tarski(A_20, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9184, c_36])).
% 8.46/2.95  tff(c_9564, plain, (![A_862]: (k1_relat_1(k7_relat_1('#skF_5', A_862))=A_862 | ~r1_tarski(A_862, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_9210])).
% 8.46/2.95  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.46/2.95  tff(c_8768, plain, (![A_795, B_796, C_797, D_798]: (k2_partfun1(A_795, B_796, C_797, D_798)=k7_relat_1(C_797, D_798) | ~m1_subset_1(C_797, k1_zfmisc_1(k2_zfmisc_1(A_795, B_796))) | ~v1_funct_1(C_797))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.46/2.95  tff(c_8775, plain, (![D_798]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_798)=k7_relat_1('#skF_5', D_798) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_8768])).
% 8.46/2.95  tff(c_8786, plain, (![D_798]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_798)=k7_relat_1('#skF_5', D_798))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_8775])).
% 8.46/2.95  tff(c_34, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(k7_relat_1(B_19, A_18)), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.46/2.95  tff(c_3111, plain, (![A_336, B_337, C_338, D_339]: (k2_partfun1(A_336, B_337, C_338, D_339)=k7_relat_1(C_338, D_339) | ~m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(A_336, B_337))) | ~v1_funct_1(C_338))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.46/2.95  tff(c_3118, plain, (![D_339]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_339)=k7_relat_1('#skF_5', D_339) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_3111])).
% 8.46/2.95  tff(c_3127, plain, (![D_339]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_339)=k7_relat_1('#skF_5', D_339))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3118])).
% 8.46/2.95  tff(c_1785, plain, (![A_237, B_238, C_239, D_240]: (k7_relset_1(A_237, B_238, C_239, D_240)=k9_relat_1(C_239, D_240) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.46/2.95  tff(c_1796, plain, (![D_240]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_240)=k9_relat_1('#skF_5', D_240))), inference(resolution, [status(thm)], [c_74, c_1785])).
% 8.46/2.95  tff(c_70, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.46/2.95  tff(c_1798, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1796, c_70])).
% 8.46/2.95  tff(c_32, plain, (![B_17, A_16]: (k2_relat_1(k7_relat_1(B_17, A_16))=k9_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.46/2.95  tff(c_3044, plain, (![A_330, B_331, C_332, D_333]: (k2_partfun1(A_330, B_331, C_332, D_333)=k7_relat_1(C_332, D_333) | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))) | ~v1_funct_1(C_332))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.46/2.96  tff(c_3051, plain, (![D_333]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_333)=k7_relat_1('#skF_5', D_333) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_3044])).
% 8.46/2.96  tff(c_3060, plain, (![D_333]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_333)=k7_relat_1('#skF_5', D_333))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3051])).
% 8.46/2.96  tff(c_30, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.46/2.96  tff(c_2166, plain, (![A_282, B_283, C_284, D_285]: (k2_partfun1(A_282, B_283, C_284, D_285)=k7_relat_1(C_284, D_285) | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))) | ~v1_funct_1(C_284))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.46/2.96  tff(c_2173, plain, (![D_285]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_285)=k7_relat_1('#skF_5', D_285) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_2166])).
% 8.46/2.96  tff(c_2182, plain, (![D_285]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_285)=k7_relat_1('#skF_5', D_285))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2173])).
% 8.46/2.96  tff(c_2867, plain, (![A_318, B_319, C_320, D_321]: (m1_subset_1(k2_partfun1(A_318, B_319, C_320, D_321), k1_zfmisc_1(k2_zfmisc_1(A_318, B_319))) | ~m1_subset_1(C_320, k1_zfmisc_1(k2_zfmisc_1(A_318, B_319))) | ~v1_funct_1(C_320))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.46/2.96  tff(c_2900, plain, (![D_285]: (m1_subset_1(k7_relat_1('#skF_5', D_285), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2182, c_2867])).
% 8.46/2.96  tff(c_2924, plain, (![D_322]: (m1_subset_1(k7_relat_1('#skF_5', D_322), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_2900])).
% 8.46/2.96  tff(c_24, plain, (![B_11, A_9]: (v1_relat_1(B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_9)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.46/2.96  tff(c_2948, plain, (![D_322]: (v1_relat_1(k7_relat_1('#skF_5', D_322)) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(resolution, [status(thm)], [c_2924, c_24])).
% 8.46/2.96  tff(c_2969, plain, (![D_322]: (v1_relat_1(k7_relat_1('#skF_5', D_322)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2948])).
% 8.46/2.96  tff(c_1862, plain, (![C_250, A_251, B_252]: (m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))) | ~r1_tarski(k2_relat_1(C_250), B_252) | ~r1_tarski(k1_relat_1(C_250), A_251) | ~v1_relat_1(C_250))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.46/2.96  tff(c_913, plain, (![A_143, B_144, C_145, D_146]: (v1_funct_1(k2_partfun1(A_143, B_144, C_145, D_146)) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))) | ~v1_funct_1(C_145))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.46/2.96  tff(c_918, plain, (![D_146]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_146)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_913])).
% 8.46/2.96  tff(c_926, plain, (![D_146]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_146)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_918])).
% 8.46/2.96  tff(c_68, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.46/2.96  tff(c_164, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_68])).
% 8.46/2.96  tff(c_929, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_926, c_164])).
% 8.46/2.96  tff(c_930, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_68])).
% 8.46/2.96  tff(c_1002, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_930])).
% 8.46/2.96  tff(c_1897, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_1862, c_1002])).
% 8.46/2.96  tff(c_2085, plain, (~v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1897])).
% 8.46/2.96  tff(c_2183, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2182, c_2085])).
% 8.46/2.96  tff(c_2975, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2969, c_2183])).
% 8.46/2.96  tff(c_2976, plain, (~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_1897])).
% 8.46/2.96  tff(c_2978, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_2976])).
% 8.46/2.96  tff(c_3061, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3060, c_2978])).
% 8.46/2.96  tff(c_3088, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_32, c_3061])).
% 8.46/2.96  tff(c_3091, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_1798, c_3088])).
% 8.46/2.96  tff(c_3092, plain, (~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_2976])).
% 8.46/2.96  tff(c_3130, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3127, c_3092])).
% 8.46/2.96  tff(c_3177, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_3130])).
% 8.46/2.96  tff(c_3184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_3177])).
% 8.46/2.96  tff(c_3185, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_930])).
% 8.46/2.96  tff(c_8797, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8786, c_3185])).
% 8.46/2.96  tff(c_3186, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_930])).
% 8.46/2.96  tff(c_8048, plain, (k1_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_3186, c_8031])).
% 8.46/2.96  tff(c_8791, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8786, c_8786, c_8048])).
% 8.46/2.96  tff(c_8796, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_8786, c_3186])).
% 8.46/2.96  tff(c_9008, plain, (![B_814, C_815, A_816]: (k1_xboole_0=B_814 | v1_funct_2(C_815, A_816, B_814) | k1_relset_1(A_816, B_814, C_815)!=A_816 | ~m1_subset_1(C_815, k1_zfmisc_1(k2_zfmisc_1(A_816, B_814))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.46/2.96  tff(c_9011, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(resolution, [status(thm)], [c_8796, c_9008])).
% 8.46/2.96  tff(c_9029, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8791, c_9011])).
% 8.46/2.96  tff(c_9030, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_8797, c_9029])).
% 8.46/2.96  tff(c_9036, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_9030])).
% 8.46/2.96  tff(c_9573, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9564, c_9036])).
% 8.46/2.96  tff(c_9666, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_9573])).
% 8.46/2.96  tff(c_9667, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_9182])).
% 8.46/2.96  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.46/2.96  tff(c_9717, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9667, c_2])).
% 8.46/2.96  tff(c_9719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_9717])).
% 8.46/2.96  tff(c_9720, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_9030])).
% 8.46/2.96  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.46/2.96  tff(c_9764, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_9720, c_10])).
% 8.46/2.96  tff(c_16, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.46/2.96  tff(c_9763, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9720, c_9720, c_16])).
% 8.46/2.96  tff(c_20, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.46/2.96  tff(c_7659, plain, (r1_tarski(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_3186, c_20])).
% 8.46/2.96  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.46/2.96  tff(c_7936, plain, (k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')=k2_zfmisc_1('#skF_2', '#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_7659, c_4])).
% 8.46/2.96  tff(c_8204, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_7936])).
% 8.46/2.96  tff(c_8790, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8786, c_8204])).
% 8.46/2.96  tff(c_9926, plain, (~r1_tarski('#skF_3', k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_9763, c_8790])).
% 8.46/2.96  tff(c_9930, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9764, c_9926])).
% 8.46/2.96  tff(c_9931, plain, (k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')=k2_zfmisc_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_7936])).
% 8.46/2.96  tff(c_9939, plain, (~v1_funct_2(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9931, c_3185])).
% 8.46/2.96  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.46/2.96  tff(c_22, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.46/2.96  tff(c_10162, plain, (![A_893, B_894, A_895]: (k1_relset_1(A_893, B_894, A_895)=k1_relat_1(A_895) | ~r1_tarski(A_895, k2_zfmisc_1(A_893, B_894)))), inference(resolution, [status(thm)], [c_22, c_8031])).
% 8.46/2.96  tff(c_10192, plain, (![A_893, B_894]: (k1_relset_1(A_893, B_894, k2_zfmisc_1(A_893, B_894))=k1_relat_1(k2_zfmisc_1(A_893, B_894)))), inference(resolution, [status(thm)], [c_8, c_10162])).
% 8.46/2.96  tff(c_9938, plain, (m1_subset_1(k2_zfmisc_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_9931, c_3186])).
% 8.46/2.96  tff(c_10932, plain, (![B_956, C_957, A_958]: (k1_xboole_0=B_956 | v1_funct_2(C_957, A_958, B_956) | k1_relset_1(A_958, B_956, C_957)!=A_958 | ~m1_subset_1(C_957, k1_zfmisc_1(k2_zfmisc_1(A_958, B_956))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.46/2.96  tff(c_10938, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k2_zfmisc_1('#skF_2', '#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_9938, c_10932])).
% 8.46/2.96  tff(c_10954, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_2', '#skF_3') | k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10192, c_10938])).
% 8.46/2.96  tff(c_10955, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_9939, c_10954])).
% 8.46/2.96  tff(c_11174, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_10955])).
% 8.46/2.96  tff(c_10347, plain, (![A_919, B_920, C_921, D_922]: (k2_partfun1(A_919, B_920, C_921, D_922)=k7_relat_1(C_921, D_922) | ~m1_subset_1(C_921, k1_zfmisc_1(k2_zfmisc_1(A_919, B_920))) | ~v1_funct_1(C_921))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.46/2.96  tff(c_10354, plain, (![D_922]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_922)=k7_relat_1('#skF_5', D_922) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_10347])).
% 8.46/2.96  tff(c_10367, plain, (![D_923]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_923)=k7_relat_1('#skF_5', D_923))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_10354])).
% 8.46/2.96  tff(c_10373, plain, (k7_relat_1('#skF_5', '#skF_2')=k2_zfmisc_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10367, c_9931])).
% 8.46/2.96  tff(c_10738, plain, (![B_951, A_952, C_953]: (k1_xboole_0=B_951 | k1_relset_1(A_952, B_951, C_953)=A_952 | ~v1_funct_2(C_953, A_952, B_951) | ~m1_subset_1(C_953, k1_zfmisc_1(k2_zfmisc_1(A_952, B_951))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.46/2.96  tff(c_10751, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_10738])).
% 8.46/2.96  tff(c_10764, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_8050, c_10751])).
% 8.46/2.96  tff(c_10766, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_10764])).
% 8.46/2.96  tff(c_10792, plain, (![A_20]: (k1_relat_1(k7_relat_1('#skF_5', A_20))=A_20 | ~r1_tarski(A_20, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_10766, c_36])).
% 8.46/2.96  tff(c_11407, plain, (![A_978]: (k1_relat_1(k7_relat_1('#skF_5', A_978))=A_978 | ~r1_tarski(A_978, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_10792])).
% 8.46/2.96  tff(c_11496, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))='#skF_2' | ~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10373, c_11407])).
% 8.46/2.96  tff(c_11559, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_11496])).
% 8.46/2.96  tff(c_11561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11174, c_11559])).
% 8.46/2.96  tff(c_11562, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_10955])).
% 8.46/2.96  tff(c_95, plain, (![A_53, B_54]: (v1_relat_1(k2_zfmisc_1(A_53, B_54)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.46/2.96  tff(c_97, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_95])).
% 8.46/2.96  tff(c_18, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.46/2.96  tff(c_7473, plain, (![C_666, A_667, B_668]: (v4_relat_1(C_666, A_667) | ~m1_subset_1(C_666, k1_zfmisc_1(k2_zfmisc_1(A_667, B_668))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.46/2.96  tff(c_7533, plain, (![A_677, A_678, B_679]: (v4_relat_1(A_677, A_678) | ~r1_tarski(A_677, k2_zfmisc_1(A_678, B_679)))), inference(resolution, [status(thm)], [c_22, c_7473])).
% 8.46/2.96  tff(c_7563, plain, (![A_678, B_679]: (v4_relat_1(k2_zfmisc_1(A_678, B_679), A_678))), inference(resolution, [status(thm)], [c_8, c_7533])).
% 8.46/2.96  tff(c_7496, plain, (![B_671, A_672]: (r1_tarski(k1_relat_1(B_671), A_672) | ~v4_relat_1(B_671, A_672) | ~v1_relat_1(B_671))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.46/2.96  tff(c_12, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.46/2.96  tff(c_7576, plain, (![B_683]: (k1_relat_1(B_683)=k1_xboole_0 | ~v4_relat_1(B_683, k1_xboole_0) | ~v1_relat_1(B_683))), inference(resolution, [status(thm)], [c_7496, c_12])).
% 8.46/2.96  tff(c_7580, plain, (![B_679]: (k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_679))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, B_679)))), inference(resolution, [status(thm)], [c_7563, c_7576])).
% 8.46/2.96  tff(c_7591, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_97, c_18, c_18, c_7580])).
% 8.46/2.96  tff(c_50, plain, (![A_38]: (v1_funct_2(k1_xboole_0, A_38, k1_xboole_0) | k1_xboole_0=A_38 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_38, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.46/2.96  tff(c_83, plain, (![A_38]: (v1_funct_2(k1_xboole_0, A_38, k1_xboole_0) | k1_xboole_0=A_38 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_50])).
% 8.46/2.96  tff(c_7668, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_83])).
% 8.46/2.96  tff(c_7671, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_7668])).
% 8.46/2.96  tff(c_7675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_7671])).
% 8.46/2.96  tff(c_7677, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_83])).
% 8.46/2.96  tff(c_8055, plain, (![B_714, C_715]: (k1_relset_1(k1_xboole_0, B_714, C_715)=k1_relat_1(C_715) | ~m1_subset_1(C_715, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_8031])).
% 8.46/2.96  tff(c_8057, plain, (![B_714]: (k1_relset_1(k1_xboole_0, B_714, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_7677, c_8055])).
% 8.46/2.96  tff(c_8062, plain, (![B_714]: (k1_relset_1(k1_xboole_0, B_714, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7591, c_8057])).
% 8.46/2.96  tff(c_54, plain, (![C_40, B_39]: (v1_funct_2(C_40, k1_xboole_0, B_39) | k1_relset_1(k1_xboole_0, B_39, C_40)!=k1_xboole_0 | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_39))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.46/2.96  tff(c_10066, plain, (![C_883, B_884]: (v1_funct_2(C_883, k1_xboole_0, B_884) | k1_relset_1(k1_xboole_0, B_884, C_883)!=k1_xboole_0 | ~m1_subset_1(C_883, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_54])).
% 8.46/2.96  tff(c_10068, plain, (![B_884]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_884) | k1_relset_1(k1_xboole_0, B_884, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_7677, c_10066])).
% 8.46/2.96  tff(c_10074, plain, (![B_884]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_884))), inference(demodulation, [status(thm), theory('equality')], [c_8062, c_10068])).
% 8.46/2.96  tff(c_11578, plain, (![B_884]: (v1_funct_2('#skF_3', '#skF_3', B_884))), inference(demodulation, [status(thm), theory('equality')], [c_11562, c_11562, c_10074])).
% 8.46/2.96  tff(c_11598, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11562, c_11562, c_7591])).
% 8.46/2.96  tff(c_11611, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11562, c_11562, c_16])).
% 8.46/2.96  tff(c_11563, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_10955])).
% 8.46/2.96  tff(c_12095, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11598, c_11611, c_11563])).
% 8.46/2.96  tff(c_11731, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11611, c_9939])).
% 8.46/2.96  tff(c_12096, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12095, c_11731])).
% 8.46/2.96  tff(c_12104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11578, c_12096])).
% 8.46/2.96  tff(c_12105, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_10764])).
% 8.46/2.96  tff(c_12179, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12105, c_2])).
% 8.46/2.96  tff(c_12181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_12179])).
% 8.46/2.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.46/2.96  
% 8.46/2.96  Inference rules
% 8.46/2.96  ----------------------
% 8.46/2.96  #Ref     : 0
% 8.46/2.96  #Sup     : 2612
% 8.46/2.96  #Fact    : 0
% 8.46/2.96  #Define  : 0
% 8.46/2.96  #Split   : 56
% 8.46/2.96  #Chain   : 0
% 8.46/2.96  #Close   : 0
% 8.46/2.96  
% 8.46/2.96  Ordering : KBO
% 8.46/2.96  
% 8.46/2.96  Simplification rules
% 8.46/2.96  ----------------------
% 8.46/2.96  #Subsume      : 340
% 8.46/2.96  #Demod        : 2625
% 8.46/2.96  #Tautology    : 1024
% 8.46/2.96  #SimpNegUnit  : 48
% 8.46/2.96  #BackRed      : 458
% 8.46/2.96  
% 8.46/2.96  #Partial instantiations: 0
% 8.46/2.96  #Strategies tried      : 1
% 8.46/2.96  
% 8.46/2.96  Timing (in seconds)
% 8.46/2.96  ----------------------
% 8.46/2.96  Preprocessing        : 0.35
% 8.46/2.96  Parsing              : 0.19
% 8.46/2.96  CNF conversion       : 0.02
% 8.46/2.96  Main loop            : 1.81
% 8.46/2.96  Inferencing          : 0.59
% 8.46/2.96  Reduction            : 0.66
% 8.46/2.96  Demodulation         : 0.47
% 8.46/2.96  BG Simplification    : 0.06
% 8.46/2.96  Subsumption          : 0.34
% 8.46/2.96  Abstraction          : 0.08
% 8.46/2.96  MUC search           : 0.00
% 8.46/2.96  Cooper               : 0.00
% 8.46/2.96  Total                : 2.22
% 8.46/2.96  Index Insertion      : 0.00
% 8.46/2.96  Index Deletion       : 0.00
% 8.46/2.96  Index Matching       : 0.00
% 8.46/2.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
