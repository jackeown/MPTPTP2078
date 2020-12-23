%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:19 EST 2020

% Result     : Theorem 4.69s
% Output     : CNFRefutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 161 expanded)
%              Number of leaves         :   36 (  70 expanded)
%              Depth                    :    8
%              Number of atoms          :  147 ( 441 expanded)
%              Number of equality atoms :   25 (  44 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(A))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(B))
                       => ( r1_tarski(k7_relset_1(A,B,C,D),E)
                        <=> r1_tarski(D,k8_relset_1(A,B,C,E)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_30,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2604,plain,(
    ! [A_281,B_282,C_283,D_284] :
      ( k8_relset_1(A_281,B_282,C_283,D_284) = k10_relat_1(C_283,D_284)
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2611,plain,(
    ! [D_284] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_284) = k10_relat_1('#skF_3',D_284) ),
    inference(resolution,[status(thm)],[c_34,c_2604])).

tff(c_102,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_111,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_102])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_184,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( k8_relset_1(A_91,B_92,C_93,D_94) = k10_relat_1(C_93,D_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_191,plain,(
    ! [D_94] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_94) = k10_relat_1('#skF_3',D_94) ),
    inference(resolution,[status(thm)],[c_34,c_184])).

tff(c_50,plain,
    ( r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5')
    | r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_52,plain,(
    r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_192,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_52])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k9_relat_1(B_14,k10_relat_1(B_14,A_13)),A_13)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_179,plain,(
    ! [C_88,A_89,B_90] :
      ( r1_tarski(k9_relat_1(C_88,A_89),k9_relat_1(C_88,B_90))
      | ~ r1_tarski(A_89,B_90)
      | ~ v1_relat_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_344,plain,(
    ! [C_131,A_132,B_133] :
      ( k2_xboole_0(k9_relat_1(C_131,A_132),k9_relat_1(C_131,B_133)) = k9_relat_1(C_131,B_133)
      | ~ r1_tarski(A_132,B_133)
      | ~ v1_relat_1(C_131) ) ),
    inference(resolution,[status(thm)],[c_179,c_6])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_366,plain,(
    ! [C_134,A_135,C_136,B_137] :
      ( r1_tarski(k9_relat_1(C_134,A_135),C_136)
      | ~ r1_tarski(k9_relat_1(C_134,B_137),C_136)
      | ~ r1_tarski(A_135,B_137)
      | ~ v1_relat_1(C_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_4])).

tff(c_2237,plain,(
    ! [B_230,A_231,A_232] :
      ( r1_tarski(k9_relat_1(B_230,A_231),A_232)
      | ~ r1_tarski(A_231,k10_relat_1(B_230,A_232))
      | ~ v1_funct_1(B_230)
      | ~ v1_relat_1(B_230) ) ),
    inference(resolution,[status(thm)],[c_16,c_366])).

tff(c_241,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( k7_relset_1(A_98,B_99,C_100,D_101) = k9_relat_1(C_100,D_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_248,plain,(
    ! [D_101] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_101) = k9_relat_1('#skF_3',D_101) ),
    inference(resolution,[status(thm)],[c_34,c_241])).

tff(c_44,plain,
    ( ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_101,plain,(
    ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44])).

tff(c_249,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_101])).

tff(c_2275,plain,
    ( ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2237,c_249])).

tff(c_2299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_38,c_192,c_2275])).

tff(c_2300,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2327,plain,(
    ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_2346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2300,c_2327])).

tff(c_2347,plain,(
    ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2612,plain,(
    ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2611,c_2347])).

tff(c_2367,plain,(
    ! [C_239,A_240,B_241] :
      ( v1_relat_1(C_239)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2376,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_2367])).

tff(c_2509,plain,(
    ! [A_272,B_273,C_274,D_275] :
      ( k7_relset_1(A_272,B_273,C_274,D_275) = k9_relat_1(C_274,D_275)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2516,plain,(
    ! [D_275] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_275) = k9_relat_1('#skF_3',D_275) ),
    inference(resolution,[status(thm)],[c_34,c_2509])).

tff(c_2348,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2520,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2516,c_2348])).

tff(c_2633,plain,(
    ! [A_286,C_287,B_288] :
      ( r1_tarski(A_286,k10_relat_1(C_287,B_288))
      | ~ r1_tarski(k9_relat_1(C_287,A_286),B_288)
      | ~ r1_tarski(A_286,k1_relat_1(C_287))
      | ~ v1_funct_1(C_287)
      | ~ v1_relat_1(C_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2639,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2520,c_2633])).

tff(c_2651,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2376,c_38,c_2639])).

tff(c_2652,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_2612,c_2651])).

tff(c_36,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2859,plain,(
    ! [B_325,A_326,C_327] :
      ( k1_xboole_0 = B_325
      | k8_relset_1(A_326,B_325,C_327,B_325) = A_326
      | ~ m1_subset_1(C_327,k1_zfmisc_1(k2_zfmisc_1(A_326,B_325)))
      | ~ v1_funct_2(C_327,A_326,B_325)
      | ~ v1_funct_1(C_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2864,plain,
    ( k1_xboole_0 = '#skF_2'
    | k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_2859])).

tff(c_2868,plain,
    ( k1_xboole_0 = '#skF_2'
    | k10_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_2611,c_2864])).

tff(c_2869,plain,(
    k10_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2868])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k10_relat_1(B_12,A_11),k1_relat_1(B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2892,plain,
    ( r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2869,c_14])).

tff(c_2910,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2376,c_2892])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2302,plain,(
    ! [A_233,B_234] :
      ( r1_tarski(A_233,B_234)
      | ~ m1_subset_1(A_233,k1_zfmisc_1(B_234)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2314,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2302])).

tff(c_2322,plain,(
    k2_xboole_0('#skF_4','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2314,c_6])).

tff(c_2388,plain,(
    ! [A_247,C_248,B_249] :
      ( r1_tarski(A_247,C_248)
      | ~ r1_tarski(k2_xboole_0(A_247,B_249),C_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2391,plain,(
    ! [C_248] :
      ( r1_tarski('#skF_4',C_248)
      | ~ r1_tarski('#skF_1',C_248) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2322,c_2388])).

tff(c_2916,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2910,c_2391])).

tff(c_2924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2652,c_2916])).

tff(c_2925,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2868])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2929,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2925,c_2])).

tff(c_2931,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_2929])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:09:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.69/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.80  
% 4.69/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.80  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.69/1.80  
% 4.69/1.80  %Foreground sorts:
% 4.69/1.80  
% 4.69/1.80  
% 4.69/1.80  %Background operators:
% 4.69/1.80  
% 4.69/1.80  
% 4.69/1.80  %Foreground operators:
% 4.69/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.69/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.69/1.80  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.69/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.69/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.69/1.80  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.69/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.69/1.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.69/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.69/1.80  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.69/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.69/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.69/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.69/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.69/1.80  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.69/1.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.69/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.69/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.69/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.69/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.69/1.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.69/1.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.69/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.69/1.80  
% 4.83/1.82  tff(f_113, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (r1_tarski(k7_relset_1(A, B, C, D), E) <=> r1_tarski(D, k8_relset_1(A, B, C, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_2)).
% 4.83/1.82  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.83/1.82  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.83/1.82  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 4.83/1.82  tff(f_44, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 4.83/1.82  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.83/1.82  tff(f_30, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.83/1.82  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.83/1.82  tff(f_64, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 4.83/1.82  tff(f_88, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 4.83/1.82  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 4.83/1.82  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.83/1.82  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.83/1.82  tff(c_40, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.83/1.82  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.83/1.82  tff(c_2604, plain, (![A_281, B_282, C_283, D_284]: (k8_relset_1(A_281, B_282, C_283, D_284)=k10_relat_1(C_283, D_284) | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.83/1.82  tff(c_2611, plain, (![D_284]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_284)=k10_relat_1('#skF_3', D_284))), inference(resolution, [status(thm)], [c_34, c_2604])).
% 4.83/1.82  tff(c_102, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.83/1.82  tff(c_111, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_102])).
% 4.83/1.82  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.83/1.82  tff(c_184, plain, (![A_91, B_92, C_93, D_94]: (k8_relset_1(A_91, B_92, C_93, D_94)=k10_relat_1(C_93, D_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.83/1.82  tff(c_191, plain, (![D_94]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_94)=k10_relat_1('#skF_3', D_94))), inference(resolution, [status(thm)], [c_34, c_184])).
% 4.83/1.82  tff(c_50, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5') | r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.83/1.82  tff(c_52, plain, (r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_50])).
% 4.83/1.82  tff(c_192, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_52])).
% 4.83/1.82  tff(c_16, plain, (![B_14, A_13]: (r1_tarski(k9_relat_1(B_14, k10_relat_1(B_14, A_13)), A_13) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.83/1.82  tff(c_179, plain, (![C_88, A_89, B_90]: (r1_tarski(k9_relat_1(C_88, A_89), k9_relat_1(C_88, B_90)) | ~r1_tarski(A_89, B_90) | ~v1_relat_1(C_88))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.83/1.82  tff(c_6, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.83/1.82  tff(c_344, plain, (![C_131, A_132, B_133]: (k2_xboole_0(k9_relat_1(C_131, A_132), k9_relat_1(C_131, B_133))=k9_relat_1(C_131, B_133) | ~r1_tarski(A_132, B_133) | ~v1_relat_1(C_131))), inference(resolution, [status(thm)], [c_179, c_6])).
% 4.83/1.82  tff(c_4, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.83/1.82  tff(c_366, plain, (![C_134, A_135, C_136, B_137]: (r1_tarski(k9_relat_1(C_134, A_135), C_136) | ~r1_tarski(k9_relat_1(C_134, B_137), C_136) | ~r1_tarski(A_135, B_137) | ~v1_relat_1(C_134))), inference(superposition, [status(thm), theory('equality')], [c_344, c_4])).
% 4.83/1.82  tff(c_2237, plain, (![B_230, A_231, A_232]: (r1_tarski(k9_relat_1(B_230, A_231), A_232) | ~r1_tarski(A_231, k10_relat_1(B_230, A_232)) | ~v1_funct_1(B_230) | ~v1_relat_1(B_230))), inference(resolution, [status(thm)], [c_16, c_366])).
% 4.83/1.82  tff(c_241, plain, (![A_98, B_99, C_100, D_101]: (k7_relset_1(A_98, B_99, C_100, D_101)=k9_relat_1(C_100, D_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.83/1.82  tff(c_248, plain, (![D_101]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_101)=k9_relat_1('#skF_3', D_101))), inference(resolution, [status(thm)], [c_34, c_241])).
% 4.83/1.82  tff(c_44, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.83/1.82  tff(c_101, plain, (~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44])).
% 4.83/1.82  tff(c_249, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_248, c_101])).
% 4.83/1.82  tff(c_2275, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2237, c_249])).
% 4.83/1.82  tff(c_2299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_38, c_192, c_2275])).
% 4.83/1.82  tff(c_2300, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_50])).
% 4.83/1.82  tff(c_2327, plain, (~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_44])).
% 4.83/1.82  tff(c_2346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2300, c_2327])).
% 4.83/1.82  tff(c_2347, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_44])).
% 4.83/1.82  tff(c_2612, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2611, c_2347])).
% 4.83/1.82  tff(c_2367, plain, (![C_239, A_240, B_241]: (v1_relat_1(C_239) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.83/1.82  tff(c_2376, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_2367])).
% 4.83/1.82  tff(c_2509, plain, (![A_272, B_273, C_274, D_275]: (k7_relset_1(A_272, B_273, C_274, D_275)=k9_relat_1(C_274, D_275) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.83/1.82  tff(c_2516, plain, (![D_275]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_275)=k9_relat_1('#skF_3', D_275))), inference(resolution, [status(thm)], [c_34, c_2509])).
% 4.83/1.82  tff(c_2348, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_44])).
% 4.83/1.82  tff(c_2520, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2516, c_2348])).
% 4.83/1.82  tff(c_2633, plain, (![A_286, C_287, B_288]: (r1_tarski(A_286, k10_relat_1(C_287, B_288)) | ~r1_tarski(k9_relat_1(C_287, A_286), B_288) | ~r1_tarski(A_286, k1_relat_1(C_287)) | ~v1_funct_1(C_287) | ~v1_relat_1(C_287))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.83/1.82  tff(c_2639, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2520, c_2633])).
% 4.83/1.82  tff(c_2651, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2376, c_38, c_2639])).
% 4.83/1.82  tff(c_2652, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_2612, c_2651])).
% 4.83/1.82  tff(c_36, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.83/1.82  tff(c_2859, plain, (![B_325, A_326, C_327]: (k1_xboole_0=B_325 | k8_relset_1(A_326, B_325, C_327, B_325)=A_326 | ~m1_subset_1(C_327, k1_zfmisc_1(k2_zfmisc_1(A_326, B_325))) | ~v1_funct_2(C_327, A_326, B_325) | ~v1_funct_1(C_327))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.83/1.82  tff(c_2864, plain, (k1_xboole_0='#skF_2' | k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_2859])).
% 4.83/1.82  tff(c_2868, plain, (k1_xboole_0='#skF_2' | k10_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_2611, c_2864])).
% 4.83/1.82  tff(c_2869, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_2868])).
% 4.83/1.82  tff(c_14, plain, (![B_12, A_11]: (r1_tarski(k10_relat_1(B_12, A_11), k1_relat_1(B_12)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.83/1.82  tff(c_2892, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2869, c_14])).
% 4.83/1.82  tff(c_2910, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2376, c_2892])).
% 4.83/1.82  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.83/1.82  tff(c_2302, plain, (![A_233, B_234]: (r1_tarski(A_233, B_234) | ~m1_subset_1(A_233, k1_zfmisc_1(B_234)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.83/1.82  tff(c_2314, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_2302])).
% 4.83/1.82  tff(c_2322, plain, (k2_xboole_0('#skF_4', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_2314, c_6])).
% 4.83/1.82  tff(c_2388, plain, (![A_247, C_248, B_249]: (r1_tarski(A_247, C_248) | ~r1_tarski(k2_xboole_0(A_247, B_249), C_248))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.83/1.82  tff(c_2391, plain, (![C_248]: (r1_tarski('#skF_4', C_248) | ~r1_tarski('#skF_1', C_248))), inference(superposition, [status(thm), theory('equality')], [c_2322, c_2388])).
% 4.83/1.82  tff(c_2916, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2910, c_2391])).
% 4.83/1.82  tff(c_2924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2652, c_2916])).
% 4.83/1.82  tff(c_2925, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2868])).
% 4.83/1.82  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.83/1.82  tff(c_2929, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2925, c_2])).
% 4.83/1.82  tff(c_2931, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_2929])).
% 4.83/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.82  
% 4.83/1.82  Inference rules
% 4.83/1.82  ----------------------
% 4.83/1.82  #Ref     : 0
% 4.83/1.82  #Sup     : 669
% 4.83/1.82  #Fact    : 0
% 4.83/1.82  #Define  : 0
% 4.83/1.82  #Split   : 18
% 4.83/1.82  #Chain   : 0
% 4.83/1.82  #Close   : 0
% 4.83/1.82  
% 4.83/1.82  Ordering : KBO
% 4.83/1.82  
% 4.83/1.82  Simplification rules
% 4.83/1.82  ----------------------
% 4.83/1.82  #Subsume      : 142
% 4.83/1.82  #Demod        : 288
% 4.83/1.82  #Tautology    : 247
% 4.83/1.82  #SimpNegUnit  : 3
% 4.83/1.82  #BackRed      : 10
% 4.83/1.82  
% 4.83/1.82  #Partial instantiations: 0
% 4.83/1.82  #Strategies tried      : 1
% 4.83/1.82  
% 4.83/1.82  Timing (in seconds)
% 4.83/1.82  ----------------------
% 4.83/1.82  Preprocessing        : 0.33
% 4.83/1.82  Parsing              : 0.17
% 4.83/1.82  CNF conversion       : 0.03
% 4.83/1.82  Main loop            : 0.73
% 4.83/1.82  Inferencing          : 0.25
% 4.83/1.82  Reduction            : 0.23
% 4.83/1.82  Demodulation         : 0.16
% 4.83/1.82  BG Simplification    : 0.03
% 4.83/1.82  Subsumption          : 0.16
% 4.83/1.82  Abstraction          : 0.04
% 4.83/1.82  MUC search           : 0.00
% 4.83/1.82  Cooper               : 0.00
% 4.83/1.82  Total                : 1.10
% 4.83/1.82  Index Insertion      : 0.00
% 4.83/1.82  Index Deletion       : 0.00
% 4.83/1.82  Index Matching       : 0.00
% 4.83/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
