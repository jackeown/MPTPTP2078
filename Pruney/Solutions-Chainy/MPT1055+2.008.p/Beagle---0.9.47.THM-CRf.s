%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:19 EST 2020

% Result     : Theorem 6.73s
% Output     : CNFRefutation 6.73s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 168 expanded)
%              Number of leaves         :   39 (  73 expanded)
%              Depth                    :    9
%              Number of atoms          :  153 ( 445 expanded)
%              Number of equality atoms :   21 (  38 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_36,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_58,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(A_67,B_68)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_75,plain,(
    r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_58])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_88,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_101,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_88])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_40,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_5044,plain,(
    ! [A_292,B_293,C_294,D_295] :
      ( k8_relset_1(A_292,B_293,C_294,D_295) = k10_relat_1(C_294,D_295)
      | ~ m1_subset_1(C_294,k1_zfmisc_1(k2_zfmisc_1(A_292,B_293))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5054,plain,(
    ! [D_295] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_295) = k10_relat_1('#skF_4',D_295) ),
    inference(resolution,[status(thm)],[c_38,c_5044])).

tff(c_5486,plain,(
    ! [B_321,A_322,C_323] :
      ( k1_xboole_0 = B_321
      | k8_relset_1(A_322,B_321,C_323,B_321) = A_322
      | ~ m1_subset_1(C_323,k1_zfmisc_1(k2_zfmisc_1(A_322,B_321)))
      | ~ v1_funct_2(C_323,A_322,B_321)
      | ~ v1_funct_1(C_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5491,plain,
    ( k1_xboole_0 = '#skF_3'
    | k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_5486])).

tff(c_5498,plain,
    ( k1_xboole_0 = '#skF_3'
    | k10_relat_1('#skF_4','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_5054,c_5491])).

tff(c_5500,plain,(
    k10_relat_1('#skF_4','#skF_3') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5498])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k10_relat_1(B_15,A_14),k1_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_5507,plain,
    ( r1_tarski('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5500,c_16])).

tff(c_5513,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_5507])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5546,plain,(
    ! [A_324] :
      ( r1_tarski(A_324,k1_relat_1('#skF_4'))
      | ~ r1_tarski(A_324,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_5513,c_2])).

tff(c_402,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k8_relset_1(A_105,B_106,C_107,D_108) = k10_relat_1(C_107,D_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_412,plain,(
    ! [D_108] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_108) = k10_relat_1('#skF_4',D_108) ),
    inference(resolution,[status(thm)],[c_38,c_402])).

tff(c_54,plain,
    ( r1_tarski(k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_103,plain,(
    r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_457,plain,(
    r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_103])).

tff(c_14,plain,(
    ! [C_13,A_11,B_12] :
      ( r1_tarski(k9_relat_1(C_13,A_11),k9_relat_1(C_13,B_12))
      | ~ r1_tarski(A_11,B_12)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_253,plain,(
    ! [B_94,A_95] :
      ( r1_tarski(k9_relat_1(B_94,k10_relat_1(B_94,A_95)),A_95)
      | ~ v1_funct_1(B_94)
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1435,plain,(
    ! [A_174,A_175,B_176] :
      ( r1_tarski(A_174,A_175)
      | ~ r1_tarski(A_174,k9_relat_1(B_176,k10_relat_1(B_176,A_175)))
      | ~ v1_funct_1(B_176)
      | ~ v1_relat_1(B_176) ) ),
    inference(resolution,[status(thm)],[c_253,c_2])).

tff(c_4458,plain,(
    ! [C_261,A_262,A_263] :
      ( r1_tarski(k9_relat_1(C_261,A_262),A_263)
      | ~ v1_funct_1(C_261)
      | ~ r1_tarski(A_262,k10_relat_1(C_261,A_263))
      | ~ v1_relat_1(C_261) ) ),
    inference(resolution,[status(thm)],[c_14,c_1435])).

tff(c_489,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k7_relset_1(A_112,B_113,C_114,D_115) = k9_relat_1(C_114,D_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_499,plain,(
    ! [D_115] : k7_relset_1('#skF_2','#skF_3','#skF_4',D_115) = k9_relat_1('#skF_4',D_115) ),
    inference(resolution,[status(thm)],[c_38,c_489])).

tff(c_48,plain,
    ( ~ r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6'))
    | ~ r1_tarski(k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_169,plain,(
    ~ r1_tarski(k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_48])).

tff(c_501,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_169])).

tff(c_4590,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4458,c_501])).

tff(c_4659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_457,c_42,c_4590])).

tff(c_4661,plain,(
    ~ r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_5063,plain,(
    ~ r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5054,c_4661])).

tff(c_5174,plain,(
    ! [A_303,B_304,C_305,D_306] :
      ( k7_relset_1(A_303,B_304,C_305,D_306) = k9_relat_1(C_305,D_306)
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(A_303,B_304))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_5184,plain,(
    ! [D_306] : k7_relset_1('#skF_2','#skF_3','#skF_4',D_306) = k9_relat_1('#skF_4',D_306) ),
    inference(resolution,[status(thm)],[c_38,c_5174])).

tff(c_4660,plain,(
    r1_tarski(k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_5189,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5184,c_4660])).

tff(c_5277,plain,(
    ! [A_309,C_310,B_311] :
      ( r1_tarski(A_309,k10_relat_1(C_310,B_311))
      | ~ r1_tarski(k9_relat_1(C_310,A_309),B_311)
      | ~ r1_tarski(A_309,k1_relat_1(C_310))
      | ~ v1_funct_1(C_310)
      | ~ v1_relat_1(C_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5283,plain,
    ( r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5189,c_5277])).

tff(c_5299,plain,
    ( r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_42,c_5283])).

tff(c_5300,plain,(
    ~ r1_tarski('#skF_5',k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_5063,c_5299])).

tff(c_5549,plain,(
    ~ r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_5546,c_5300])).

tff(c_5562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_5549])).

tff(c_5563,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5498])).

tff(c_6,plain,(
    ! [A_5] : m1_subset_1('#skF_1'(A_5),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    ! [A_74,B_75] :
      ( r2_hidden(A_74,B_75)
      | v1_xboole_0(B_75)
      | ~ m1_subset_1(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4680,plain,(
    ! [B_269,A_270] :
      ( ~ r1_tarski(B_269,A_270)
      | v1_xboole_0(B_269)
      | ~ m1_subset_1(A_270,B_269) ) ),
    inference(resolution,[status(thm)],[c_83,c_22])).

tff(c_4708,plain,(
    ! [A_4] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_4680])).

tff(c_4733,plain,(
    ! [A_274] : ~ m1_subset_1(A_274,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_4708])).

tff(c_4738,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_4733])).

tff(c_4739,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4708])).

tff(c_5576,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5563,c_4739])).

tff(c_5580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_5576])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:53:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.73/2.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.73/2.42  
% 6.73/2.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.73/2.42  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 6.73/2.42  
% 6.73/2.42  %Foreground sorts:
% 6.73/2.42  
% 6.73/2.42  
% 6.73/2.42  %Background operators:
% 6.73/2.42  
% 6.73/2.42  
% 6.73/2.42  %Foreground operators:
% 6.73/2.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.73/2.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.73/2.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.73/2.42  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 6.73/2.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.73/2.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.73/2.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.73/2.42  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.73/2.42  tff('#skF_5', type, '#skF_5': $i).
% 6.73/2.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.73/2.42  tff('#skF_6', type, '#skF_6': $i).
% 6.73/2.42  tff('#skF_2', type, '#skF_2': $i).
% 6.73/2.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.73/2.42  tff('#skF_3', type, '#skF_3': $i).
% 6.73/2.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.73/2.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.73/2.42  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.73/2.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.73/2.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.73/2.42  tff('#skF_4', type, '#skF_4': $i).
% 6.73/2.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.73/2.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.73/2.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.73/2.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.73/2.42  
% 6.73/2.44  tff(f_126, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (r1_tarski(k7_relset_1(A, B, C, D), E) <=> r1_tarski(D, k8_relset_1(A, B, C, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_2)).
% 6.73/2.44  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.73/2.44  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.73/2.44  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 6.73/2.44  tff(f_101, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 6.73/2.44  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 6.73/2.44  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.73/2.44  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 6.73/2.44  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 6.73/2.44  tff(f_85, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.73/2.44  tff(f_72, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 6.73/2.44  tff(f_36, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 6.73/2.44  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.73/2.44  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 6.73/2.44  tff(f_77, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.73/2.44  tff(c_44, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.73/2.44  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.73/2.44  tff(c_58, plain, (![A_67, B_68]: (r1_tarski(A_67, B_68) | ~m1_subset_1(A_67, k1_zfmisc_1(B_68)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.73/2.44  tff(c_75, plain, (r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_58])).
% 6.73/2.44  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.73/2.44  tff(c_88, plain, (![C_76, A_77, B_78]: (v1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.73/2.44  tff(c_101, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_88])).
% 6.73/2.44  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.73/2.44  tff(c_40, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.73/2.44  tff(c_5044, plain, (![A_292, B_293, C_294, D_295]: (k8_relset_1(A_292, B_293, C_294, D_295)=k10_relat_1(C_294, D_295) | ~m1_subset_1(C_294, k1_zfmisc_1(k2_zfmisc_1(A_292, B_293))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.73/2.44  tff(c_5054, plain, (![D_295]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_295)=k10_relat_1('#skF_4', D_295))), inference(resolution, [status(thm)], [c_38, c_5044])).
% 6.73/2.44  tff(c_5486, plain, (![B_321, A_322, C_323]: (k1_xboole_0=B_321 | k8_relset_1(A_322, B_321, C_323, B_321)=A_322 | ~m1_subset_1(C_323, k1_zfmisc_1(k2_zfmisc_1(A_322, B_321))) | ~v1_funct_2(C_323, A_322, B_321) | ~v1_funct_1(C_323))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.73/2.44  tff(c_5491, plain, (k1_xboole_0='#skF_3' | k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_5486])).
% 6.73/2.44  tff(c_5498, plain, (k1_xboole_0='#skF_3' | k10_relat_1('#skF_4', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_5054, c_5491])).
% 6.73/2.44  tff(c_5500, plain, (k10_relat_1('#skF_4', '#skF_3')='#skF_2'), inference(splitLeft, [status(thm)], [c_5498])).
% 6.73/2.44  tff(c_16, plain, (![B_15, A_14]: (r1_tarski(k10_relat_1(B_15, A_14), k1_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.73/2.44  tff(c_5507, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5500, c_16])).
% 6.73/2.44  tff(c_5513, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_5507])).
% 6.73/2.44  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.73/2.44  tff(c_5546, plain, (![A_324]: (r1_tarski(A_324, k1_relat_1('#skF_4')) | ~r1_tarski(A_324, '#skF_2'))), inference(resolution, [status(thm)], [c_5513, c_2])).
% 6.73/2.44  tff(c_402, plain, (![A_105, B_106, C_107, D_108]: (k8_relset_1(A_105, B_106, C_107, D_108)=k10_relat_1(C_107, D_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.73/2.44  tff(c_412, plain, (![D_108]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_108)=k10_relat_1('#skF_4', D_108))), inference(resolution, [status(thm)], [c_38, c_402])).
% 6.73/2.44  tff(c_54, plain, (r1_tarski(k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.73/2.44  tff(c_103, plain, (r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_54])).
% 6.73/2.44  tff(c_457, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_412, c_103])).
% 6.73/2.44  tff(c_14, plain, (![C_13, A_11, B_12]: (r1_tarski(k9_relat_1(C_13, A_11), k9_relat_1(C_13, B_12)) | ~r1_tarski(A_11, B_12) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.73/2.44  tff(c_253, plain, (![B_94, A_95]: (r1_tarski(k9_relat_1(B_94, k10_relat_1(B_94, A_95)), A_95) | ~v1_funct_1(B_94) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.73/2.44  tff(c_1435, plain, (![A_174, A_175, B_176]: (r1_tarski(A_174, A_175) | ~r1_tarski(A_174, k9_relat_1(B_176, k10_relat_1(B_176, A_175))) | ~v1_funct_1(B_176) | ~v1_relat_1(B_176))), inference(resolution, [status(thm)], [c_253, c_2])).
% 6.73/2.44  tff(c_4458, plain, (![C_261, A_262, A_263]: (r1_tarski(k9_relat_1(C_261, A_262), A_263) | ~v1_funct_1(C_261) | ~r1_tarski(A_262, k10_relat_1(C_261, A_263)) | ~v1_relat_1(C_261))), inference(resolution, [status(thm)], [c_14, c_1435])).
% 6.73/2.44  tff(c_489, plain, (![A_112, B_113, C_114, D_115]: (k7_relset_1(A_112, B_113, C_114, D_115)=k9_relat_1(C_114, D_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.73/2.44  tff(c_499, plain, (![D_115]: (k7_relset_1('#skF_2', '#skF_3', '#skF_4', D_115)=k9_relat_1('#skF_4', D_115))), inference(resolution, [status(thm)], [c_38, c_489])).
% 6.73/2.44  tff(c_48, plain, (~r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')) | ~r1_tarski(k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.73/2.44  tff(c_169, plain, (~r1_tarski(k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_48])).
% 6.73/2.44  tff(c_501, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_499, c_169])).
% 6.73/2.44  tff(c_4590, plain, (~v1_funct_1('#skF_4') | ~r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4458, c_501])).
% 6.73/2.44  tff(c_4659, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_457, c_42, c_4590])).
% 6.73/2.44  tff(c_4661, plain, (~r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_54])).
% 6.73/2.44  tff(c_5063, plain, (~r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5054, c_4661])).
% 6.73/2.44  tff(c_5174, plain, (![A_303, B_304, C_305, D_306]: (k7_relset_1(A_303, B_304, C_305, D_306)=k9_relat_1(C_305, D_306) | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(A_303, B_304))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.73/2.44  tff(c_5184, plain, (![D_306]: (k7_relset_1('#skF_2', '#skF_3', '#skF_4', D_306)=k9_relat_1('#skF_4', D_306))), inference(resolution, [status(thm)], [c_38, c_5174])).
% 6.73/2.44  tff(c_4660, plain, (r1_tarski(k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_54])).
% 6.73/2.44  tff(c_5189, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5184, c_4660])).
% 6.73/2.44  tff(c_5277, plain, (![A_309, C_310, B_311]: (r1_tarski(A_309, k10_relat_1(C_310, B_311)) | ~r1_tarski(k9_relat_1(C_310, A_309), B_311) | ~r1_tarski(A_309, k1_relat_1(C_310)) | ~v1_funct_1(C_310) | ~v1_relat_1(C_310))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.73/2.44  tff(c_5283, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_5189, c_5277])).
% 6.73/2.44  tff(c_5299, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_42, c_5283])).
% 6.73/2.44  tff(c_5300, plain, (~r1_tarski('#skF_5', k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_5063, c_5299])).
% 6.73/2.44  tff(c_5549, plain, (~r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_5546, c_5300])).
% 6.73/2.44  tff(c_5562, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_5549])).
% 6.73/2.44  tff(c_5563, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_5498])).
% 6.73/2.44  tff(c_6, plain, (![A_5]: (m1_subset_1('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.73/2.44  tff(c_4, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.73/2.44  tff(c_83, plain, (![A_74, B_75]: (r2_hidden(A_74, B_75) | v1_xboole_0(B_75) | ~m1_subset_1(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.73/2.44  tff(c_22, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.73/2.44  tff(c_4680, plain, (![B_269, A_270]: (~r1_tarski(B_269, A_270) | v1_xboole_0(B_269) | ~m1_subset_1(A_270, B_269))), inference(resolution, [status(thm)], [c_83, c_22])).
% 6.73/2.44  tff(c_4708, plain, (![A_4]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_4680])).
% 6.73/2.44  tff(c_4733, plain, (![A_274]: (~m1_subset_1(A_274, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_4708])).
% 6.73/2.44  tff(c_4738, plain, $false, inference(resolution, [status(thm)], [c_6, c_4733])).
% 6.73/2.44  tff(c_4739, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_4708])).
% 6.73/2.44  tff(c_5576, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5563, c_4739])).
% 6.73/2.44  tff(c_5580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_5576])).
% 6.73/2.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.73/2.44  
% 6.73/2.44  Inference rules
% 6.73/2.44  ----------------------
% 6.73/2.44  #Ref     : 0
% 6.73/2.44  #Sup     : 1227
% 6.73/2.44  #Fact    : 0
% 6.73/2.44  #Define  : 0
% 6.73/2.44  #Split   : 34
% 6.73/2.44  #Chain   : 0
% 6.73/2.44  #Close   : 0
% 6.73/2.44  
% 6.73/2.44  Ordering : KBO
% 6.73/2.44  
% 6.73/2.44  Simplification rules
% 6.73/2.44  ----------------------
% 6.73/2.44  #Subsume      : 202
% 6.73/2.44  #Demod        : 428
% 6.73/2.44  #Tautology    : 315
% 6.73/2.44  #SimpNegUnit  : 7
% 6.73/2.44  #BackRed      : 22
% 6.73/2.44  
% 6.73/2.44  #Partial instantiations: 0
% 6.73/2.44  #Strategies tried      : 1
% 6.73/2.44  
% 6.73/2.44  Timing (in seconds)
% 6.73/2.44  ----------------------
% 6.73/2.44  Preprocessing        : 0.42
% 6.73/2.44  Parsing              : 0.24
% 6.73/2.44  CNF conversion       : 0.03
% 6.73/2.44  Main loop            : 1.19
% 6.73/2.44  Inferencing          : 0.37
% 6.73/2.44  Reduction            : 0.42
% 6.73/2.44  Demodulation         : 0.29
% 6.73/2.44  BG Simplification    : 0.04
% 6.73/2.44  Subsumption          : 0.26
% 6.73/2.44  Abstraction          : 0.05
% 6.73/2.44  MUC search           : 0.00
% 6.73/2.44  Cooper               : 0.00
% 6.73/2.44  Total                : 1.65
% 6.73/2.44  Index Insertion      : 0.00
% 6.73/2.44  Index Deletion       : 0.00
% 6.73/2.44  Index Matching       : 0.00
% 6.73/2.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
