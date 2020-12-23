%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1055+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 192 expanded)
%              Number of leaves         :   34 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :  150 ( 587 expanded)
%              Number of equality atoms :   22 (  61 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
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

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(C,A)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | r1_tarski(C,k8_relset_1(A,B,D,k7_relset_1(A,B,D,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_2)).

tff(f_29,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_30,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_650,plain,(
    ! [A_162,B_163,C_164,D_165] :
      ( k8_relset_1(A_162,B_163,C_164,D_165) = k10_relat_1(C_164,D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_657,plain,(
    ! [D_165] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_165) = k10_relat_1('#skF_3',D_165) ),
    inference(resolution,[status(thm)],[c_32,c_650])).

tff(c_73,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_82,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_73])).

tff(c_230,plain,(
    ! [A_87,B_88,C_89,D_90] :
      ( k8_relset_1(A_87,B_88,C_89,D_90) = k10_relat_1(C_89,D_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_237,plain,(
    ! [D_90] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_90) = k10_relat_1('#skF_3',D_90) ),
    inference(resolution,[status(thm)],[c_32,c_230])).

tff(c_48,plain,
    ( r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5')
    | r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_54,plain,(
    r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_240,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_54])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_14,plain,(
    ! [C_16,A_14,B_15] :
      ( r1_tarski(k9_relat_1(C_16,A_14),k9_relat_1(C_16,B_15))
      | ~ r1_tarski(A_14,B_15)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_118,plain,(
    ! [B_72,A_73] :
      ( r1_tarski(k9_relat_1(B_72,k10_relat_1(B_72,A_73)),A_73)
      | ~ v1_funct_1(B_72)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    ! [A_20,C_22,B_21] :
      ( r1_tarski(A_20,C_22)
      | ~ r1_tarski(B_21,C_22)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_360,plain,(
    ! [A_115,A_116,B_117] :
      ( r1_tarski(A_115,A_116)
      | ~ r1_tarski(A_115,k9_relat_1(B_117,k10_relat_1(B_117,A_116)))
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(resolution,[status(thm)],[c_118,c_18])).

tff(c_371,plain,(
    ! [C_118,A_119,A_120] :
      ( r1_tarski(k9_relat_1(C_118,A_119),A_120)
      | ~ v1_funct_1(C_118)
      | ~ r1_tarski(A_119,k10_relat_1(C_118,A_120))
      | ~ v1_relat_1(C_118) ) ),
    inference(resolution,[status(thm)],[c_14,c_360])).

tff(c_319,plain,(
    ! [A_102,B_103,C_104,D_105] :
      ( k7_relset_1(A_102,B_103,C_104,D_105) = k9_relat_1(C_104,D_105)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_326,plain,(
    ! [D_105] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_105) = k9_relat_1('#skF_3',D_105) ),
    inference(resolution,[status(thm)],[c_32,c_319])).

tff(c_42,plain,
    ( ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_90,plain,(
    ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_42])).

tff(c_327,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_90])).

tff(c_387,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_371,c_327])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_240,c_36,c_387])).

tff(c_420,plain,(
    ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_681,plain,(
    ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_420])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_422,plain,(
    ! [A_123,B_124] :
      ( r1_tarski(A_123,B_124)
      | ~ m1_subset_1(A_123,k1_zfmisc_1(B_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_438,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_422])).

tff(c_616,plain,(
    ! [A_157,B_158,C_159,D_160] :
      ( k7_relset_1(A_157,B_158,C_159,D_160) = k9_relat_1(C_159,D_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_623,plain,(
    ! [D_160] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_160) = k9_relat_1('#skF_3',D_160) ),
    inference(resolution,[status(thm)],[c_32,c_616])).

tff(c_419,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_627,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_419])).

tff(c_445,plain,(
    ! [C_125,A_126,B_127] :
      ( v1_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_454,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_445])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_34,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_818,plain,(
    ! [B_193,C_194,A_195,D_196] :
      ( k1_xboole_0 = B_193
      | r1_tarski(C_194,k8_relset_1(A_195,B_193,D_196,k7_relset_1(A_195,B_193,D_196,C_194)))
      | ~ r1_tarski(C_194,A_195)
      | ~ m1_subset_1(D_196,k1_zfmisc_1(k2_zfmisc_1(A_195,B_193)))
      | ~ v1_funct_2(D_196,A_195,B_193)
      | ~ v1_funct_1(D_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_828,plain,(
    ! [C_194] :
      ( k1_xboole_0 = '#skF_2'
      | r1_tarski(C_194,k10_relat_1('#skF_3',k7_relset_1('#skF_1','#skF_2','#skF_3',C_194)))
      | ~ r1_tarski(C_194,'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_818])).

tff(c_836,plain,(
    ! [C_194] :
      ( k1_xboole_0 = '#skF_2'
      | r1_tarski(C_194,k10_relat_1('#skF_3',k9_relat_1('#skF_3',C_194)))
      | ~ r1_tarski(C_194,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_623,c_828])).

tff(c_844,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_836])).

tff(c_4,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_847,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_844,c_49])).

tff(c_850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_847])).

tff(c_852,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_836])).

tff(c_831,plain,(
    ! [D_160] :
      ( k1_xboole_0 = '#skF_2'
      | r1_tarski(D_160,k8_relset_1('#skF_1','#skF_2','#skF_3',k9_relat_1('#skF_3',D_160)))
      | ~ r1_tarski(D_160,'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_818])).

tff(c_838,plain,(
    ! [D_160] :
      ( k1_xboole_0 = '#skF_2'
      | r1_tarski(D_160,k10_relat_1('#skF_3',k9_relat_1('#skF_3',D_160)))
      | ~ r1_tarski(D_160,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_657,c_831])).

tff(c_853,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_838])).

tff(c_854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_852,c_853])).

tff(c_855,plain,(
    ! [D_160] :
      ( r1_tarski(D_160,k10_relat_1('#skF_3',k9_relat_1('#skF_3',D_160)))
      | ~ r1_tarski(D_160,'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_838])).

tff(c_604,plain,(
    ! [C_151,A_152,B_153] :
      ( r1_tarski(k10_relat_1(C_151,A_152),k10_relat_1(C_151,B_153))
      | ~ r1_tarski(A_152,B_153)
      | ~ v1_relat_1(C_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1037,plain,(
    ! [A_223,C_224,B_225,A_226] :
      ( r1_tarski(A_223,k10_relat_1(C_224,B_225))
      | ~ r1_tarski(A_223,k10_relat_1(C_224,A_226))
      | ~ r1_tarski(A_226,B_225)
      | ~ v1_relat_1(C_224) ) ),
    inference(resolution,[status(thm)],[c_604,c_18])).

tff(c_1044,plain,(
    ! [D_160,B_225] :
      ( r1_tarski(D_160,k10_relat_1('#skF_3',B_225))
      | ~ r1_tarski(k9_relat_1('#skF_3',D_160),B_225)
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(D_160,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_855,c_1037])).

tff(c_1060,plain,(
    ! [D_230,B_231] :
      ( r1_tarski(D_230,k10_relat_1('#skF_3',B_231))
      | ~ r1_tarski(k9_relat_1('#skF_3',D_230),B_231)
      | ~ r1_tarski(D_230,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_1044])).

tff(c_1108,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_627,c_1060])).

tff(c_1155,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_1108])).

tff(c_1157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_681,c_1155])).

%------------------------------------------------------------------------------
