%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1055+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:20 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 152 expanded)
%              Number of leaves         :   34 (  67 expanded)
%              Depth                    :   10
%              Number of atoms          :  138 ( 425 expanded)
%              Number of equality atoms :   19 (  38 expanded)
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

tff(f_109,negated_conjecture,(
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

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,axiom,(
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
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_706,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( k8_relset_1(A_158,B_159,C_160,D_161) = k10_relat_1(C_160,D_161)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_713,plain,(
    ! [D_161] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_161) = k10_relat_1('#skF_3',D_161) ),
    inference(resolution,[status(thm)],[c_32,c_706])).

tff(c_82,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_91,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_82])).

tff(c_311,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k8_relset_1(A_105,B_106,C_107,D_108) = k10_relat_1(C_107,D_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_318,plain,(
    ! [D_108] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_108) = k10_relat_1('#skF_3',D_108) ),
    inference(resolution,[status(thm)],[c_32,c_311])).

tff(c_42,plain,
    ( ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_98,plain,(
    ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,
    ( r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5')
    | r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_163,plain,(
    r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_48])).

tff(c_335,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_163])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_12,plain,(
    ! [C_16,A_14,B_15] :
      ( r1_tarski(k9_relat_1(C_16,A_14),k9_relat_1(C_16,B_15))
      | ~ r1_tarski(A_14,B_15)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_122,plain,(
    ! [B_73,A_74] :
      ( r1_tarski(k9_relat_1(B_73,k10_relat_1(B_73,A_74)),A_74)
      | ~ v1_funct_1(B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_20,C_22,B_21] :
      ( r1_tarski(A_20,C_22)
      | ~ r1_tarski(B_21,C_22)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_472,plain,(
    ! [A_127,A_128,B_129] :
      ( r1_tarski(A_127,A_128)
      | ~ r1_tarski(A_127,k9_relat_1(B_129,k10_relat_1(B_129,A_128)))
      | ~ v1_funct_1(B_129)
      | ~ v1_relat_1(B_129) ) ),
    inference(resolution,[status(thm)],[c_122,c_16])).

tff(c_496,plain,(
    ! [C_132,A_133,A_134] :
      ( r1_tarski(k9_relat_1(C_132,A_133),A_134)
      | ~ v1_funct_1(C_132)
      | ~ r1_tarski(A_133,k10_relat_1(C_132,A_134))
      | ~ v1_relat_1(C_132) ) ),
    inference(resolution,[status(thm)],[c_12,c_472])).

tff(c_238,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( k7_relset_1(A_89,B_90,C_91,D_92) = k9_relat_1(C_91,D_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_245,plain,(
    ! [D_92] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_92) = k9_relat_1('#skF_3',D_92) ),
    inference(resolution,[status(thm)],[c_32,c_238])).

tff(c_246,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_98])).

tff(c_517,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_496,c_246])).

tff(c_545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_335,c_36,c_517])).

tff(c_546,plain,(
    ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_714,plain,(
    ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_546])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_64,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_76,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_64])).

tff(c_743,plain,(
    ! [A_172,B_173,C_174,D_175] :
      ( k7_relset_1(A_172,B_173,C_174,D_175) = k9_relat_1(C_174,D_175)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_750,plain,(
    ! [D_175] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_175) = k9_relat_1('#skF_3',D_175) ),
    inference(resolution,[status(thm)],[c_32,c_743])).

tff(c_547,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_764,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_750,c_547])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_34,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_847,plain,(
    ! [B_184,C_185,A_186,D_187] :
      ( k1_xboole_0 = B_184
      | r1_tarski(C_185,k8_relset_1(A_186,B_184,D_187,k7_relset_1(A_186,B_184,D_187,C_185)))
      | ~ r1_tarski(C_185,A_186)
      | ~ m1_subset_1(D_187,k1_zfmisc_1(k2_zfmisc_1(A_186,B_184)))
      | ~ v1_funct_2(D_187,A_186,B_184)
      | ~ v1_funct_1(D_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_856,plain,(
    ! [D_175] :
      ( k1_xboole_0 = '#skF_2'
      | r1_tarski(D_175,k8_relset_1('#skF_1','#skF_2','#skF_3',k9_relat_1('#skF_3',D_175)))
      | ~ r1_tarski(D_175,'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_847])).

tff(c_865,plain,(
    ! [D_175] :
      ( k1_xboole_0 = '#skF_2'
      | r1_tarski(D_175,k10_relat_1('#skF_3',k9_relat_1('#skF_3',D_175)))
      | ~ r1_tarski(D_175,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_713,c_856])).

tff(c_894,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_865])).

tff(c_4,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_49,plain,(
    ! [A_56] :
      ( k1_xboole_0 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_53,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_49])).

tff(c_54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_4])).

tff(c_897,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_894,c_54])).

tff(c_901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_897])).

tff(c_902,plain,(
    ! [D_175] :
      ( r1_tarski(D_175,k10_relat_1('#skF_3',k9_relat_1('#skF_3',D_175)))
      | ~ r1_tarski(D_175,'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_865])).

tff(c_696,plain,(
    ! [C_155,A_156,B_157] :
      ( r1_tarski(k10_relat_1(C_155,A_156),k10_relat_1(C_155,B_157))
      | ~ r1_tarski(A_156,B_157)
      | ~ v1_relat_1(C_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1077,plain,(
    ! [A_215,C_216,B_217,A_218] :
      ( r1_tarski(A_215,k10_relat_1(C_216,B_217))
      | ~ r1_tarski(A_215,k10_relat_1(C_216,A_218))
      | ~ r1_tarski(A_218,B_217)
      | ~ v1_relat_1(C_216) ) ),
    inference(resolution,[status(thm)],[c_696,c_16])).

tff(c_1084,plain,(
    ! [D_175,B_217] :
      ( r1_tarski(D_175,k10_relat_1('#skF_3',B_217))
      | ~ r1_tarski(k9_relat_1('#skF_3',D_175),B_217)
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(D_175,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_902,c_1077])).

tff(c_1099,plain,(
    ! [D_219,B_220] :
      ( r1_tarski(D_219,k10_relat_1('#skF_3',B_220))
      | ~ r1_tarski(k9_relat_1('#skF_3',D_219),B_220)
      | ~ r1_tarski(D_219,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_1084])).

tff(c_1135,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_764,c_1099])).

tff(c_1179,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1135])).

tff(c_1181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_714,c_1179])).

%------------------------------------------------------------------------------
