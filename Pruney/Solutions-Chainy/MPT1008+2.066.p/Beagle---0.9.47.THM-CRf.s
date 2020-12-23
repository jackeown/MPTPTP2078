%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:35 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 288 expanded)
%              Number of leaves         :   59 ( 124 expanded)
%              Depth                    :   12
%              Number of atoms          :  148 ( 546 expanded)
%              Number of equality atoms :   78 ( 197 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_148,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_funct_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_86,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_61,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_85,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_136,axiom,(
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

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_231,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_235,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_231])).

tff(c_459,plain,(
    ! [C_93,A_94,B_95] :
      ( v4_relat_1(C_93,A_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_463,plain,(
    v4_relat_1('#skF_3',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_78,c_459])).

tff(c_38,plain,(
    ! [B_32,A_31] :
      ( k7_relat_1(B_32,A_31) = B_32
      | ~ v4_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_466,plain,
    ( k7_relat_1('#skF_3',k1_tarski('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_463,c_38])).

tff(c_469,plain,(
    k7_relat_1('#skF_3',k1_tarski('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_466])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(k1_tarski(A_18),B_19)
      | r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_488,plain,(
    ! [A_102,B_103] :
      ( k7_relat_1(A_102,B_103) = k1_xboole_0
      | ~ r1_xboole_0(B_103,k1_relat_1(A_102))
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_496,plain,(
    ! [A_102,A_18] :
      ( k7_relat_1(A_102,k1_tarski(A_18)) = k1_xboole_0
      | ~ v1_relat_1(A_102)
      | r2_hidden(A_18,k1_relat_1(A_102)) ) ),
    inference(resolution,[status(thm)],[c_22,c_488])).

tff(c_615,plain,(
    ! [A_113,B_114,C_115] :
      ( k2_relset_1(A_113,B_114,C_115) = k2_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_619,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_615])).

tff(c_74,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') != k1_tarski(k1_funct_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_620,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_74])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_971,plain,(
    ! [B_149,A_150] :
      ( k2_relat_1(k7_relat_1(B_149,k1_tarski(A_150))) = k1_tarski(k1_funct_1(B_149,A_150))
      | ~ r2_hidden(A_150,k1_relat_1(B_149))
      | ~ v1_funct_1(B_149)
      | ~ v1_relat_1(B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_989,plain,
    ( k1_tarski(k1_funct_1('#skF_3','#skF_1')) = k2_relat_1('#skF_3')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_469,c_971])).

tff(c_996,plain,
    ( k1_tarski(k1_funct_1('#skF_3','#skF_1')) = k2_relat_1('#skF_3')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_82,c_989])).

tff(c_997,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_620,c_996])).

tff(c_1000,plain,
    ( k7_relat_1('#skF_3',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_496,c_997])).

tff(c_1003,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_469,c_1000])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_236,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k4_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_248,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_236])).

tff(c_255,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_248])).

tff(c_319,plain,(
    ! [A_82,B_83] : k4_xboole_0(A_82,k4_xboole_0(A_82,B_83)) = k3_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_345,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_319])).

tff(c_351,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_345])).

tff(c_24,plain,(
    ! [B_21] : k4_xboole_0(k1_tarski(B_21),k1_tarski(B_21)) != k1_tarski(B_21) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_353,plain,(
    ! [B_21] : k1_tarski(B_21) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_24])).

tff(c_1018,plain,(
    ! [B_21] : k1_tarski(B_21) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1003,c_353])).

tff(c_44,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_95,plain,(
    ! [A_54] : v1_relat_1(k6_relat_1(A_54)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_97,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_95])).

tff(c_42,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_40,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_301,plain,(
    ! [A_81] :
      ( k10_relat_1(A_81,k2_relat_1(A_81)) = k1_relat_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_310,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_301])).

tff(c_314,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_42,c_310])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_151,plain,(
    ! [A_63] :
      ( k1_xboole_0 = A_63
      | ~ r1_tarski(A_63,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_168,plain,(
    ! [B_6] : k3_xboole_0(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_151])).

tff(c_552,plain,(
    ! [B_108,A_109] :
      ( k10_relat_1(B_108,k3_xboole_0(k2_relat_1(B_108),A_109)) = k10_relat_1(B_108,A_109)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_569,plain,(
    ! [A_109] :
      ( k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_109)) = k10_relat_1(k1_xboole_0,A_109)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_552])).

tff(c_575,plain,(
    ! [A_109] : k10_relat_1(k1_xboole_0,A_109) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_314,c_168,c_569])).

tff(c_1012,plain,(
    ! [A_109] : k10_relat_1('#skF_3',A_109) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1003,c_1003,c_575])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_80,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_762,plain,(
    ! [A_125,B_126,C_127,D_128] :
      ( k8_relset_1(A_125,B_126,C_127,D_128) = k10_relat_1(C_127,D_128)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_765,plain,(
    ! [D_128] : k8_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3',D_128) = k10_relat_1('#skF_3',D_128) ),
    inference(resolution,[status(thm)],[c_78,c_762])).

tff(c_842,plain,(
    ! [A_132,B_133,C_134] :
      ( k8_relset_1(A_132,B_133,C_134,B_133) = k1_relset_1(A_132,B_133,C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_844,plain,(
    k8_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3','#skF_2') = k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_842])).

tff(c_846,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_765,c_844])).

tff(c_954,plain,(
    ! [B_146,A_147,C_148] :
      ( k1_xboole_0 = B_146
      | k1_relset_1(A_147,B_146,C_148) = A_147
      | ~ v1_funct_2(C_148,A_147,B_146)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_147,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_957,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_954])).

tff(c_960,plain,
    ( k1_xboole_0 = '#skF_2'
    | k10_relat_1('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_846,c_957])).

tff(c_961,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_960])).

tff(c_1143,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1012,c_961])).

tff(c_1146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1018,c_1143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:45:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.52  
% 3.07/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.07/1.52  
% 3.07/1.52  %Foreground sorts:
% 3.07/1.52  
% 3.07/1.52  
% 3.07/1.52  %Background operators:
% 3.07/1.52  
% 3.07/1.52  
% 3.07/1.52  %Foreground operators:
% 3.07/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.07/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.07/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.07/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.07/1.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.07/1.52  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.07/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.07/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.07/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.07/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.07/1.52  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.07/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.07/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.07/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.07/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.07/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.07/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.07/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.07/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.07/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.07/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.52  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.07/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.07/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.07/1.52  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.07/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.07/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.07/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.07/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.52  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.07/1.52  
% 3.31/1.54  tff(f_148, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.31/1.54  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.31/1.54  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.31/1.54  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.31/1.54  tff(f_52, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.31/1.54  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 3.31/1.54  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.31/1.54  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_funct_1)).
% 3.31/1.54  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.31/1.54  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.31/1.54  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.31/1.54  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.31/1.54  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.31/1.54  tff(f_86, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 3.31/1.54  tff(f_61, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.31/1.54  tff(f_85, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.31/1.54  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.31/1.54  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.31/1.54  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.31/1.54  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 3.31/1.54  tff(f_112, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.31/1.54  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.31/1.54  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.31/1.54  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.31/1.54  tff(c_231, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.31/1.54  tff(c_235, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_231])).
% 3.31/1.54  tff(c_459, plain, (![C_93, A_94, B_95]: (v4_relat_1(C_93, A_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.31/1.54  tff(c_463, plain, (v4_relat_1('#skF_3', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_78, c_459])).
% 3.31/1.54  tff(c_38, plain, (![B_32, A_31]: (k7_relat_1(B_32, A_31)=B_32 | ~v4_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.31/1.54  tff(c_466, plain, (k7_relat_1('#skF_3', k1_tarski('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_463, c_38])).
% 3.31/1.54  tff(c_469, plain, (k7_relat_1('#skF_3', k1_tarski('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_235, c_466])).
% 3.31/1.54  tff(c_22, plain, (![A_18, B_19]: (r1_xboole_0(k1_tarski(A_18), B_19) | r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.31/1.54  tff(c_488, plain, (![A_102, B_103]: (k7_relat_1(A_102, B_103)=k1_xboole_0 | ~r1_xboole_0(B_103, k1_relat_1(A_102)) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.31/1.54  tff(c_496, plain, (![A_102, A_18]: (k7_relat_1(A_102, k1_tarski(A_18))=k1_xboole_0 | ~v1_relat_1(A_102) | r2_hidden(A_18, k1_relat_1(A_102)))), inference(resolution, [status(thm)], [c_22, c_488])).
% 3.31/1.54  tff(c_615, plain, (![A_113, B_114, C_115]: (k2_relset_1(A_113, B_114, C_115)=k2_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.31/1.54  tff(c_619, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_615])).
% 3.31/1.54  tff(c_74, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')!=k1_tarski(k1_funct_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.31/1.54  tff(c_620, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_619, c_74])).
% 3.31/1.54  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.31/1.54  tff(c_971, plain, (![B_149, A_150]: (k2_relat_1(k7_relat_1(B_149, k1_tarski(A_150)))=k1_tarski(k1_funct_1(B_149, A_150)) | ~r2_hidden(A_150, k1_relat_1(B_149)) | ~v1_funct_1(B_149) | ~v1_relat_1(B_149))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.31/1.54  tff(c_989, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))=k2_relat_1('#skF_3') | ~r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_469, c_971])).
% 3.31/1.54  tff(c_996, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))=k2_relat_1('#skF_3') | ~r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_82, c_989])).
% 3.31/1.54  tff(c_997, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_620, c_996])).
% 3.31/1.54  tff(c_1000, plain, (k7_relat_1('#skF_3', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_496, c_997])).
% 3.31/1.54  tff(c_1003, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_235, c_469, c_1000])).
% 3.31/1.54  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.31/1.54  tff(c_14, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.31/1.54  tff(c_236, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k4_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.31/1.54  tff(c_248, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_236])).
% 3.31/1.54  tff(c_255, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_248])).
% 3.31/1.54  tff(c_319, plain, (![A_82, B_83]: (k4_xboole_0(A_82, k4_xboole_0(A_82, B_83))=k3_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.31/1.54  tff(c_345, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_255, c_319])).
% 3.31/1.54  tff(c_351, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_345])).
% 3.31/1.54  tff(c_24, plain, (![B_21]: (k4_xboole_0(k1_tarski(B_21), k1_tarski(B_21))!=k1_tarski(B_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.31/1.54  tff(c_353, plain, (![B_21]: (k1_tarski(B_21)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_351, c_24])).
% 3.31/1.54  tff(c_1018, plain, (![B_21]: (k1_tarski(B_21)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1003, c_353])).
% 3.31/1.54  tff(c_44, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.31/1.54  tff(c_95, plain, (![A_54]: (v1_relat_1(k6_relat_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.31/1.54  tff(c_97, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_95])).
% 3.31/1.54  tff(c_42, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.31/1.54  tff(c_40, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.31/1.54  tff(c_301, plain, (![A_81]: (k10_relat_1(A_81, k2_relat_1(A_81))=k1_relat_1(A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.31/1.54  tff(c_310, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_301])).
% 3.31/1.54  tff(c_314, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_97, c_42, c_310])).
% 3.31/1.54  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.31/1.54  tff(c_151, plain, (![A_63]: (k1_xboole_0=A_63 | ~r1_tarski(A_63, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.31/1.54  tff(c_168, plain, (![B_6]: (k3_xboole_0(k1_xboole_0, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_151])).
% 3.31/1.54  tff(c_552, plain, (![B_108, A_109]: (k10_relat_1(B_108, k3_xboole_0(k2_relat_1(B_108), A_109))=k10_relat_1(B_108, A_109) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.54  tff(c_569, plain, (![A_109]: (k10_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_109))=k10_relat_1(k1_xboole_0, A_109) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_552])).
% 3.31/1.54  tff(c_575, plain, (![A_109]: (k10_relat_1(k1_xboole_0, A_109)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_97, c_314, c_168, c_569])).
% 3.31/1.54  tff(c_1012, plain, (![A_109]: (k10_relat_1('#skF_3', A_109)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1003, c_1003, c_575])).
% 3.31/1.54  tff(c_76, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.31/1.54  tff(c_80, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.31/1.54  tff(c_762, plain, (![A_125, B_126, C_127, D_128]: (k8_relset_1(A_125, B_126, C_127, D_128)=k10_relat_1(C_127, D_128) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.31/1.54  tff(c_765, plain, (![D_128]: (k8_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', D_128)=k10_relat_1('#skF_3', D_128))), inference(resolution, [status(thm)], [c_78, c_762])).
% 3.31/1.54  tff(c_842, plain, (![A_132, B_133, C_134]: (k8_relset_1(A_132, B_133, C_134, B_133)=k1_relset_1(A_132, B_133, C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.31/1.54  tff(c_844, plain, (k8_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', '#skF_2')=k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_78, c_842])).
% 3.31/1.54  tff(c_846, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_765, c_844])).
% 3.31/1.54  tff(c_954, plain, (![B_146, A_147, C_148]: (k1_xboole_0=B_146 | k1_relset_1(A_147, B_146, C_148)=A_147 | ~v1_funct_2(C_148, A_147, B_146) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_147, B_146))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.31/1.54  tff(c_957, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_78, c_954])).
% 3.31/1.54  tff(c_960, plain, (k1_xboole_0='#skF_2' | k10_relat_1('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_846, c_957])).
% 3.31/1.54  tff(c_961, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_76, c_960])).
% 3.31/1.54  tff(c_1143, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1012, c_961])).
% 3.31/1.54  tff(c_1146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1018, c_1143])).
% 3.31/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.54  
% 3.31/1.54  Inference rules
% 3.31/1.54  ----------------------
% 3.31/1.54  #Ref     : 0
% 3.31/1.54  #Sup     : 240
% 3.31/1.54  #Fact    : 0
% 3.31/1.54  #Define  : 0
% 3.31/1.54  #Split   : 0
% 3.31/1.54  #Chain   : 0
% 3.31/1.54  #Close   : 0
% 3.31/1.54  
% 3.31/1.54  Ordering : KBO
% 3.31/1.54  
% 3.31/1.54  Simplification rules
% 3.31/1.54  ----------------------
% 3.31/1.54  #Subsume      : 12
% 3.31/1.54  #Demod        : 239
% 3.31/1.54  #Tautology    : 178
% 3.31/1.54  #SimpNegUnit  : 13
% 3.31/1.54  #BackRed      : 38
% 3.31/1.54  
% 3.31/1.54  #Partial instantiations: 0
% 3.31/1.54  #Strategies tried      : 1
% 3.31/1.54  
% 3.31/1.54  Timing (in seconds)
% 3.31/1.54  ----------------------
% 3.31/1.55  Preprocessing        : 0.36
% 3.31/1.55  Parsing              : 0.19
% 3.31/1.55  CNF conversion       : 0.02
% 3.31/1.55  Main loop            : 0.38
% 3.31/1.55  Inferencing          : 0.13
% 3.31/1.55  Reduction            : 0.14
% 3.31/1.55  Demodulation         : 0.10
% 3.31/1.55  BG Simplification    : 0.02
% 3.31/1.55  Subsumption          : 0.05
% 3.31/1.55  Abstraction          : 0.02
% 3.31/1.55  MUC search           : 0.00
% 3.31/1.55  Cooper               : 0.00
% 3.31/1.55  Total                : 0.77
% 3.31/1.55  Index Insertion      : 0.00
% 3.31/1.55  Index Deletion       : 0.00
% 3.31/1.55  Index Matching       : 0.00
% 3.31/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
