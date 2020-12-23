%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:19 EST 2020

% Result     : Theorem 4.60s
% Output     : CNFRefutation 4.95s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 146 expanded)
%              Number of leaves         :   41 (  67 expanded)
%              Depth                    :    8
%              Number of atoms          :  136 ( 374 expanded)
%              Number of equality atoms :   33 (  50 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
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

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1967,plain,(
    ! [A_260,B_261,C_262,D_263] :
      ( k8_relset_1(A_260,B_261,C_262,D_263) = k10_relat_1(C_262,D_263)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1974,plain,(
    ! [D_263] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_263) = k10_relat_1('#skF_3',D_263) ),
    inference(resolution,[status(thm)],[c_50,c_1967])).

tff(c_60,plain,
    ( ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_69,plain,(
    ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_656,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( k7_relset_1(A_116,B_117,C_118,D_119) = k9_relat_1(C_118,D_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_663,plain,(
    ! [D_119] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_119) = k9_relat_1('#skF_3',D_119) ),
    inference(resolution,[status(thm)],[c_50,c_656])).

tff(c_664,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_69])).

tff(c_275,plain,(
    ! [C_84,A_85,B_86] :
      ( v1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_284,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_275])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_703,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( k8_relset_1(A_123,B_124,C_125,D_126) = k10_relat_1(C_125,D_126)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_710,plain,(
    ! [D_126] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_126) = k10_relat_1('#skF_3',D_126) ),
    inference(resolution,[status(thm)],[c_50,c_703])).

tff(c_66,plain,
    ( r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5')
    | r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_174,plain,(
    r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_230,plain,(
    k3_xboole_0('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_174,c_6])).

tff(c_714,plain,(
    k3_xboole_0('#skF_4',k10_relat_1('#skF_3','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_710,c_230])).

tff(c_1212,plain,(
    ! [C_199,A_200,B_201] :
      ( r1_tarski(k9_relat_1(C_199,k3_xboole_0(A_200,k10_relat_1(C_199,B_201))),k3_xboole_0(k9_relat_1(C_199,A_200),B_201))
      | ~ v1_funct_1(C_199)
      | ~ v1_relat_1(C_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1245,plain,
    ( r1_tarski(k9_relat_1('#skF_3','#skF_4'),k3_xboole_0(k9_relat_1('#skF_3','#skF_4'),'#skF_5'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_714,c_1212])).

tff(c_1291,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_4'),k3_xboole_0('#skF_5',k9_relat_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_54,c_2,c_1245])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_tarski(A_3,k3_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1319,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1291,c_4])).

tff(c_1329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_664,c_1319])).

tff(c_1330,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_1330])).

tff(c_1385,plain,(
    ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1975,plain,(
    ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1974,c_1385])).

tff(c_1630,plain,(
    ! [C_226,A_227,B_228] :
      ( v1_relat_1(C_226)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_227,B_228))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1639,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1630])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1420,plain,(
    ! [A_209,B_210] :
      ( r1_tarski(A_209,B_210)
      | ~ m1_subset_1(A_209,k1_zfmisc_1(B_210)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1432,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1420])).

tff(c_52,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1825,plain,(
    ! [A_243,B_244,C_245] :
      ( k1_relset_1(A_243,B_244,C_245) = k1_relat_1(C_245)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1834,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1825])).

tff(c_2225,plain,(
    ! [B_314,A_315,C_316] :
      ( k1_xboole_0 = B_314
      | k1_relset_1(A_315,B_314,C_316) = A_315
      | ~ v1_funct_2(C_316,A_315,B_314)
      | ~ m1_subset_1(C_316,k1_zfmisc_1(k2_zfmisc_1(A_315,B_314))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2232,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2225])).

tff(c_2236,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1834,c_2232])).

tff(c_2237,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2236])).

tff(c_1903,plain,(
    ! [A_255,B_256,C_257,D_258] :
      ( k7_relset_1(A_255,B_256,C_257,D_258) = k9_relat_1(C_257,D_258)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1910,plain,(
    ! [D_258] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_258) = k9_relat_1('#skF_3',D_258) ),
    inference(resolution,[status(thm)],[c_50,c_1903])).

tff(c_1386,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1914,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1910,c_1386])).

tff(c_2629,plain,(
    ! [A_336,C_337,B_338] :
      ( r1_tarski(A_336,k10_relat_1(C_337,B_338))
      | ~ r1_tarski(k9_relat_1(C_337,A_336),B_338)
      | ~ r1_tarski(A_336,k1_relat_1(C_337))
      | ~ v1_funct_1(C_337)
      | ~ v1_relat_1(C_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2665,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1914,c_2629])).

tff(c_2707,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1639,c_54,c_1432,c_2237,c_2665])).

tff(c_2709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1975,c_2707])).

tff(c_2710,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2236])).

tff(c_8,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1548,plain,(
    ! [B_217,A_218] :
      ( ~ r1_xboole_0(B_217,A_218)
      | ~ r1_tarski(B_217,A_218)
      | v1_xboole_0(B_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1553,plain,(
    ! [A_219] :
      ( ~ r1_tarski(A_219,k1_xboole_0)
      | v1_xboole_0(A_219) ) ),
    inference(resolution,[status(thm)],[c_10,c_1548])).

tff(c_1558,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_1553])).

tff(c_2727,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2710,c_1558])).

tff(c_2734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2727])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:44:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.60/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.91  
% 4.60/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.91  %$ v1_funct_2 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.60/1.91  
% 4.60/1.91  %Foreground sorts:
% 4.60/1.91  
% 4.60/1.91  
% 4.60/1.91  %Background operators:
% 4.60/1.91  
% 4.60/1.91  
% 4.60/1.91  %Foreground operators:
% 4.60/1.91  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.60/1.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.60/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.91  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.60/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.60/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.60/1.91  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.60/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.60/1.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.60/1.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.60/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.60/1.91  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.60/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.60/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.60/1.91  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.60/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.60/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.91  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.60/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.60/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.60/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.60/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.60/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.60/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.60/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.60/1.91  
% 4.95/1.92  tff(f_132, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (r1_tarski(k7_relset_1(A, B, C, D), E) <=> r1_tarski(D, k8_relset_1(A, B, C, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_2)).
% 4.95/1.92  tff(f_83, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.95/1.92  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.95/1.92  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.95/1.92  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.95/1.92  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.95/1.92  tff(f_57, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_funct_1)).
% 4.95/1.92  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 4.95/1.92  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.95/1.92  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.95/1.92  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.95/1.92  tff(f_67, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 4.95/1.92  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.95/1.92  tff(f_39, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.95/1.92  tff(f_47, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 4.95/1.92  tff(c_56, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.95/1.92  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.95/1.92  tff(c_1967, plain, (![A_260, B_261, C_262, D_263]: (k8_relset_1(A_260, B_261, C_262, D_263)=k10_relat_1(C_262, D_263) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.95/1.92  tff(c_1974, plain, (![D_263]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_263)=k10_relat_1('#skF_3', D_263))), inference(resolution, [status(thm)], [c_50, c_1967])).
% 4.95/1.92  tff(c_60, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.95/1.92  tff(c_69, plain, (~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_60])).
% 4.95/1.92  tff(c_656, plain, (![A_116, B_117, C_118, D_119]: (k7_relset_1(A_116, B_117, C_118, D_119)=k9_relat_1(C_118, D_119) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.95/1.92  tff(c_663, plain, (![D_119]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_119)=k9_relat_1('#skF_3', D_119))), inference(resolution, [status(thm)], [c_50, c_656])).
% 4.95/1.92  tff(c_664, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_663, c_69])).
% 4.95/1.92  tff(c_275, plain, (![C_84, A_85, B_86]: (v1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.95/1.92  tff(c_284, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_275])).
% 4.95/1.92  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.95/1.92  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.95/1.92  tff(c_703, plain, (![A_123, B_124, C_125, D_126]: (k8_relset_1(A_123, B_124, C_125, D_126)=k10_relat_1(C_125, D_126) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.95/1.92  tff(c_710, plain, (![D_126]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_126)=k10_relat_1('#skF_3', D_126))), inference(resolution, [status(thm)], [c_50, c_703])).
% 4.95/1.92  tff(c_66, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5') | r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.95/1.92  tff(c_174, plain, (r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_66])).
% 4.95/1.92  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.95/1.92  tff(c_230, plain, (k3_xboole_0('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_174, c_6])).
% 4.95/1.92  tff(c_714, plain, (k3_xboole_0('#skF_4', k10_relat_1('#skF_3', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_710, c_230])).
% 4.95/1.92  tff(c_1212, plain, (![C_199, A_200, B_201]: (r1_tarski(k9_relat_1(C_199, k3_xboole_0(A_200, k10_relat_1(C_199, B_201))), k3_xboole_0(k9_relat_1(C_199, A_200), B_201)) | ~v1_funct_1(C_199) | ~v1_relat_1(C_199))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.95/1.92  tff(c_1245, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_4'), k3_xboole_0(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_714, c_1212])).
% 4.95/1.92  tff(c_1291, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_4'), k3_xboole_0('#skF_5', k9_relat_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_54, c_2, c_1245])).
% 4.95/1.92  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, B_4) | ~r1_tarski(A_3, k3_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.95/1.93  tff(c_1319, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_1291, c_4])).
% 4.95/1.93  tff(c_1329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_664, c_1319])).
% 4.95/1.93  tff(c_1330, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_66])).
% 4.95/1.93  tff(c_1384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_1330])).
% 4.95/1.93  tff(c_1385, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_60])).
% 4.95/1.93  tff(c_1975, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1974, c_1385])).
% 4.95/1.93  tff(c_1630, plain, (![C_226, A_227, B_228]: (v1_relat_1(C_226) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_227, B_228))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.95/1.93  tff(c_1639, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_1630])).
% 4.95/1.93  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.95/1.93  tff(c_1420, plain, (![A_209, B_210]: (r1_tarski(A_209, B_210) | ~m1_subset_1(A_209, k1_zfmisc_1(B_210)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.95/1.93  tff(c_1432, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_1420])).
% 4.95/1.93  tff(c_52, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.95/1.93  tff(c_1825, plain, (![A_243, B_244, C_245]: (k1_relset_1(A_243, B_244, C_245)=k1_relat_1(C_245) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.95/1.93  tff(c_1834, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_1825])).
% 4.95/1.93  tff(c_2225, plain, (![B_314, A_315, C_316]: (k1_xboole_0=B_314 | k1_relset_1(A_315, B_314, C_316)=A_315 | ~v1_funct_2(C_316, A_315, B_314) | ~m1_subset_1(C_316, k1_zfmisc_1(k2_zfmisc_1(A_315, B_314))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.95/1.93  tff(c_2232, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_2225])).
% 4.95/1.93  tff(c_2236, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1834, c_2232])).
% 4.95/1.93  tff(c_2237, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_2236])).
% 4.95/1.93  tff(c_1903, plain, (![A_255, B_256, C_257, D_258]: (k7_relset_1(A_255, B_256, C_257, D_258)=k9_relat_1(C_257, D_258) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.95/1.93  tff(c_1910, plain, (![D_258]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_258)=k9_relat_1('#skF_3', D_258))), inference(resolution, [status(thm)], [c_50, c_1903])).
% 4.95/1.93  tff(c_1386, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 4.95/1.93  tff(c_1914, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1910, c_1386])).
% 4.95/1.93  tff(c_2629, plain, (![A_336, C_337, B_338]: (r1_tarski(A_336, k10_relat_1(C_337, B_338)) | ~r1_tarski(k9_relat_1(C_337, A_336), B_338) | ~r1_tarski(A_336, k1_relat_1(C_337)) | ~v1_funct_1(C_337) | ~v1_relat_1(C_337))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.95/1.93  tff(c_2665, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1914, c_2629])).
% 4.95/1.93  tff(c_2707, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1639, c_54, c_1432, c_2237, c_2665])).
% 4.95/1.93  tff(c_2709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1975, c_2707])).
% 4.95/1.93  tff(c_2710, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2236])).
% 4.95/1.93  tff(c_8, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.95/1.93  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.95/1.93  tff(c_1548, plain, (![B_217, A_218]: (~r1_xboole_0(B_217, A_218) | ~r1_tarski(B_217, A_218) | v1_xboole_0(B_217))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.95/1.93  tff(c_1553, plain, (![A_219]: (~r1_tarski(A_219, k1_xboole_0) | v1_xboole_0(A_219))), inference(resolution, [status(thm)], [c_10, c_1548])).
% 4.95/1.93  tff(c_1558, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1553])).
% 4.95/1.93  tff(c_2727, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2710, c_1558])).
% 4.95/1.93  tff(c_2734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_2727])).
% 4.95/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.95/1.93  
% 4.95/1.93  Inference rules
% 4.95/1.93  ----------------------
% 4.95/1.93  #Ref     : 0
% 4.95/1.93  #Sup     : 612
% 4.95/1.93  #Fact    : 0
% 4.95/1.93  #Define  : 0
% 4.95/1.93  #Split   : 16
% 4.95/1.93  #Chain   : 0
% 4.95/1.93  #Close   : 0
% 4.95/1.93  
% 4.95/1.93  Ordering : KBO
% 4.95/1.93  
% 4.95/1.93  Simplification rules
% 4.95/1.93  ----------------------
% 4.95/1.93  #Subsume      : 82
% 4.95/1.93  #Demod        : 433
% 4.95/1.93  #Tautology    : 330
% 4.95/1.93  #SimpNegUnit  : 12
% 4.95/1.93  #BackRed      : 88
% 4.95/1.93  
% 4.95/1.93  #Partial instantiations: 0
% 4.95/1.93  #Strategies tried      : 1
% 4.95/1.93  
% 4.95/1.93  Timing (in seconds)
% 4.95/1.93  ----------------------
% 4.95/1.93  Preprocessing        : 0.36
% 4.95/1.93  Parsing              : 0.20
% 4.95/1.93  CNF conversion       : 0.03
% 4.95/1.93  Main loop            : 0.75
% 4.95/1.93  Inferencing          : 0.25
% 4.95/1.93  Reduction            : 0.27
% 4.95/1.93  Demodulation         : 0.19
% 4.95/1.93  BG Simplification    : 0.03
% 4.95/1.93  Subsumption          : 0.12
% 4.95/1.93  Abstraction          : 0.03
% 4.95/1.93  MUC search           : 0.00
% 4.95/1.93  Cooper               : 0.00
% 4.95/1.93  Total                : 1.15
% 4.95/1.93  Index Insertion      : 0.00
% 4.95/1.93  Index Deletion       : 0.00
% 4.95/1.93  Index Matching       : 0.00
% 4.95/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
