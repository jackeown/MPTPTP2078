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
% DateTime   : Thu Dec  3 10:14:49 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 239 expanded)
%              Number of leaves         :   46 ( 102 expanded)
%              Depth                    :   11
%              Number of atoms          :  132 ( 455 expanded)
%              Number of equality atoms :   48 ( 110 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_78,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_104,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_113,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_104])).

tff(c_20,plain,(
    ! [A_19] : k9_relat_1(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_667,plain,(
    ! [B_146,A_147] :
      ( r1_xboole_0(k1_relat_1(B_146),A_147)
      | k9_relat_1(B_146,A_147) != k1_xboole_0
      | ~ v1_relat_1(B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_676,plain,(
    ! [A_147] :
      ( r1_xboole_0(k1_xboole_0,A_147)
      | k9_relat_1(k1_xboole_0,A_147) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_667])).

tff(c_681,plain,(
    ! [A_147] : r1_xboole_0(k1_xboole_0,A_147) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_20,c_676])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_112,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_104])).

tff(c_137,plain,(
    ! [C_52,A_53,B_54] :
      ( v4_relat_1(C_52,A_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_145,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_137])).

tff(c_212,plain,(
    ! [B_68,A_69] :
      ( k7_relat_1(B_68,A_69) = B_68
      | ~ v4_relat_1(B_68,A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_215,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_145,c_212])).

tff(c_221,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_215])).

tff(c_18,plain,(
    ! [B_18,A_17] :
      ( k2_relat_1(k7_relat_1(B_18,A_17)) = k9_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_240,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_18])).

tff(c_244,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_240])).

tff(c_157,plain,(
    ! [B_59,A_60] :
      ( k2_relat_1(k7_relat_1(B_59,A_60)) = k9_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k9_relat_1(B_16,A_15),k2_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_369,plain,(
    ! [B_99,A_100,A_101] :
      ( r1_tarski(k9_relat_1(k7_relat_1(B_99,A_100),A_101),k9_relat_1(B_99,A_100))
      | ~ v1_relat_1(k7_relat_1(B_99,A_100))
      | ~ v1_relat_1(B_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_16])).

tff(c_375,plain,(
    ! [A_101] :
      ( r1_tarski(k9_relat_1('#skF_4',A_101),k9_relat_1('#skF_4',k1_tarski('#skF_1')))
      | ~ v1_relat_1(k7_relat_1('#skF_4',k1_tarski('#skF_1')))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_369])).

tff(c_392,plain,(
    ! [A_101] : r1_tarski(k9_relat_1('#skF_4',A_101),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_112,c_221,c_244,c_375])).

tff(c_36,plain,(
    ! [A_26] :
      ( k1_relat_1(A_26) = k1_xboole_0
      | k2_relat_1(A_26) != k1_xboole_0
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_117,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_112,c_36])).

tff(c_135,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_14,plain,(
    ! [A_12,B_14] :
      ( k9_relat_1(A_12,k1_tarski(B_14)) = k11_relat_1(A_12,B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_257,plain,
    ( k11_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_14])).

tff(c_267,plain,(
    k11_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_257])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( r2_hidden(A_22,k1_relat_1(B_23))
      | k11_relat_1(B_23,A_22) = k1_xboole_0
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_359,plain,(
    ! [B_97,A_98] :
      ( k1_tarski(k1_funct_1(B_97,A_98)) = k11_relat_1(B_97,A_98)
      | ~ r2_hidden(A_98,k1_relat_1(B_97))
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_397,plain,(
    ! [B_102,A_103] :
      ( k1_tarski(k1_funct_1(B_102,A_103)) = k11_relat_1(B_102,A_103)
      | ~ v1_funct_1(B_102)
      | k11_relat_1(B_102,A_103) = k1_xboole_0
      | ~ v1_relat_1(B_102) ) ),
    inference(resolution,[status(thm)],[c_26,c_359])).

tff(c_333,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( k7_relset_1(A_89,B_90,C_91,D_92) = k9_relat_1(C_91,D_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_339,plain,(
    ! [D_92] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_92) = k9_relat_1('#skF_4',D_92) ),
    inference(resolution,[status(thm)],[c_54,c_333])).

tff(c_50,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_349,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_50])).

tff(c_403,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | k11_relat_1('#skF_4','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_349])).

tff(c_412,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_267,c_58,c_267,c_403])).

tff(c_413,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_412])).

tff(c_431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_413])).

tff(c_432,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_596,plain,(
    ! [B_127,A_128] :
      ( k9_relat_1(B_127,A_128) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_127),A_128)
      | ~ v1_relat_1(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_599,plain,(
    ! [A_128] :
      ( k9_relat_1('#skF_4',A_128) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_128)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_596])).

tff(c_604,plain,(
    ! [A_128] :
      ( k9_relat_1('#skF_4',A_128) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_599])).

tff(c_698,plain,(
    ! [A_128] : k9_relat_1('#skF_4',A_128) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_604])).

tff(c_773,plain,(
    ! [A_156,B_157,C_158,D_159] :
      ( k7_relset_1(A_156,B_157,C_158,D_159) = k9_relat_1(C_158,D_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_775,plain,(
    ! [D_159] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_159) = k9_relat_1('#skF_4',D_159) ),
    inference(resolution,[status(thm)],[c_54,c_773])).

tff(c_780,plain,(
    ! [D_159] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_159) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_775])).

tff(c_790,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_50])).

tff(c_793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_790])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:47:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.48  
% 3.00/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.49  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.00/1.49  
% 3.00/1.49  %Foreground sorts:
% 3.00/1.49  
% 3.00/1.49  
% 3.00/1.49  %Background operators:
% 3.00/1.49  
% 3.00/1.49  
% 3.00/1.49  %Foreground operators:
% 3.00/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.00/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.00/1.49  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.00/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.00/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.00/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.00/1.49  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.00/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.00/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.00/1.49  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.00/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.00/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.00/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.00/1.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.00/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.00/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.00/1.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.00/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.00/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.00/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.00/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.00/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.00/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.00/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.00/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.00/1.49  
% 3.00/1.50  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.00/1.50  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.00/1.50  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.00/1.50  tff(f_56, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 3.00/1.50  tff(f_78, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.00/1.50  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 3.00/1.50  tff(f_118, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.00/1.50  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.00/1.50  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.00/1.50  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.00/1.50  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.00/1.50  tff(f_84, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 3.00/1.50  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.00/1.50  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.00/1.50  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 3.00/1.50  tff(f_106, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.00/1.50  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.00/1.50  tff(c_10, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.00/1.50  tff(c_104, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.00/1.50  tff(c_113, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_104])).
% 3.00/1.50  tff(c_20, plain, (![A_19]: (k9_relat_1(k1_xboole_0, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.00/1.50  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.00/1.50  tff(c_667, plain, (![B_146, A_147]: (r1_xboole_0(k1_relat_1(B_146), A_147) | k9_relat_1(B_146, A_147)!=k1_xboole_0 | ~v1_relat_1(B_146))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.00/1.50  tff(c_676, plain, (![A_147]: (r1_xboole_0(k1_xboole_0, A_147) | k9_relat_1(k1_xboole_0, A_147)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_667])).
% 3.00/1.50  tff(c_681, plain, (![A_147]: (r1_xboole_0(k1_xboole_0, A_147))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_20, c_676])).
% 3.00/1.50  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.00/1.50  tff(c_112, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_104])).
% 3.00/1.50  tff(c_137, plain, (![C_52, A_53, B_54]: (v4_relat_1(C_52, A_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.00/1.50  tff(c_145, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_54, c_137])).
% 3.00/1.50  tff(c_212, plain, (![B_68, A_69]: (k7_relat_1(B_68, A_69)=B_68 | ~v4_relat_1(B_68, A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.00/1.50  tff(c_215, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_145, c_212])).
% 3.00/1.50  tff(c_221, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_215])).
% 3.00/1.50  tff(c_18, plain, (![B_18, A_17]: (k2_relat_1(k7_relat_1(B_18, A_17))=k9_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.00/1.50  tff(c_240, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_221, c_18])).
% 3.00/1.50  tff(c_244, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_240])).
% 3.00/1.50  tff(c_157, plain, (![B_59, A_60]: (k2_relat_1(k7_relat_1(B_59, A_60))=k9_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.00/1.50  tff(c_16, plain, (![B_16, A_15]: (r1_tarski(k9_relat_1(B_16, A_15), k2_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.00/1.50  tff(c_369, plain, (![B_99, A_100, A_101]: (r1_tarski(k9_relat_1(k7_relat_1(B_99, A_100), A_101), k9_relat_1(B_99, A_100)) | ~v1_relat_1(k7_relat_1(B_99, A_100)) | ~v1_relat_1(B_99))), inference(superposition, [status(thm), theory('equality')], [c_157, c_16])).
% 3.00/1.50  tff(c_375, plain, (![A_101]: (r1_tarski(k9_relat_1('#skF_4', A_101), k9_relat_1('#skF_4', k1_tarski('#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_4', k1_tarski('#skF_1'))) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_221, c_369])).
% 3.00/1.50  tff(c_392, plain, (![A_101]: (r1_tarski(k9_relat_1('#skF_4', A_101), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_112, c_221, c_244, c_375])).
% 3.00/1.50  tff(c_36, plain, (![A_26]: (k1_relat_1(A_26)=k1_xboole_0 | k2_relat_1(A_26)!=k1_xboole_0 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.00/1.50  tff(c_117, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_112, c_36])).
% 3.00/1.50  tff(c_135, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_117])).
% 3.00/1.50  tff(c_14, plain, (![A_12, B_14]: (k9_relat_1(A_12, k1_tarski(B_14))=k11_relat_1(A_12, B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.00/1.50  tff(c_257, plain, (k11_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_244, c_14])).
% 3.00/1.50  tff(c_267, plain, (k11_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_257])).
% 3.00/1.50  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.00/1.50  tff(c_26, plain, (![A_22, B_23]: (r2_hidden(A_22, k1_relat_1(B_23)) | k11_relat_1(B_23, A_22)=k1_xboole_0 | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.00/1.50  tff(c_359, plain, (![B_97, A_98]: (k1_tarski(k1_funct_1(B_97, A_98))=k11_relat_1(B_97, A_98) | ~r2_hidden(A_98, k1_relat_1(B_97)) | ~v1_funct_1(B_97) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.00/1.50  tff(c_397, plain, (![B_102, A_103]: (k1_tarski(k1_funct_1(B_102, A_103))=k11_relat_1(B_102, A_103) | ~v1_funct_1(B_102) | k11_relat_1(B_102, A_103)=k1_xboole_0 | ~v1_relat_1(B_102))), inference(resolution, [status(thm)], [c_26, c_359])).
% 3.00/1.50  tff(c_333, plain, (![A_89, B_90, C_91, D_92]: (k7_relset_1(A_89, B_90, C_91, D_92)=k9_relat_1(C_91, D_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.00/1.50  tff(c_339, plain, (![D_92]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_92)=k9_relat_1('#skF_4', D_92))), inference(resolution, [status(thm)], [c_54, c_333])).
% 3.00/1.50  tff(c_50, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.00/1.50  tff(c_349, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_339, c_50])).
% 3.00/1.50  tff(c_403, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_1')) | ~v1_funct_1('#skF_4') | k11_relat_1('#skF_4', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_397, c_349])).
% 3.00/1.50  tff(c_412, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_112, c_267, c_58, c_267, c_403])).
% 3.00/1.50  tff(c_413, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_135, c_412])).
% 3.00/1.50  tff(c_431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_392, c_413])).
% 3.00/1.50  tff(c_432, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_117])).
% 3.00/1.50  tff(c_596, plain, (![B_127, A_128]: (k9_relat_1(B_127, A_128)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_127), A_128) | ~v1_relat_1(B_127))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.00/1.50  tff(c_599, plain, (![A_128]: (k9_relat_1('#skF_4', A_128)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_128) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_432, c_596])).
% 3.00/1.50  tff(c_604, plain, (![A_128]: (k9_relat_1('#skF_4', A_128)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_128))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_599])).
% 3.00/1.50  tff(c_698, plain, (![A_128]: (k9_relat_1('#skF_4', A_128)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_681, c_604])).
% 3.00/1.50  tff(c_773, plain, (![A_156, B_157, C_158, D_159]: (k7_relset_1(A_156, B_157, C_158, D_159)=k9_relat_1(C_158, D_159) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.00/1.50  tff(c_775, plain, (![D_159]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_159)=k9_relat_1('#skF_4', D_159))), inference(resolution, [status(thm)], [c_54, c_773])).
% 3.00/1.50  tff(c_780, plain, (![D_159]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_159)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_698, c_775])).
% 3.00/1.50  tff(c_790, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_780, c_50])).
% 3.00/1.50  tff(c_793, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_790])).
% 3.00/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.50  
% 3.00/1.50  Inference rules
% 3.00/1.50  ----------------------
% 3.00/1.50  #Ref     : 0
% 3.00/1.50  #Sup     : 157
% 3.00/1.50  #Fact    : 0
% 3.00/1.50  #Define  : 0
% 3.00/1.50  #Split   : 1
% 3.00/1.50  #Chain   : 0
% 3.00/1.50  #Close   : 0
% 3.00/1.50  
% 3.00/1.50  Ordering : KBO
% 3.00/1.50  
% 3.00/1.50  Simplification rules
% 3.00/1.50  ----------------------
% 3.00/1.50  #Subsume      : 4
% 3.00/1.50  #Demod        : 143
% 3.00/1.50  #Tautology    : 104
% 3.00/1.50  #SimpNegUnit  : 4
% 3.00/1.50  #BackRed      : 6
% 3.00/1.50  
% 3.00/1.50  #Partial instantiations: 0
% 3.00/1.50  #Strategies tried      : 1
% 3.00/1.50  
% 3.00/1.50  Timing (in seconds)
% 3.00/1.50  ----------------------
% 3.00/1.51  Preprocessing        : 0.35
% 3.00/1.51  Parsing              : 0.20
% 3.00/1.51  CNF conversion       : 0.02
% 3.00/1.51  Main loop            : 0.32
% 3.00/1.51  Inferencing          : 0.13
% 3.00/1.51  Reduction            : 0.10
% 3.00/1.51  Demodulation         : 0.07
% 3.00/1.51  BG Simplification    : 0.02
% 3.00/1.51  Subsumption          : 0.05
% 3.00/1.51  Abstraction          : 0.01
% 3.00/1.51  MUC search           : 0.00
% 3.00/1.51  Cooper               : 0.00
% 3.00/1.51  Total                : 0.71
% 3.00/1.51  Index Insertion      : 0.00
% 3.00/1.51  Index Deletion       : 0.00
% 3.00/1.51  Index Matching       : 0.00
% 3.00/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
