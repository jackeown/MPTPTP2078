%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:46 EST 2020

% Result     : Theorem 5.55s
% Output     : CNFRefutation 5.63s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 448 expanded)
%              Number of leaves         :   33 ( 166 expanded)
%              Depth                    :   14
%              Number of atoms          :  201 (1404 expanded)
%              Number of equality atoms :   68 ( 381 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
         => ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(c_38,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_42,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_92,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_105,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_92])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_46,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_743,plain,(
    ! [D_106,C_107,B_108,A_109] :
      ( k1_funct_1(k2_funct_1(D_106),k1_funct_1(D_106,C_107)) = C_107
      | k1_xboole_0 = B_108
      | ~ r2_hidden(C_107,A_109)
      | ~ v2_funct_1(D_106)
      | ~ m1_subset_1(D_106,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108)))
      | ~ v1_funct_2(D_106,A_109,B_108)
      | ~ v1_funct_1(D_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_828,plain,(
    ! [D_112,B_113] :
      ( k1_funct_1(k2_funct_1(D_112),k1_funct_1(D_112,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_113
      | ~ v2_funct_1(D_112)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_113)))
      | ~ v1_funct_2(D_112,'#skF_3',B_113)
      | ~ v1_funct_1(D_112) ) ),
    inference(resolution,[status(thm)],[c_42,c_743])).

tff(c_839,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_828])).

tff(c_848,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_839])).

tff(c_1021,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_848])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1041,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1021,c_8])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1039,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1021,c_1021,c_14])).

tff(c_83,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_83])).

tff(c_163,plain,(
    ! [B_50,A_51] :
      ( B_50 = A_51
      | ~ r1_tarski(B_50,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_170,plain,
    ( k2_zfmisc_1('#skF_3','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_91,c_163])).

tff(c_189,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_1088,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1039,c_189])).

tff(c_1093,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_1088])).

tff(c_1095,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_848])).

tff(c_1094,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_848])).

tff(c_40,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_44,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_970,plain,(
    ! [D_121,B_122] :
      ( k1_funct_1(k2_funct_1(D_121),k1_funct_1(D_121,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_122
      | ~ v2_funct_1(D_121)
      | ~ m1_subset_1(D_121,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_122)))
      | ~ v1_funct_2(D_121,'#skF_3',B_122)
      | ~ v1_funct_1(D_121) ) ),
    inference(resolution,[status(thm)],[c_44,c_743])).

tff(c_981,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_970])).

tff(c_990,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_40,c_981])).

tff(c_1104,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1094,c_990])).

tff(c_1105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1095,c_38,c_1104])).

tff(c_1106,plain,(
    k2_zfmisc_1('#skF_3','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_1109,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1106,c_48])).

tff(c_1588,plain,(
    ! [D_167,C_168,B_169,A_170] :
      ( k1_funct_1(k2_funct_1(D_167),k1_funct_1(D_167,C_168)) = C_168
      | k1_xboole_0 = B_169
      | ~ r2_hidden(C_168,A_170)
      | ~ v2_funct_1(D_167)
      | ~ m1_subset_1(D_167,k1_zfmisc_1(k2_zfmisc_1(A_170,B_169)))
      | ~ v1_funct_2(D_167,A_170,B_169)
      | ~ v1_funct_1(D_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1837,plain,(
    ! [D_196,B_197] :
      ( k1_funct_1(k2_funct_1(D_196),k1_funct_1(D_196,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_197
      | ~ v2_funct_1(D_196)
      | ~ m1_subset_1(D_196,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_197)))
      | ~ v1_funct_2(D_196,'#skF_3',B_197)
      | ~ v1_funct_1(D_196) ) ),
    inference(resolution,[status(thm)],[c_44,c_1588])).

tff(c_1845,plain,(
    ! [D_196] :
      ( k1_funct_1(k2_funct_1(D_196),k1_funct_1(D_196,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = '#skF_3'
      | ~ v2_funct_1(D_196)
      | ~ m1_subset_1(D_196,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(D_196,'#skF_3','#skF_3')
      | ~ v1_funct_1(D_196) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1106,c_1837])).

tff(c_2156,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1845])).

tff(c_2185,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2156,c_8])).

tff(c_1159,plain,(
    ! [A_135,B_136,C_137] :
      ( k1_relset_1(A_135,B_136,C_137) = k1_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1247,plain,(
    ! [C_150] :
      ( k1_relset_1('#skF_3','#skF_3',C_150) = k1_relat_1(C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1106,c_1159])).

tff(c_1260,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1109,c_1247])).

tff(c_32,plain,(
    ! [A_18,B_19,C_20] :
      ( m1_subset_1(k1_relset_1(A_18,B_19,C_20),k1_zfmisc_1(A_18))
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1265,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1260,c_32])).

tff(c_1269,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1109,c_1106,c_1265])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1274,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1269,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1277,plain,
    ( k1_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1274,c_2])).

tff(c_1278,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1277])).

tff(c_2192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2185,c_1278])).

tff(c_4857,plain,(
    ! [D_349] :
      ( k1_funct_1(k2_funct_1(D_349),k1_funct_1(D_349,'#skF_5')) = '#skF_5'
      | ~ v2_funct_1(D_349)
      | ~ m1_subset_1(D_349,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(D_349,'#skF_3','#skF_3')
      | ~ v1_funct_1(D_349) ) ),
    inference(splitRight,[status(thm)],[c_1845])).

tff(c_4882,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5'
    | ~ v2_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4857])).

tff(c_4890,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1109,c_46,c_4882])).

tff(c_2194,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1845])).

tff(c_1663,plain,(
    ! [D_178,B_179] :
      ( k1_funct_1(k2_funct_1(D_178),k1_funct_1(D_178,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_179
      | ~ v2_funct_1(D_178)
      | ~ m1_subset_1(D_178,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_179)))
      | ~ v1_funct_2(D_178,'#skF_3',B_179)
      | ~ v1_funct_1(D_178) ) ),
    inference(resolution,[status(thm)],[c_42,c_1588])).

tff(c_1671,plain,(
    ! [D_178] :
      ( k1_funct_1(k2_funct_1(D_178),k1_funct_1(D_178,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = '#skF_3'
      | ~ v2_funct_1(D_178)
      | ~ m1_subset_1(D_178,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(D_178,'#skF_3','#skF_3')
      | ~ v1_funct_1(D_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1106,c_1663])).

tff(c_2241,plain,(
    ! [D_178] :
      ( k1_funct_1(k2_funct_1(D_178),k1_funct_1(D_178,'#skF_6')) = '#skF_6'
      | ~ v2_funct_1(D_178)
      | ~ m1_subset_1(D_178,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(D_178,'#skF_3','#skF_3')
      | ~ v1_funct_1(D_178) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2194,c_1671])).

tff(c_4894,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v2_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4890,c_2241])).

tff(c_4905,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1109,c_46,c_4894])).

tff(c_4907,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_4905])).

tff(c_4908,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1277])).

tff(c_5067,plain,(
    ! [C_353,B_354,A_355] :
      ( C_353 = B_354
      | k1_funct_1(A_355,C_353) != k1_funct_1(A_355,B_354)
      | ~ r2_hidden(C_353,k1_relat_1(A_355))
      | ~ r2_hidden(B_354,k1_relat_1(A_355))
      | ~ v2_funct_1(A_355)
      | ~ v1_funct_1(A_355)
      | ~ v1_relat_1(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5073,plain,(
    ! [B_354] :
      ( B_354 = '#skF_5'
      | k1_funct_1('#skF_4',B_354) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ r2_hidden(B_354,k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_5067])).

tff(c_5091,plain,(
    ! [B_356] :
      ( B_356 = '#skF_5'
      | k1_funct_1('#skF_4',B_356) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(B_356,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_52,c_46,c_4908,c_44,c_4908,c_5073])).

tff(c_5094,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42,c_5091])).

tff(c_5101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_5094])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n024.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 18:20:36 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.55/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.55/2.08  
% 5.55/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.55/2.08  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 5.55/2.08  
% 5.55/2.08  %Foreground sorts:
% 5.55/2.08  
% 5.55/2.08  
% 5.55/2.08  %Background operators:
% 5.55/2.08  
% 5.55/2.08  
% 5.55/2.08  %Foreground operators:
% 5.55/2.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.55/2.08  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.55/2.08  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.55/2.08  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.55/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.55/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.55/2.08  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.55/2.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.55/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.55/2.08  tff('#skF_5', type, '#skF_5': $i).
% 5.55/2.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.55/2.08  tff('#skF_6', type, '#skF_6': $i).
% 5.55/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.55/2.08  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.55/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.55/2.08  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.55/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.55/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.55/2.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.55/2.08  tff('#skF_4', type, '#skF_4': $i).
% 5.55/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.55/2.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.55/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.55/2.08  
% 5.63/2.10  tff(f_102, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 5.63/2.10  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.63/2.10  tff(f_84, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 5.63/2.10  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.63/2.10  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.63/2.10  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.63/2.10  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.63/2.10  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.63/2.10  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 5.63/2.10  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 5.63/2.10  tff(c_38, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.63/2.10  tff(c_42, plain, (r2_hidden('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.63/2.10  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.63/2.10  tff(c_92, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.63/2.10  tff(c_105, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_92])).
% 5.63/2.10  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.63/2.10  tff(c_46, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.63/2.10  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.63/2.10  tff(c_743, plain, (![D_106, C_107, B_108, A_109]: (k1_funct_1(k2_funct_1(D_106), k1_funct_1(D_106, C_107))=C_107 | k1_xboole_0=B_108 | ~r2_hidden(C_107, A_109) | ~v2_funct_1(D_106) | ~m1_subset_1(D_106, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))) | ~v1_funct_2(D_106, A_109, B_108) | ~v1_funct_1(D_106))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.63/2.10  tff(c_828, plain, (![D_112, B_113]: (k1_funct_1(k2_funct_1(D_112), k1_funct_1(D_112, '#skF_6'))='#skF_6' | k1_xboole_0=B_113 | ~v2_funct_1(D_112) | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_113))) | ~v1_funct_2(D_112, '#skF_3', B_113) | ~v1_funct_1(D_112))), inference(resolution, [status(thm)], [c_42, c_743])).
% 5.63/2.10  tff(c_839, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_828])).
% 5.63/2.10  tff(c_848, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_839])).
% 5.63/2.10  tff(c_1021, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_848])).
% 5.63/2.10  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.63/2.10  tff(c_1041, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1021, c_8])).
% 5.63/2.10  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.63/2.10  tff(c_1039, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1021, c_1021, c_14])).
% 5.63/2.10  tff(c_83, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.63/2.10  tff(c_91, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_83])).
% 5.63/2.10  tff(c_163, plain, (![B_50, A_51]: (B_50=A_51 | ~r1_tarski(B_50, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.63/2.10  tff(c_170, plain, (k2_zfmisc_1('#skF_3', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_91, c_163])).
% 5.63/2.10  tff(c_189, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_170])).
% 5.63/2.10  tff(c_1088, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1039, c_189])).
% 5.63/2.10  tff(c_1093, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1041, c_1088])).
% 5.63/2.10  tff(c_1095, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_848])).
% 5.63/2.10  tff(c_1094, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_848])).
% 5.63/2.10  tff(c_40, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.63/2.10  tff(c_44, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.63/2.10  tff(c_970, plain, (![D_121, B_122]: (k1_funct_1(k2_funct_1(D_121), k1_funct_1(D_121, '#skF_5'))='#skF_5' | k1_xboole_0=B_122 | ~v2_funct_1(D_121) | ~m1_subset_1(D_121, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_122))) | ~v1_funct_2(D_121, '#skF_3', B_122) | ~v1_funct_1(D_121))), inference(resolution, [status(thm)], [c_44, c_743])).
% 5.63/2.10  tff(c_981, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_970])).
% 5.63/2.10  tff(c_990, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_40, c_981])).
% 5.63/2.10  tff(c_1104, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1094, c_990])).
% 5.63/2.10  tff(c_1105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1095, c_38, c_1104])).
% 5.63/2.10  tff(c_1106, plain, (k2_zfmisc_1('#skF_3', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_170])).
% 5.63/2.10  tff(c_1109, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1106, c_48])).
% 5.63/2.10  tff(c_1588, plain, (![D_167, C_168, B_169, A_170]: (k1_funct_1(k2_funct_1(D_167), k1_funct_1(D_167, C_168))=C_168 | k1_xboole_0=B_169 | ~r2_hidden(C_168, A_170) | ~v2_funct_1(D_167) | ~m1_subset_1(D_167, k1_zfmisc_1(k2_zfmisc_1(A_170, B_169))) | ~v1_funct_2(D_167, A_170, B_169) | ~v1_funct_1(D_167))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.63/2.10  tff(c_1837, plain, (![D_196, B_197]: (k1_funct_1(k2_funct_1(D_196), k1_funct_1(D_196, '#skF_5'))='#skF_5' | k1_xboole_0=B_197 | ~v2_funct_1(D_196) | ~m1_subset_1(D_196, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_197))) | ~v1_funct_2(D_196, '#skF_3', B_197) | ~v1_funct_1(D_196))), inference(resolution, [status(thm)], [c_44, c_1588])).
% 5.63/2.10  tff(c_1845, plain, (![D_196]: (k1_funct_1(k2_funct_1(D_196), k1_funct_1(D_196, '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1(D_196) | ~m1_subset_1(D_196, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(D_196, '#skF_3', '#skF_3') | ~v1_funct_1(D_196))), inference(superposition, [status(thm), theory('equality')], [c_1106, c_1837])).
% 5.63/2.10  tff(c_2156, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1845])).
% 5.63/2.10  tff(c_2185, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2156, c_8])).
% 5.63/2.10  tff(c_1159, plain, (![A_135, B_136, C_137]: (k1_relset_1(A_135, B_136, C_137)=k1_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.63/2.10  tff(c_1247, plain, (![C_150]: (k1_relset_1('#skF_3', '#skF_3', C_150)=k1_relat_1(C_150) | ~m1_subset_1(C_150, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1106, c_1159])).
% 5.63/2.10  tff(c_1260, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1109, c_1247])).
% 5.63/2.10  tff(c_32, plain, (![A_18, B_19, C_20]: (m1_subset_1(k1_relset_1(A_18, B_19, C_20), k1_zfmisc_1(A_18)) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.63/2.10  tff(c_1265, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1260, c_32])).
% 5.63/2.10  tff(c_1269, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1109, c_1106, c_1265])).
% 5.63/2.10  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.63/2.10  tff(c_1274, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1269, c_16])).
% 5.63/2.10  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.63/2.10  tff(c_1277, plain, (k1_relat_1('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1274, c_2])).
% 5.63/2.10  tff(c_1278, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1277])).
% 5.63/2.10  tff(c_2192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2185, c_1278])).
% 5.63/2.10  tff(c_4857, plain, (![D_349]: (k1_funct_1(k2_funct_1(D_349), k1_funct_1(D_349, '#skF_5'))='#skF_5' | ~v2_funct_1(D_349) | ~m1_subset_1(D_349, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(D_349, '#skF_3', '#skF_3') | ~v1_funct_1(D_349))), inference(splitRight, [status(thm)], [c_1845])).
% 5.63/2.10  tff(c_4882, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5' | ~v2_funct_1('#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_40, c_4857])).
% 5.63/2.10  tff(c_4890, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1109, c_46, c_4882])).
% 5.63/2.10  tff(c_2194, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1845])).
% 5.63/2.10  tff(c_1663, plain, (![D_178, B_179]: (k1_funct_1(k2_funct_1(D_178), k1_funct_1(D_178, '#skF_6'))='#skF_6' | k1_xboole_0=B_179 | ~v2_funct_1(D_178) | ~m1_subset_1(D_178, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_179))) | ~v1_funct_2(D_178, '#skF_3', B_179) | ~v1_funct_1(D_178))), inference(resolution, [status(thm)], [c_42, c_1588])).
% 5.63/2.10  tff(c_1671, plain, (![D_178]: (k1_funct_1(k2_funct_1(D_178), k1_funct_1(D_178, '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1(D_178) | ~m1_subset_1(D_178, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(D_178, '#skF_3', '#skF_3') | ~v1_funct_1(D_178))), inference(superposition, [status(thm), theory('equality')], [c_1106, c_1663])).
% 5.63/2.10  tff(c_2241, plain, (![D_178]: (k1_funct_1(k2_funct_1(D_178), k1_funct_1(D_178, '#skF_6'))='#skF_6' | ~v2_funct_1(D_178) | ~m1_subset_1(D_178, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(D_178, '#skF_3', '#skF_3') | ~v1_funct_1(D_178))), inference(negUnitSimplification, [status(thm)], [c_2194, c_1671])).
% 5.63/2.10  tff(c_4894, plain, ('#skF_5'='#skF_6' | ~v2_funct_1('#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4890, c_2241])).
% 5.63/2.10  tff(c_4905, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1109, c_46, c_4894])).
% 5.63/2.10  tff(c_4907, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_4905])).
% 5.63/2.10  tff(c_4908, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1277])).
% 5.63/2.10  tff(c_5067, plain, (![C_353, B_354, A_355]: (C_353=B_354 | k1_funct_1(A_355, C_353)!=k1_funct_1(A_355, B_354) | ~r2_hidden(C_353, k1_relat_1(A_355)) | ~r2_hidden(B_354, k1_relat_1(A_355)) | ~v2_funct_1(A_355) | ~v1_funct_1(A_355) | ~v1_relat_1(A_355))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.63/2.10  tff(c_5073, plain, (![B_354]: (B_354='#skF_5' | k1_funct_1('#skF_4', B_354)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~r2_hidden(B_354, k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_5067])).
% 5.63/2.10  tff(c_5091, plain, (![B_356]: (B_356='#skF_5' | k1_funct_1('#skF_4', B_356)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(B_356, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_52, c_46, c_4908, c_44, c_4908, c_5073])).
% 5.63/2.10  tff(c_5094, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_42, c_5091])).
% 5.63/2.10  tff(c_5101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_5094])).
% 5.63/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.63/2.10  
% 5.63/2.10  Inference rules
% 5.63/2.10  ----------------------
% 5.63/2.10  #Ref     : 4
% 5.63/2.10  #Sup     : 1080
% 5.63/2.10  #Fact    : 0
% 5.63/2.10  #Define  : 0
% 5.63/2.10  #Split   : 16
% 5.63/2.10  #Chain   : 0
% 5.63/2.10  #Close   : 0
% 5.63/2.10  
% 5.63/2.10  Ordering : KBO
% 5.63/2.10  
% 5.63/2.10  Simplification rules
% 5.63/2.10  ----------------------
% 5.63/2.10  #Subsume      : 134
% 5.63/2.10  #Demod        : 1869
% 5.63/2.10  #Tautology    : 531
% 5.63/2.10  #SimpNegUnit  : 18
% 5.63/2.10  #BackRed      : 104
% 5.63/2.10  
% 5.63/2.10  #Partial instantiations: 0
% 5.63/2.10  #Strategies tried      : 1
% 5.63/2.10  
% 5.63/2.10  Timing (in seconds)
% 5.63/2.10  ----------------------
% 5.63/2.10  Preprocessing        : 0.32
% 5.63/2.10  Parsing              : 0.17
% 5.63/2.10  CNF conversion       : 0.02
% 5.63/2.10  Main loop            : 1.02
% 5.63/2.10  Inferencing          : 0.32
% 5.63/2.10  Reduction            : 0.38
% 5.63/2.10  Demodulation         : 0.29
% 5.63/2.10  BG Simplification    : 0.04
% 5.63/2.10  Subsumption          : 0.20
% 5.63/2.10  Abstraction          : 0.05
% 5.63/2.10  MUC search           : 0.00
% 5.63/2.10  Cooper               : 0.00
% 5.63/2.10  Total                : 1.37
% 5.63/2.10  Index Insertion      : 0.00
% 5.63/2.10  Index Deletion       : 0.00
% 5.63/2.10  Index Matching       : 0.00
% 5.63/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
