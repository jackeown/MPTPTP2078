%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:45 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 235 expanded)
%              Number of leaves         :   40 (  95 expanded)
%              Depth                    :   11
%              Number of atoms          :  126 ( 461 expanded)
%              Number of equality atoms :   51 ( 156 expanded)
%              Maximal formula depth    :    9 (   3 average)
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

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_94,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_68,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_49,axiom,(
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

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_136,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_149,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_136])).

tff(c_32,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k9_relat_1(B_20,A_19),k2_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,(
    ! [A_21] :
      ( k1_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_158,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_149,c_40])).

tff(c_208,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_662,plain,(
    ! [B_135,A_136] :
      ( k1_tarski(k1_funct_1(B_135,A_136)) = k2_relat_1(B_135)
      | k1_tarski(A_136) != k1_relat_1(B_135)
      | ~ v1_funct_1(B_135)
      | ~ v1_relat_1(B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_559,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k7_relset_1(A_112,B_113,C_114,D_115) = k9_relat_1(C_114,D_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_571,plain,(
    ! [D_115] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_115) = k9_relat_1('#skF_4',D_115) ),
    inference(resolution,[status(thm)],[c_56,c_559])).

tff(c_52,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_602,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_52])).

tff(c_668,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_602])).

tff(c_677,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_60,c_668])).

tff(c_714,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_677])).

tff(c_334,plain,(
    ! [C_79,A_80,B_81] :
      ( v4_relat_1(C_79,A_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_347,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_334])).

tff(c_301,plain,(
    ! [B_77,A_78] :
      ( r1_tarski(k1_relat_1(B_77),A_78)
      | ~ v4_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( k1_tarski(B_10) = A_9
      | k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_tarski(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_998,plain,(
    ! [B_178,B_179] :
      ( k1_tarski(B_178) = k1_relat_1(B_179)
      | k1_relat_1(B_179) = k1_xboole_0
      | ~ v4_relat_1(B_179,k1_tarski(B_178))
      | ~ v1_relat_1(B_179) ) ),
    inference(resolution,[status(thm)],[c_301,c_14])).

tff(c_1020,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_347,c_998])).

tff(c_1037,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_1020])).

tff(c_1039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_714,c_1037])).

tff(c_1040,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_677])).

tff(c_1102,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_1040])).

tff(c_1106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_1102])).

tff(c_1107,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1117,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1107,c_1107,c_34])).

tff(c_38,plain,(
    ! [A_21] :
      ( k2_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_157,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_149,c_38])).

tff(c_173,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_1110,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1107,c_173])).

tff(c_1155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1117,c_1110])).

tff(c_1156,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_20,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_83,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_91,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(resolution,[status(thm)],[c_20,c_83])).

tff(c_1162,plain,(
    ! [A_11] : r1_tarski('#skF_4',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1156,c_91])).

tff(c_1157,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_1172,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1156,c_1157])).

tff(c_1182,plain,(
    ! [B_184,A_185] :
      ( r1_tarski(k9_relat_1(B_184,A_185),k2_relat_1(B_184))
      | ~ v1_relat_1(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1187,plain,(
    ! [A_185] :
      ( r1_tarski(k9_relat_1('#skF_4',A_185),'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1172,c_1182])).

tff(c_1224,plain,(
    ! [A_188] : r1_tarski(k9_relat_1('#skF_4',A_188),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_1187])).

tff(c_110,plain,(
    ! [B_47,A_48] :
      ( B_47 = A_48
      | ~ r1_tarski(B_47,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_91,c_110])).

tff(c_1159,plain,(
    ! [A_11] :
      ( A_11 = '#skF_4'
      | ~ r1_tarski(A_11,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1156,c_1156,c_118])).

tff(c_1230,plain,(
    ! [A_188] : k9_relat_1('#skF_4',A_188) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1224,c_1159])).

tff(c_1163,plain,(
    ! [A_11] : m1_subset_1('#skF_4',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1156,c_20])).

tff(c_1564,plain,(
    ! [A_246,B_247,C_248,D_249] :
      ( k7_relset_1(A_246,B_247,C_248,D_249) = k9_relat_1(C_248,D_249)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1569,plain,(
    ! [A_246,B_247,D_249] : k7_relset_1(A_246,B_247,'#skF_4',D_249) = k9_relat_1('#skF_4',D_249) ),
    inference(resolution,[status(thm)],[c_1163,c_1564])).

tff(c_1574,plain,(
    ! [A_246,B_247,D_249] : k7_relset_1(A_246,B_247,'#skF_4',D_249) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1230,c_1569])).

tff(c_1576,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1574,c_52])).

tff(c_1579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1162,c_1576])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:15:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.62  
% 3.48/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.62  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.48/1.62  
% 3.48/1.62  %Foreground sorts:
% 3.48/1.62  
% 3.48/1.62  
% 3.48/1.62  %Background operators:
% 3.48/1.62  
% 3.48/1.62  
% 3.48/1.62  %Foreground operators:
% 3.48/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.48/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.48/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.48/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.48/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.48/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.48/1.62  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.48/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.48/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.48/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.48/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.48/1.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.48/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.48/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.48/1.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.48/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.48/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.48/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.48/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.48/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.48/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.48/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.48/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.48/1.62  
% 3.48/1.64  tff(f_110, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.48/1.64  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.48/1.64  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.48/1.64  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.48/1.64  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.48/1.64  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.48/1.64  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.48/1.64  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.48/1.64  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.48/1.64  tff(f_68, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.48/1.64  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.48/1.64  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.48/1.64  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.48/1.64  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.48/1.64  tff(c_136, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.48/1.64  tff(c_149, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_136])).
% 3.48/1.64  tff(c_32, plain, (![B_20, A_19]: (r1_tarski(k9_relat_1(B_20, A_19), k2_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.48/1.64  tff(c_40, plain, (![A_21]: (k1_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.48/1.64  tff(c_158, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_149, c_40])).
% 3.48/1.64  tff(c_208, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_158])).
% 3.48/1.64  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.48/1.64  tff(c_662, plain, (![B_135, A_136]: (k1_tarski(k1_funct_1(B_135, A_136))=k2_relat_1(B_135) | k1_tarski(A_136)!=k1_relat_1(B_135) | ~v1_funct_1(B_135) | ~v1_relat_1(B_135))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.48/1.64  tff(c_559, plain, (![A_112, B_113, C_114, D_115]: (k7_relset_1(A_112, B_113, C_114, D_115)=k9_relat_1(C_114, D_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.48/1.64  tff(c_571, plain, (![D_115]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_115)=k9_relat_1('#skF_4', D_115))), inference(resolution, [status(thm)], [c_56, c_559])).
% 3.48/1.64  tff(c_52, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.48/1.64  tff(c_602, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_571, c_52])).
% 3.48/1.64  tff(c_668, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_662, c_602])).
% 3.48/1.64  tff(c_677, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_60, c_668])).
% 3.48/1.64  tff(c_714, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_677])).
% 3.48/1.64  tff(c_334, plain, (![C_79, A_80, B_81]: (v4_relat_1(C_79, A_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.48/1.64  tff(c_347, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_334])).
% 3.48/1.64  tff(c_301, plain, (![B_77, A_78]: (r1_tarski(k1_relat_1(B_77), A_78) | ~v4_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.48/1.64  tff(c_14, plain, (![B_10, A_9]: (k1_tarski(B_10)=A_9 | k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_tarski(B_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.48/1.64  tff(c_998, plain, (![B_178, B_179]: (k1_tarski(B_178)=k1_relat_1(B_179) | k1_relat_1(B_179)=k1_xboole_0 | ~v4_relat_1(B_179, k1_tarski(B_178)) | ~v1_relat_1(B_179))), inference(resolution, [status(thm)], [c_301, c_14])).
% 3.48/1.64  tff(c_1020, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_347, c_998])).
% 3.48/1.64  tff(c_1037, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_149, c_1020])).
% 3.48/1.64  tff(c_1039, plain, $false, inference(negUnitSimplification, [status(thm)], [c_208, c_714, c_1037])).
% 3.48/1.64  tff(c_1040, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_677])).
% 3.48/1.64  tff(c_1102, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_1040])).
% 3.48/1.64  tff(c_1106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149, c_1102])).
% 3.48/1.64  tff(c_1107, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_158])).
% 3.48/1.64  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.48/1.64  tff(c_1117, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1107, c_1107, c_34])).
% 3.48/1.64  tff(c_38, plain, (![A_21]: (k2_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.48/1.64  tff(c_157, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_149, c_38])).
% 3.48/1.64  tff(c_173, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_157])).
% 3.48/1.64  tff(c_1110, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1107, c_173])).
% 3.48/1.64  tff(c_1155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1117, c_1110])).
% 3.48/1.64  tff(c_1156, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_157])).
% 3.48/1.64  tff(c_20, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.48/1.64  tff(c_83, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.48/1.64  tff(c_91, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(resolution, [status(thm)], [c_20, c_83])).
% 3.48/1.64  tff(c_1162, plain, (![A_11]: (r1_tarski('#skF_4', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_1156, c_91])).
% 3.48/1.64  tff(c_1157, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_157])).
% 3.48/1.64  tff(c_1172, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1156, c_1157])).
% 3.48/1.64  tff(c_1182, plain, (![B_184, A_185]: (r1_tarski(k9_relat_1(B_184, A_185), k2_relat_1(B_184)) | ~v1_relat_1(B_184))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.48/1.64  tff(c_1187, plain, (![A_185]: (r1_tarski(k9_relat_1('#skF_4', A_185), '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1172, c_1182])).
% 3.48/1.64  tff(c_1224, plain, (![A_188]: (r1_tarski(k9_relat_1('#skF_4', A_188), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_1187])).
% 3.48/1.64  tff(c_110, plain, (![B_47, A_48]: (B_47=A_48 | ~r1_tarski(B_47, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.48/1.64  tff(c_118, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(resolution, [status(thm)], [c_91, c_110])).
% 3.48/1.64  tff(c_1159, plain, (![A_11]: (A_11='#skF_4' | ~r1_tarski(A_11, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1156, c_1156, c_118])).
% 3.48/1.64  tff(c_1230, plain, (![A_188]: (k9_relat_1('#skF_4', A_188)='#skF_4')), inference(resolution, [status(thm)], [c_1224, c_1159])).
% 3.48/1.64  tff(c_1163, plain, (![A_11]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_1156, c_20])).
% 3.48/1.64  tff(c_1564, plain, (![A_246, B_247, C_248, D_249]: (k7_relset_1(A_246, B_247, C_248, D_249)=k9_relat_1(C_248, D_249) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.48/1.64  tff(c_1569, plain, (![A_246, B_247, D_249]: (k7_relset_1(A_246, B_247, '#skF_4', D_249)=k9_relat_1('#skF_4', D_249))), inference(resolution, [status(thm)], [c_1163, c_1564])).
% 3.48/1.64  tff(c_1574, plain, (![A_246, B_247, D_249]: (k7_relset_1(A_246, B_247, '#skF_4', D_249)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1230, c_1569])).
% 3.48/1.64  tff(c_1576, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1574, c_52])).
% 3.48/1.64  tff(c_1579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1162, c_1576])).
% 3.48/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.64  
% 3.48/1.64  Inference rules
% 3.48/1.64  ----------------------
% 3.48/1.64  #Ref     : 0
% 3.48/1.64  #Sup     : 302
% 3.48/1.64  #Fact    : 0
% 3.48/1.64  #Define  : 0
% 3.48/1.64  #Split   : 5
% 3.48/1.64  #Chain   : 0
% 3.48/1.64  #Close   : 0
% 3.48/1.64  
% 3.48/1.64  Ordering : KBO
% 3.48/1.64  
% 3.48/1.64  Simplification rules
% 3.48/1.64  ----------------------
% 3.48/1.64  #Subsume      : 19
% 3.48/1.64  #Demod        : 303
% 3.48/1.64  #Tautology    : 171
% 3.48/1.64  #SimpNegUnit  : 1
% 3.48/1.64  #BackRed      : 35
% 3.48/1.64  
% 3.48/1.64  #Partial instantiations: 0
% 3.48/1.64  #Strategies tried      : 1
% 3.48/1.64  
% 3.48/1.64  Timing (in seconds)
% 3.48/1.64  ----------------------
% 3.48/1.64  Preprocessing        : 0.32
% 3.48/1.64  Parsing              : 0.17
% 3.48/1.64  CNF conversion       : 0.02
% 3.48/1.64  Main loop            : 0.46
% 3.48/1.64  Inferencing          : 0.16
% 3.48/1.64  Reduction            : 0.16
% 3.48/1.64  Demodulation         : 0.11
% 3.48/1.64  BG Simplification    : 0.02
% 3.48/1.64  Subsumption          : 0.08
% 3.48/1.64  Abstraction          : 0.02
% 3.48/1.64  MUC search           : 0.00
% 3.48/1.64  Cooper               : 0.00
% 3.48/1.64  Total                : 0.82
% 3.48/1.64  Index Insertion      : 0.00
% 3.48/1.64  Index Deletion       : 0.00
% 3.48/1.64  Index Matching       : 0.00
% 3.48/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
