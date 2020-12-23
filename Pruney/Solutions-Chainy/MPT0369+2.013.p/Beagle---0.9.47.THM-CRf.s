%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:52 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 188 expanded)
%              Number of leaves         :   32 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :  126 ( 430 expanded)
%              Number of equality atoms :   22 (  46 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_85,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_68,plain,(
    m1_subset_1('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_93,plain,(
    ! [B_46,A_47] :
      ( v1_xboole_0(B_46)
      | ~ m1_subset_1(B_46,A_47)
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_109,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_93])).

tff(c_110,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_52,plain,(
    ! [B_26,A_25] :
      ( r2_hidden(B_26,A_25)
      | ~ m1_subset_1(B_26,A_25)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_66,plain,(
    ~ r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_70,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_420,plain,(
    ! [A_86,B_87] :
      ( k4_xboole_0(A_86,B_87) = k3_subset_1(A_86,B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_444,plain,(
    k4_xboole_0('#skF_7','#skF_8') = k3_subset_1('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_420])).

tff(c_514,plain,(
    ! [D_92,A_93,B_94] :
      ( r2_hidden(D_92,k4_xboole_0(A_93,B_94))
      | r2_hidden(D_92,B_94)
      | ~ r2_hidden(D_92,A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_737,plain,(
    ! [D_108] :
      ( r2_hidden(D_108,k3_subset_1('#skF_7','#skF_8'))
      | r2_hidden(D_108,'#skF_8')
      | ~ r2_hidden(D_108,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_514])).

tff(c_64,plain,(
    ~ r2_hidden('#skF_9',k3_subset_1('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_758,plain,
    ( r2_hidden('#skF_9','#skF_8')
    | ~ r2_hidden('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_737,c_64])).

tff(c_769,plain,(
    ~ r2_hidden('#skF_9','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_758])).

tff(c_772,plain,
    ( ~ m1_subset_1('#skF_9','#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_769])).

tff(c_775,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_772])).

tff(c_777,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_775])).

tff(c_779,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_778,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_54,plain,(
    ! [B_26,A_25] :
      ( m1_subset_1(B_26,A_25)
      | ~ v1_xboole_0(B_26)
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_895,plain,(
    ! [B_134,A_135] :
      ( r2_hidden(B_134,A_135)
      | ~ m1_subset_1(B_134,A_135)
      | v1_xboole_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_933,plain,
    ( ~ m1_subset_1('#skF_9','#skF_8')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_895,c_66])).

tff(c_934,plain,(
    ~ m1_subset_1('#skF_9','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_933])).

tff(c_937,plain,
    ( ~ v1_xboole_0('#skF_9')
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_934])).

tff(c_940,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_937])).

tff(c_795,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_2'(A_114,B_115),A_114)
      | r1_tarski(A_114,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_809,plain,(
    ! [A_114,B_115] :
      ( ~ v1_xboole_0(A_114)
      | r1_tarski(A_114,B_115) ) ),
    inference(resolution,[status(thm)],[c_795,c_2])).

tff(c_868,plain,(
    ! [B_130,A_131] :
      ( B_130 = A_131
      | ~ r1_tarski(B_130,A_131)
      | ~ r1_tarski(A_131,B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_881,plain,(
    ! [B_132,A_133] :
      ( B_132 = A_133
      | ~ r1_tarski(B_132,A_133)
      | ~ v1_xboole_0(A_133) ) ),
    inference(resolution,[status(thm)],[c_809,c_868])).

tff(c_969,plain,(
    ! [B_137,A_138] :
      ( B_137 = A_138
      | ~ v1_xboole_0(B_137)
      | ~ v1_xboole_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_809,c_881])).

tff(c_976,plain,(
    ! [A_139] :
      ( A_139 = '#skF_7'
      | ~ v1_xboole_0(A_139) ) ),
    inference(resolution,[status(thm)],[c_779,c_969])).

tff(c_985,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_778,c_976])).

tff(c_1004,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_70])).

tff(c_60,plain,(
    ! [A_29] : ~ v1_xboole_0(k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_38,plain,(
    ! [C_24,A_20] :
      ( r1_tarski(C_24,A_20)
      | ~ r2_hidden(C_24,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_914,plain,(
    ! [B_134,A_20] :
      ( r1_tarski(B_134,A_20)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(A_20))
      | v1_xboole_0(k1_zfmisc_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_895,c_38])).

tff(c_1119,plain,(
    ! [B_149,A_150] :
      ( r1_tarski(B_149,A_150)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(A_150)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_914])).

tff(c_1142,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_1004,c_1119])).

tff(c_875,plain,(
    ! [B_115,A_114] :
      ( B_115 = A_114
      | ~ r1_tarski(B_115,A_114)
      | ~ v1_xboole_0(A_114) ) ),
    inference(resolution,[status(thm)],[c_809,c_868])).

tff(c_1159,plain,
    ( '#skF_9' = '#skF_8'
    | ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_1142,c_875])).

tff(c_1164,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_1159])).

tff(c_1208,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1164,c_778])).

tff(c_1212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_940,c_1208])).

tff(c_1213,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_933])).

tff(c_1249,plain,(
    ! [B_156,A_157] :
      ( B_156 = A_157
      | ~ v1_xboole_0(B_156)
      | ~ v1_xboole_0(A_157) ) ),
    inference(resolution,[status(thm)],[c_809,c_881])).

tff(c_1259,plain,(
    ! [A_158] :
      ( A_158 = '#skF_8'
      | ~ v1_xboole_0(A_158) ) ),
    inference(resolution,[status(thm)],[c_1213,c_1249])).

tff(c_1271,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_779,c_1259])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1292,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1271,c_72])).

tff(c_62,plain,(
    ! [A_30] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1417,plain,(
    ! [B_167,A_168] :
      ( r1_tarski(B_167,A_168)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(A_168)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_914])).

tff(c_1479,plain,(
    ! [A_172] : r1_tarski(k1_xboole_0,A_172) ),
    inference(resolution,[status(thm)],[c_62,c_1417])).

tff(c_1487,plain,(
    ! [A_173] :
      ( k1_xboole_0 = A_173
      | ~ v1_xboole_0(A_173) ) ),
    inference(resolution,[status(thm)],[c_1479,c_875])).

tff(c_1490,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1213,c_1487])).

tff(c_1494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1292,c_1490])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:53:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.56  
% 3.42/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.57  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_5
% 3.42/1.57  
% 3.42/1.57  %Foreground sorts:
% 3.42/1.57  
% 3.42/1.57  
% 3.42/1.57  %Background operators:
% 3.42/1.57  
% 3.42/1.57  
% 3.42/1.57  %Foreground operators:
% 3.42/1.57  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.42/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.42/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.42/1.57  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.42/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.42/1.57  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.42/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.42/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.42/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.42/1.57  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.42/1.57  tff('#skF_9', type, '#skF_9': $i).
% 3.42/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.42/1.57  tff('#skF_8', type, '#skF_8': $i).
% 3.42/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.57  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.42/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.42/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.42/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.42/1.57  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.42/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.42/1.57  
% 3.42/1.58  tff(f_100, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 3.42/1.58  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.42/1.58  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.42/1.58  tff(f_48, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.42/1.58  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.42/1.58  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.42/1.58  tff(f_54, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.42/1.58  tff(f_83, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.42/1.58  tff(f_63, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.42/1.58  tff(f_85, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.42/1.58  tff(c_68, plain, (m1_subset_1('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.42/1.58  tff(c_93, plain, (![B_46, A_47]: (v1_xboole_0(B_46) | ~m1_subset_1(B_46, A_47) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.42/1.58  tff(c_109, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_68, c_93])).
% 3.42/1.58  tff(c_110, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_109])).
% 3.42/1.58  tff(c_52, plain, (![B_26, A_25]: (r2_hidden(B_26, A_25) | ~m1_subset_1(B_26, A_25) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.42/1.58  tff(c_66, plain, (~r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.42/1.58  tff(c_70, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.42/1.58  tff(c_420, plain, (![A_86, B_87]: (k4_xboole_0(A_86, B_87)=k3_subset_1(A_86, B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.42/1.58  tff(c_444, plain, (k4_xboole_0('#skF_7', '#skF_8')=k3_subset_1('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_70, c_420])).
% 3.42/1.58  tff(c_514, plain, (![D_92, A_93, B_94]: (r2_hidden(D_92, k4_xboole_0(A_93, B_94)) | r2_hidden(D_92, B_94) | ~r2_hidden(D_92, A_93))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.42/1.58  tff(c_737, plain, (![D_108]: (r2_hidden(D_108, k3_subset_1('#skF_7', '#skF_8')) | r2_hidden(D_108, '#skF_8') | ~r2_hidden(D_108, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_444, c_514])).
% 3.42/1.58  tff(c_64, plain, (~r2_hidden('#skF_9', k3_subset_1('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.42/1.58  tff(c_758, plain, (r2_hidden('#skF_9', '#skF_8') | ~r2_hidden('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_737, c_64])).
% 3.42/1.58  tff(c_769, plain, (~r2_hidden('#skF_9', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_66, c_758])).
% 3.42/1.58  tff(c_772, plain, (~m1_subset_1('#skF_9', '#skF_7') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_52, c_769])).
% 3.42/1.58  tff(c_775, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_772])).
% 3.42/1.58  tff(c_777, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_775])).
% 3.42/1.58  tff(c_779, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_109])).
% 3.42/1.58  tff(c_778, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_109])).
% 3.42/1.58  tff(c_54, plain, (![B_26, A_25]: (m1_subset_1(B_26, A_25) | ~v1_xboole_0(B_26) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.42/1.58  tff(c_895, plain, (![B_134, A_135]: (r2_hidden(B_134, A_135) | ~m1_subset_1(B_134, A_135) | v1_xboole_0(A_135))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.42/1.58  tff(c_933, plain, (~m1_subset_1('#skF_9', '#skF_8') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_895, c_66])).
% 3.42/1.58  tff(c_934, plain, (~m1_subset_1('#skF_9', '#skF_8')), inference(splitLeft, [status(thm)], [c_933])).
% 3.42/1.58  tff(c_937, plain, (~v1_xboole_0('#skF_9') | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_54, c_934])).
% 3.42/1.58  tff(c_940, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_778, c_937])).
% 3.42/1.58  tff(c_795, plain, (![A_114, B_115]: (r2_hidden('#skF_2'(A_114, B_115), A_114) | r1_tarski(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.42/1.58  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.42/1.58  tff(c_809, plain, (![A_114, B_115]: (~v1_xboole_0(A_114) | r1_tarski(A_114, B_115))), inference(resolution, [status(thm)], [c_795, c_2])).
% 3.42/1.58  tff(c_868, plain, (![B_130, A_131]: (B_130=A_131 | ~r1_tarski(B_130, A_131) | ~r1_tarski(A_131, B_130))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.42/1.58  tff(c_881, plain, (![B_132, A_133]: (B_132=A_133 | ~r1_tarski(B_132, A_133) | ~v1_xboole_0(A_133))), inference(resolution, [status(thm)], [c_809, c_868])).
% 3.42/1.58  tff(c_969, plain, (![B_137, A_138]: (B_137=A_138 | ~v1_xboole_0(B_137) | ~v1_xboole_0(A_138))), inference(resolution, [status(thm)], [c_809, c_881])).
% 3.42/1.58  tff(c_976, plain, (![A_139]: (A_139='#skF_7' | ~v1_xboole_0(A_139))), inference(resolution, [status(thm)], [c_779, c_969])).
% 3.42/1.58  tff(c_985, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_778, c_976])).
% 3.42/1.58  tff(c_1004, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_985, c_70])).
% 3.42/1.58  tff(c_60, plain, (![A_29]: (~v1_xboole_0(k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.42/1.58  tff(c_38, plain, (![C_24, A_20]: (r1_tarski(C_24, A_20) | ~r2_hidden(C_24, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.42/1.58  tff(c_914, plain, (![B_134, A_20]: (r1_tarski(B_134, A_20) | ~m1_subset_1(B_134, k1_zfmisc_1(A_20)) | v1_xboole_0(k1_zfmisc_1(A_20)))), inference(resolution, [status(thm)], [c_895, c_38])).
% 3.42/1.58  tff(c_1119, plain, (![B_149, A_150]: (r1_tarski(B_149, A_150) | ~m1_subset_1(B_149, k1_zfmisc_1(A_150)))), inference(negUnitSimplification, [status(thm)], [c_60, c_914])).
% 3.42/1.58  tff(c_1142, plain, (r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_1004, c_1119])).
% 3.42/1.58  tff(c_875, plain, (![B_115, A_114]: (B_115=A_114 | ~r1_tarski(B_115, A_114) | ~v1_xboole_0(A_114))), inference(resolution, [status(thm)], [c_809, c_868])).
% 3.42/1.58  tff(c_1159, plain, ('#skF_9'='#skF_8' | ~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_1142, c_875])).
% 3.42/1.58  tff(c_1164, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_778, c_1159])).
% 3.42/1.58  tff(c_1208, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1164, c_778])).
% 3.42/1.58  tff(c_1212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_940, c_1208])).
% 3.42/1.58  tff(c_1213, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_933])).
% 3.42/1.58  tff(c_1249, plain, (![B_156, A_157]: (B_156=A_157 | ~v1_xboole_0(B_156) | ~v1_xboole_0(A_157))), inference(resolution, [status(thm)], [c_809, c_881])).
% 3.42/1.58  tff(c_1259, plain, (![A_158]: (A_158='#skF_8' | ~v1_xboole_0(A_158))), inference(resolution, [status(thm)], [c_1213, c_1249])).
% 3.42/1.58  tff(c_1271, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_779, c_1259])).
% 3.42/1.58  tff(c_72, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.42/1.58  tff(c_1292, plain, (k1_xboole_0!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1271, c_72])).
% 3.42/1.58  tff(c_62, plain, (![A_30]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.42/1.58  tff(c_1417, plain, (![B_167, A_168]: (r1_tarski(B_167, A_168) | ~m1_subset_1(B_167, k1_zfmisc_1(A_168)))), inference(negUnitSimplification, [status(thm)], [c_60, c_914])).
% 3.42/1.58  tff(c_1479, plain, (![A_172]: (r1_tarski(k1_xboole_0, A_172))), inference(resolution, [status(thm)], [c_62, c_1417])).
% 3.42/1.58  tff(c_1487, plain, (![A_173]: (k1_xboole_0=A_173 | ~v1_xboole_0(A_173))), inference(resolution, [status(thm)], [c_1479, c_875])).
% 3.42/1.58  tff(c_1490, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_1213, c_1487])).
% 3.42/1.58  tff(c_1494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1292, c_1490])).
% 3.42/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.58  
% 3.42/1.58  Inference rules
% 3.42/1.58  ----------------------
% 3.42/1.58  #Ref     : 0
% 3.42/1.58  #Sup     : 299
% 3.42/1.58  #Fact    : 0
% 3.42/1.58  #Define  : 0
% 3.42/1.58  #Split   : 9
% 3.42/1.58  #Chain   : 0
% 3.42/1.58  #Close   : 0
% 3.42/1.58  
% 3.42/1.58  Ordering : KBO
% 3.42/1.58  
% 3.42/1.58  Simplification rules
% 3.42/1.58  ----------------------
% 3.42/1.58  #Subsume      : 47
% 3.42/1.58  #Demod        : 83
% 3.42/1.58  #Tautology    : 90
% 3.42/1.58  #SimpNegUnit  : 42
% 3.42/1.58  #BackRed      : 31
% 3.42/1.58  
% 3.42/1.58  #Partial instantiations: 0
% 3.42/1.58  #Strategies tried      : 1
% 3.42/1.58  
% 3.42/1.58  Timing (in seconds)
% 3.42/1.58  ----------------------
% 3.42/1.58  Preprocessing        : 0.31
% 3.42/1.58  Parsing              : 0.15
% 3.42/1.58  CNF conversion       : 0.03
% 3.42/1.58  Main loop            : 0.44
% 3.42/1.58  Inferencing          : 0.16
% 3.42/1.58  Reduction            : 0.13
% 3.42/1.58  Demodulation         : 0.08
% 3.42/1.59  BG Simplification    : 0.02
% 3.42/1.59  Subsumption          : 0.09
% 3.42/1.59  Abstraction          : 0.02
% 3.42/1.59  MUC search           : 0.00
% 3.42/1.59  Cooper               : 0.00
% 3.42/1.59  Total                : 0.79
% 3.42/1.59  Index Insertion      : 0.00
% 3.42/1.59  Index Deletion       : 0.00
% 3.42/1.59  Index Matching       : 0.00
% 3.42/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
