%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:23 EST 2020

% Result     : Theorem 5.92s
% Output     : CNFRefutation 5.92s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 137 expanded)
%              Number of leaves         :   35 (  64 expanded)
%              Depth                    :    8
%              Number of atoms          :  105 ( 258 expanded)
%              Number of equality atoms :   27 (  73 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_14,plain,(
    ! [C_14] : r2_hidden(C_14,k1_tarski(C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_134,plain,(
    ! [B_49,A_50] :
      ( ~ r1_tarski(B_49,A_50)
      | ~ r2_hidden(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_149,plain,(
    ! [C_14] : ~ r1_tarski(k1_tarski(C_14),C_14) ),
    inference(resolution,[status(thm)],[c_14,c_134])).

tff(c_113,plain,(
    ! [B_44,A_45] :
      ( ~ r2_hidden(B_44,A_45)
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [C_14] : ~ v1_xboole_0(k1_tarski(C_14)) ),
    inference(resolution,[status(thm)],[c_14,c_113])).

tff(c_166,plain,(
    ! [A_58] :
      ( v1_xboole_0(A_58)
      | r2_hidden('#skF_1'(A_58),A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_170,plain,(
    ! [A_10] :
      ( '#skF_1'(k1_tarski(A_10)) = A_10
      | v1_xboole_0(k1_tarski(A_10)) ) ),
    inference(resolution,[status(thm)],[c_166,c_12])).

tff(c_179,plain,(
    ! [A_10] : '#skF_1'(k1_tarski(A_10)) = A_10 ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_170])).

tff(c_210,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_2'(A_63,B_64),A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_460,plain,(
    ! [A_111,B_112] :
      ( '#skF_2'(k1_tarski(A_111),B_112) = A_111
      | r1_tarski(k1_tarski(A_111),B_112) ) ),
    inference(resolution,[status(thm)],[c_210,c_12])).

tff(c_58,plain,(
    ! [B_31,A_30] :
      ( ~ r1_tarski(B_31,A_30)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_180,plain,(
    ! [A_58] :
      ( ~ r1_tarski(A_58,'#skF_1'(A_58))
      | v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_166,c_58])).

tff(c_479,plain,(
    ! [A_111] :
      ( v1_xboole_0(k1_tarski(A_111))
      | '#skF_2'(k1_tarski(A_111),'#skF_1'(k1_tarski(A_111))) = A_111 ) ),
    inference(resolution,[status(thm)],[c_460,c_180])).

tff(c_492,plain,(
    ! [A_111] :
      ( v1_xboole_0(k1_tarski(A_111))
      | '#skF_2'(k1_tarski(A_111),A_111) = A_111 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_479])).

tff(c_503,plain,(
    ! [A_115] : '#skF_2'(k1_tarski(A_115),A_115) = A_115 ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_492])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_512,plain,(
    ! [A_115] :
      ( ~ r2_hidden(A_115,A_115)
      | r1_tarski(k1_tarski(A_115),A_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_8])).

tff(c_521,plain,(
    ! [A_115] : ~ r2_hidden(A_115,A_115) ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_512])).

tff(c_62,plain,(
    k1_funct_1('#skF_10','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48,plain,(
    ! [A_24] : k2_zfmisc_1(A_24,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1662,plain,(
    ! [C_1820,B_1821,D_1822] :
      ( r2_hidden(k4_tarski(C_1820,B_1821),k2_zfmisc_1(k1_tarski(C_1820),D_1822))
      | ~ r2_hidden(B_1821,D_1822) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1749,plain,(
    ! [C_1878,B_1879] :
      ( r2_hidden(k4_tarski(C_1878,B_1879),k1_xboole_0)
      | ~ r2_hidden(B_1879,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1662])).

tff(c_340,plain,(
    ! [C_81,A_82,B_83,D_84] :
      ( C_81 = A_82
      | ~ r2_hidden(k4_tarski(A_82,B_83),k2_zfmisc_1(k1_tarski(C_81),D_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_343,plain,(
    ! [C_81,A_82,B_83] :
      ( C_81 = A_82
      | ~ r2_hidden(k4_tarski(A_82,B_83),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_340])).

tff(c_1765,plain,(
    ! [C_81,C_1878,B_1879] :
      ( C_81 = C_1878
      | ~ r2_hidden(B_1879,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1749,c_343])).

tff(c_1773,plain,(
    ! [B_1906] : ~ r2_hidden(B_1906,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1765])).

tff(c_1792,plain,(
    ! [B_6] : r1_tarski(k1_xboole_0,B_6) ),
    inference(resolution,[status(thm)],[c_10,c_1773])).

tff(c_70,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_68,plain,(
    v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_66,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_64,plain,(
    r2_hidden('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_5226,plain,(
    ! [D_16372,C_16373,B_16374,A_16375] :
      ( r2_hidden(k1_funct_1(D_16372,C_16373),B_16374)
      | k1_xboole_0 = B_16374
      | ~ r2_hidden(C_16373,A_16375)
      | ~ m1_subset_1(D_16372,k1_zfmisc_1(k2_zfmisc_1(A_16375,B_16374)))
      | ~ v1_funct_2(D_16372,A_16375,B_16374)
      | ~ v1_funct_1(D_16372) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_5434,plain,(
    ! [D_16901,B_16902] :
      ( r2_hidden(k1_funct_1(D_16901,'#skF_9'),B_16902)
      | k1_xboole_0 = B_16902
      | ~ m1_subset_1(D_16901,k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_16902)))
      | ~ v1_funct_2(D_16901,'#skF_7',B_16902)
      | ~ v1_funct_1(D_16901) ) ),
    inference(resolution,[status(thm)],[c_64,c_5226])).

tff(c_5447,plain,
    ( r2_hidden(k1_funct_1('#skF_10','#skF_9'),k1_tarski('#skF_8'))
    | k1_tarski('#skF_8') = k1_xboole_0
    | ~ v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8'))
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_66,c_5434])).

tff(c_5454,plain,
    ( r2_hidden(k1_funct_1('#skF_10','#skF_9'),k1_tarski('#skF_8'))
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_5447])).

tff(c_5457,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5454])).

tff(c_5549,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_5457,c_149])).

tff(c_5632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1792,c_5549])).

tff(c_5633,plain,(
    r2_hidden(k1_funct_1('#skF_10','#skF_9'),k1_tarski('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_5454])).

tff(c_5651,plain,(
    k1_funct_1('#skF_10','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_5633,c_12])).

tff(c_5719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_5651])).

tff(c_8243,plain,(
    ! [C_17423] : C_17423 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1765])).

tff(c_8245,plain,(
    r2_hidden('#skF_9','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_8243,c_64])).

tff(c_8387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_521,c_8245])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.92/2.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.92/2.30  
% 5.92/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.92/2.30  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 5.92/2.30  
% 5.92/2.30  %Foreground sorts:
% 5.92/2.30  
% 5.92/2.30  
% 5.92/2.30  %Background operators:
% 5.92/2.30  
% 5.92/2.30  
% 5.92/2.30  %Foreground operators:
% 5.92/2.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.92/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.92/2.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.92/2.30  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.92/2.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.92/2.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.92/2.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.92/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.92/2.30  tff('#skF_7', type, '#skF_7': $i).
% 5.92/2.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.92/2.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.92/2.30  tff('#skF_10', type, '#skF_10': $i).
% 5.92/2.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.92/2.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.92/2.30  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.92/2.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.92/2.30  tff('#skF_9', type, '#skF_9': $i).
% 5.92/2.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.92/2.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.92/2.30  tff('#skF_8', type, '#skF_8': $i).
% 5.92/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.92/2.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.92/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.92/2.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.92/2.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.92/2.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.92/2.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.92/2.30  
% 5.92/2.32  tff(f_45, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 5.92/2.32  tff(f_75, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.92/2.32  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.92/2.32  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.92/2.32  tff(f_98, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 5.92/2.32  tff(f_64, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.92/2.32  tff(f_70, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 5.92/2.32  tff(f_87, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 5.92/2.32  tff(c_14, plain, (![C_14]: (r2_hidden(C_14, k1_tarski(C_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.92/2.32  tff(c_134, plain, (![B_49, A_50]: (~r1_tarski(B_49, A_50) | ~r2_hidden(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.92/2.32  tff(c_149, plain, (![C_14]: (~r1_tarski(k1_tarski(C_14), C_14))), inference(resolution, [status(thm)], [c_14, c_134])).
% 5.92/2.32  tff(c_113, plain, (![B_44, A_45]: (~r2_hidden(B_44, A_45) | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.92/2.32  tff(c_128, plain, (![C_14]: (~v1_xboole_0(k1_tarski(C_14)))), inference(resolution, [status(thm)], [c_14, c_113])).
% 5.92/2.32  tff(c_166, plain, (![A_58]: (v1_xboole_0(A_58) | r2_hidden('#skF_1'(A_58), A_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.92/2.32  tff(c_12, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.92/2.32  tff(c_170, plain, (![A_10]: ('#skF_1'(k1_tarski(A_10))=A_10 | v1_xboole_0(k1_tarski(A_10)))), inference(resolution, [status(thm)], [c_166, c_12])).
% 5.92/2.32  tff(c_179, plain, (![A_10]: ('#skF_1'(k1_tarski(A_10))=A_10)), inference(negUnitSimplification, [status(thm)], [c_128, c_170])).
% 5.92/2.32  tff(c_210, plain, (![A_63, B_64]: (r2_hidden('#skF_2'(A_63, B_64), A_63) | r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.92/2.32  tff(c_460, plain, (![A_111, B_112]: ('#skF_2'(k1_tarski(A_111), B_112)=A_111 | r1_tarski(k1_tarski(A_111), B_112))), inference(resolution, [status(thm)], [c_210, c_12])).
% 5.92/2.32  tff(c_58, plain, (![B_31, A_30]: (~r1_tarski(B_31, A_30) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.92/2.32  tff(c_180, plain, (![A_58]: (~r1_tarski(A_58, '#skF_1'(A_58)) | v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_166, c_58])).
% 5.92/2.32  tff(c_479, plain, (![A_111]: (v1_xboole_0(k1_tarski(A_111)) | '#skF_2'(k1_tarski(A_111), '#skF_1'(k1_tarski(A_111)))=A_111)), inference(resolution, [status(thm)], [c_460, c_180])).
% 5.92/2.32  tff(c_492, plain, (![A_111]: (v1_xboole_0(k1_tarski(A_111)) | '#skF_2'(k1_tarski(A_111), A_111)=A_111)), inference(demodulation, [status(thm), theory('equality')], [c_179, c_479])).
% 5.92/2.32  tff(c_503, plain, (![A_115]: ('#skF_2'(k1_tarski(A_115), A_115)=A_115)), inference(negUnitSimplification, [status(thm)], [c_128, c_492])).
% 5.92/2.32  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.92/2.32  tff(c_512, plain, (![A_115]: (~r2_hidden(A_115, A_115) | r1_tarski(k1_tarski(A_115), A_115))), inference(superposition, [status(thm), theory('equality')], [c_503, c_8])).
% 5.92/2.32  tff(c_521, plain, (![A_115]: (~r2_hidden(A_115, A_115))), inference(negUnitSimplification, [status(thm)], [c_149, c_512])).
% 5.92/2.32  tff(c_62, plain, (k1_funct_1('#skF_10', '#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.92/2.32  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.92/2.32  tff(c_48, plain, (![A_24]: (k2_zfmisc_1(A_24, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.92/2.32  tff(c_1662, plain, (![C_1820, B_1821, D_1822]: (r2_hidden(k4_tarski(C_1820, B_1821), k2_zfmisc_1(k1_tarski(C_1820), D_1822)) | ~r2_hidden(B_1821, D_1822))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.92/2.32  tff(c_1749, plain, (![C_1878, B_1879]: (r2_hidden(k4_tarski(C_1878, B_1879), k1_xboole_0) | ~r2_hidden(B_1879, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1662])).
% 5.92/2.32  tff(c_340, plain, (![C_81, A_82, B_83, D_84]: (C_81=A_82 | ~r2_hidden(k4_tarski(A_82, B_83), k2_zfmisc_1(k1_tarski(C_81), D_84)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.92/2.32  tff(c_343, plain, (![C_81, A_82, B_83]: (C_81=A_82 | ~r2_hidden(k4_tarski(A_82, B_83), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_340])).
% 5.92/2.32  tff(c_1765, plain, (![C_81, C_1878, B_1879]: (C_81=C_1878 | ~r2_hidden(B_1879, k1_xboole_0))), inference(resolution, [status(thm)], [c_1749, c_343])).
% 5.92/2.32  tff(c_1773, plain, (![B_1906]: (~r2_hidden(B_1906, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1765])).
% 5.92/2.32  tff(c_1792, plain, (![B_6]: (r1_tarski(k1_xboole_0, B_6))), inference(resolution, [status(thm)], [c_10, c_1773])).
% 5.92/2.32  tff(c_70, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.92/2.32  tff(c_68, plain, (v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.92/2.32  tff(c_66, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.92/2.32  tff(c_64, plain, (r2_hidden('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.92/2.32  tff(c_5226, plain, (![D_16372, C_16373, B_16374, A_16375]: (r2_hidden(k1_funct_1(D_16372, C_16373), B_16374) | k1_xboole_0=B_16374 | ~r2_hidden(C_16373, A_16375) | ~m1_subset_1(D_16372, k1_zfmisc_1(k2_zfmisc_1(A_16375, B_16374))) | ~v1_funct_2(D_16372, A_16375, B_16374) | ~v1_funct_1(D_16372))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.92/2.32  tff(c_5434, plain, (![D_16901, B_16902]: (r2_hidden(k1_funct_1(D_16901, '#skF_9'), B_16902) | k1_xboole_0=B_16902 | ~m1_subset_1(D_16901, k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_16902))) | ~v1_funct_2(D_16901, '#skF_7', B_16902) | ~v1_funct_1(D_16901))), inference(resolution, [status(thm)], [c_64, c_5226])).
% 5.92/2.32  tff(c_5447, plain, (r2_hidden(k1_funct_1('#skF_10', '#skF_9'), k1_tarski('#skF_8')) | k1_tarski('#skF_8')=k1_xboole_0 | ~v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8')) | ~v1_funct_1('#skF_10')), inference(resolution, [status(thm)], [c_66, c_5434])).
% 5.92/2.32  tff(c_5454, plain, (r2_hidden(k1_funct_1('#skF_10', '#skF_9'), k1_tarski('#skF_8')) | k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_5447])).
% 5.92/2.32  tff(c_5457, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5454])).
% 5.92/2.32  tff(c_5549, plain, (~r1_tarski(k1_xboole_0, '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_5457, c_149])).
% 5.92/2.32  tff(c_5632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1792, c_5549])).
% 5.92/2.32  tff(c_5633, plain, (r2_hidden(k1_funct_1('#skF_10', '#skF_9'), k1_tarski('#skF_8'))), inference(splitRight, [status(thm)], [c_5454])).
% 5.92/2.32  tff(c_5651, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_5633, c_12])).
% 5.92/2.32  tff(c_5719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_5651])).
% 5.92/2.32  tff(c_8243, plain, (![C_17423]: (C_17423='#skF_9')), inference(splitRight, [status(thm)], [c_1765])).
% 5.92/2.32  tff(c_8245, plain, (r2_hidden('#skF_9', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_8243, c_64])).
% 5.92/2.32  tff(c_8387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_521, c_8245])).
% 5.92/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.92/2.32  
% 5.92/2.32  Inference rules
% 5.92/2.32  ----------------------
% 5.92/2.32  #Ref     : 0
% 5.92/2.32  #Sup     : 1429
% 5.92/2.32  #Fact    : 2
% 5.92/2.32  #Define  : 0
% 5.92/2.32  #Split   : 11
% 5.92/2.32  #Chain   : 0
% 5.92/2.32  #Close   : 0
% 5.92/2.32  
% 5.92/2.32  Ordering : KBO
% 5.92/2.32  
% 5.92/2.32  Simplification rules
% 5.92/2.32  ----------------------
% 5.92/2.32  #Subsume      : 243
% 5.92/2.32  #Demod        : 143
% 5.92/2.32  #Tautology    : 253
% 5.92/2.32  #SimpNegUnit  : 64
% 5.92/2.32  #BackRed      : 2
% 5.92/2.32  
% 5.92/2.32  #Partial instantiations: 9290
% 5.92/2.32  #Strategies tried      : 1
% 5.92/2.32  
% 5.92/2.32  Timing (in seconds)
% 5.92/2.32  ----------------------
% 5.92/2.32  Preprocessing        : 0.32
% 5.92/2.32  Parsing              : 0.17
% 5.92/2.32  CNF conversion       : 0.03
% 5.92/2.32  Main loop            : 1.13
% 5.92/2.32  Inferencing          : 0.53
% 5.92/2.32  Reduction            : 0.28
% 5.92/2.32  Demodulation         : 0.18
% 5.92/2.32  BG Simplification    : 0.04
% 5.92/2.32  Subsumption          : 0.20
% 5.92/2.32  Abstraction          : 0.05
% 5.92/2.32  MUC search           : 0.00
% 5.92/2.32  Cooper               : 0.00
% 5.92/2.32  Total                : 1.48
% 5.92/2.32  Index Insertion      : 0.00
% 5.92/2.32  Index Deletion       : 0.00
% 5.92/2.32  Index Matching       : 0.00
% 5.92/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
