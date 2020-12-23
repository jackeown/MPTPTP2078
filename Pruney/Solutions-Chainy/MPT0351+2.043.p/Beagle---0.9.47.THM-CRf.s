%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:42 EST 2020

% Result     : Theorem 10.93s
% Output     : CNFRefutation 11.22s
% Verified   : 
% Statistics : Number of formulae       :   64 (  92 expanded)
%              Number of leaves         :   32 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   90 ( 172 expanded)
%              Number of equality atoms :   27 (  52 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_71,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_73,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_76,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_54,plain,(
    ! [A_28] : k2_subset_1(A_28) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_56,plain,(
    ! [A_29] : m1_subset_1(k2_subset_1(A_29),k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_66,plain,(
    ! [A_29] : m1_subset_1(A_29,k1_zfmisc_1(A_29)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56])).

tff(c_642,plain,(
    ! [A_128,B_129,C_130] :
      ( k4_subset_1(A_128,B_129,C_130) = k2_xboole_0(B_129,C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(A_128))
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1146,plain,(
    ! [A_168,B_169] :
      ( k4_subset_1(A_168,B_169,A_168) = k2_xboole_0(B_169,A_168)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(A_168)) ) ),
    inference(resolution,[status(thm)],[c_66,c_642])).

tff(c_1158,plain,(
    k4_subset_1('#skF_6','#skF_7','#skF_6') = k2_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_1146])).

tff(c_1166,plain,(
    k4_subset_1('#skF_6','#skF_7','#skF_6') = k2_xboole_0('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1158])).

tff(c_62,plain,(
    k4_subset_1('#skF_6','#skF_7',k2_subset_1('#skF_6')) != k2_subset_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_65,plain,(
    k4_subset_1('#skF_6','#skF_7','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_62])).

tff(c_1235,plain,(
    k2_xboole_0('#skF_6','#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1166,c_65])).

tff(c_58,plain,(
    ! [A_30] : ~ v1_xboole_0(k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_149,plain,(
    ! [B_51,A_52] :
      ( r2_hidden(B_51,A_52)
      | ~ m1_subset_1(B_51,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    ! [C_23,A_19] :
      ( r1_tarski(C_23,A_19)
      | ~ r2_hidden(C_23,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_153,plain,(
    ! [B_51,A_19] :
      ( r1_tarski(B_51,A_19)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_149,c_32])).

tff(c_157,plain,(
    ! [B_53,A_54] :
      ( r1_tarski(B_53,A_54)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_153])).

tff(c_170,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_157])).

tff(c_1556,plain,(
    ! [A_191,B_192,C_193] :
      ( r2_hidden('#skF_2'(A_191,B_192,C_193),B_192)
      | r2_hidden('#skF_2'(A_191,B_192,C_193),A_191)
      | r2_hidden('#skF_3'(A_191,B_192,C_193),C_193)
      | k2_xboole_0(A_191,B_192) = C_193 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),C_10)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k2_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6048,plain,(
    ! [A_461,B_462] :
      ( r2_hidden('#skF_2'(A_461,B_462,A_461),B_462)
      | r2_hidden('#skF_3'(A_461,B_462,A_461),A_461)
      | k2_xboole_0(A_461,B_462) = A_461 ) ),
    inference(resolution,[status(thm)],[c_1556,c_24])).

tff(c_1254,plain,(
    ! [A_174,B_175,C_176] :
      ( r2_hidden('#skF_2'(A_174,B_175,C_176),B_175)
      | r2_hidden('#skF_2'(A_174,B_175,C_176),A_174)
      | ~ r2_hidden('#skF_3'(A_174,B_175,C_176),A_174)
      | k2_xboole_0(A_174,B_175) = C_176 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),C_10)
      | ~ r2_hidden('#skF_3'(A_8,B_9,C_10),A_8)
      | k2_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1319,plain,(
    ! [A_174,B_175] :
      ( r2_hidden('#skF_2'(A_174,B_175,A_174),B_175)
      | ~ r2_hidden('#skF_3'(A_174,B_175,A_174),A_174)
      | k2_xboole_0(A_174,B_175) = A_174 ) ),
    inference(resolution,[status(thm)],[c_1254,c_20])).

tff(c_6112,plain,(
    ! [A_463,B_464] :
      ( r2_hidden('#skF_2'(A_463,B_464,A_463),B_464)
      | k2_xboole_0(A_463,B_464) = A_463 ) ),
    inference(resolution,[status(thm)],[c_6048,c_1319])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12374,plain,(
    ! [A_782,B_783,B_784] :
      ( r2_hidden('#skF_2'(A_782,B_783,A_782),B_784)
      | ~ r1_tarski(B_783,B_784)
      | k2_xboole_0(A_782,B_783) = A_782 ) ),
    inference(resolution,[status(thm)],[c_6112,c_4])).

tff(c_12815,plain,(
    ! [B_798,B_799] :
      ( r2_hidden('#skF_3'(B_798,B_799,B_798),B_798)
      | ~ r1_tarski(B_799,B_798)
      | k2_xboole_0(B_798,B_799) = B_798 ) ),
    inference(resolution,[status(thm)],[c_12374,c_24])).

tff(c_12414,plain,(
    ! [B_784,B_783] :
      ( ~ r2_hidden('#skF_3'(B_784,B_783,B_784),B_784)
      | ~ r1_tarski(B_783,B_784)
      | k2_xboole_0(B_784,B_783) = B_784 ) ),
    inference(resolution,[status(thm)],[c_12374,c_20])).

tff(c_12892,plain,(
    ! [B_800,B_801] :
      ( ~ r1_tarski(B_800,B_801)
      | k2_xboole_0(B_801,B_800) = B_801 ) ),
    inference(resolution,[status(thm)],[c_12815,c_12414])).

tff(c_12949,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_170,c_12892])).

tff(c_12974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1235,c_12949])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:31:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.93/3.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.93/3.85  
% 10.93/3.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.93/3.85  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 10.93/3.85  
% 10.93/3.85  %Foreground sorts:
% 10.93/3.85  
% 10.93/3.85  
% 10.93/3.85  %Background operators:
% 10.93/3.85  
% 10.93/3.85  
% 10.93/3.85  %Foreground operators:
% 10.93/3.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.93/3.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.93/3.85  tff('#skF_7', type, '#skF_7': $i).
% 10.93/3.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.93/3.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.93/3.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.93/3.85  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 10.93/3.85  tff('#skF_6', type, '#skF_6': $i).
% 10.93/3.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.93/3.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.93/3.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.93/3.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.93/3.85  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.93/3.85  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.93/3.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.93/3.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.93/3.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.93/3.85  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 10.93/3.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.93/3.85  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 10.93/3.85  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.93/3.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.93/3.85  
% 11.22/3.87  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.22/3.87  tff(f_87, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 11.22/3.87  tff(f_71, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 11.22/3.87  tff(f_73, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 11.22/3.87  tff(f_82, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 11.22/3.87  tff(f_76, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 11.22/3.87  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 11.22/3.87  tff(f_54, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 11.22/3.87  tff(f_43, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 11.22/3.87  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.22/3.87  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.22/3.87  tff(c_64, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.22/3.87  tff(c_54, plain, (![A_28]: (k2_subset_1(A_28)=A_28)), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.22/3.87  tff(c_56, plain, (![A_29]: (m1_subset_1(k2_subset_1(A_29), k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.22/3.87  tff(c_66, plain, (![A_29]: (m1_subset_1(A_29, k1_zfmisc_1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56])).
% 11.22/3.87  tff(c_642, plain, (![A_128, B_129, C_130]: (k4_subset_1(A_128, B_129, C_130)=k2_xboole_0(B_129, C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(A_128)) | ~m1_subset_1(B_129, k1_zfmisc_1(A_128)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.22/3.87  tff(c_1146, plain, (![A_168, B_169]: (k4_subset_1(A_168, B_169, A_168)=k2_xboole_0(B_169, A_168) | ~m1_subset_1(B_169, k1_zfmisc_1(A_168)))), inference(resolution, [status(thm)], [c_66, c_642])).
% 11.22/3.87  tff(c_1158, plain, (k4_subset_1('#skF_6', '#skF_7', '#skF_6')=k2_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_1146])).
% 11.22/3.87  tff(c_1166, plain, (k4_subset_1('#skF_6', '#skF_7', '#skF_6')=k2_xboole_0('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1158])).
% 11.22/3.87  tff(c_62, plain, (k4_subset_1('#skF_6', '#skF_7', k2_subset_1('#skF_6'))!=k2_subset_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.22/3.87  tff(c_65, plain, (k4_subset_1('#skF_6', '#skF_7', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_62])).
% 11.22/3.87  tff(c_1235, plain, (k2_xboole_0('#skF_6', '#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1166, c_65])).
% 11.22/3.87  tff(c_58, plain, (![A_30]: (~v1_xboole_0(k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.22/3.87  tff(c_149, plain, (![B_51, A_52]: (r2_hidden(B_51, A_52) | ~m1_subset_1(B_51, A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.22/3.87  tff(c_32, plain, (![C_23, A_19]: (r1_tarski(C_23, A_19) | ~r2_hidden(C_23, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.22/3.87  tff(c_153, plain, (![B_51, A_19]: (r1_tarski(B_51, A_19) | ~m1_subset_1(B_51, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_149, c_32])).
% 11.22/3.87  tff(c_157, plain, (![B_53, A_54]: (r1_tarski(B_53, A_54) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)))), inference(negUnitSimplification, [status(thm)], [c_58, c_153])).
% 11.22/3.87  tff(c_170, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_157])).
% 11.22/3.87  tff(c_1556, plain, (![A_191, B_192, C_193]: (r2_hidden('#skF_2'(A_191, B_192, C_193), B_192) | r2_hidden('#skF_2'(A_191, B_192, C_193), A_191) | r2_hidden('#skF_3'(A_191, B_192, C_193), C_193) | k2_xboole_0(A_191, B_192)=C_193)), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.22/3.87  tff(c_24, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), C_10) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k2_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.22/3.87  tff(c_6048, plain, (![A_461, B_462]: (r2_hidden('#skF_2'(A_461, B_462, A_461), B_462) | r2_hidden('#skF_3'(A_461, B_462, A_461), A_461) | k2_xboole_0(A_461, B_462)=A_461)), inference(resolution, [status(thm)], [c_1556, c_24])).
% 11.22/3.87  tff(c_1254, plain, (![A_174, B_175, C_176]: (r2_hidden('#skF_2'(A_174, B_175, C_176), B_175) | r2_hidden('#skF_2'(A_174, B_175, C_176), A_174) | ~r2_hidden('#skF_3'(A_174, B_175, C_176), A_174) | k2_xboole_0(A_174, B_175)=C_176)), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.22/3.87  tff(c_20, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), C_10) | ~r2_hidden('#skF_3'(A_8, B_9, C_10), A_8) | k2_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.22/3.87  tff(c_1319, plain, (![A_174, B_175]: (r2_hidden('#skF_2'(A_174, B_175, A_174), B_175) | ~r2_hidden('#skF_3'(A_174, B_175, A_174), A_174) | k2_xboole_0(A_174, B_175)=A_174)), inference(resolution, [status(thm)], [c_1254, c_20])).
% 11.22/3.87  tff(c_6112, plain, (![A_463, B_464]: (r2_hidden('#skF_2'(A_463, B_464, A_463), B_464) | k2_xboole_0(A_463, B_464)=A_463)), inference(resolution, [status(thm)], [c_6048, c_1319])).
% 11.22/3.87  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.22/3.87  tff(c_12374, plain, (![A_782, B_783, B_784]: (r2_hidden('#skF_2'(A_782, B_783, A_782), B_784) | ~r1_tarski(B_783, B_784) | k2_xboole_0(A_782, B_783)=A_782)), inference(resolution, [status(thm)], [c_6112, c_4])).
% 11.22/3.87  tff(c_12815, plain, (![B_798, B_799]: (r2_hidden('#skF_3'(B_798, B_799, B_798), B_798) | ~r1_tarski(B_799, B_798) | k2_xboole_0(B_798, B_799)=B_798)), inference(resolution, [status(thm)], [c_12374, c_24])).
% 11.22/3.87  tff(c_12414, plain, (![B_784, B_783]: (~r2_hidden('#skF_3'(B_784, B_783, B_784), B_784) | ~r1_tarski(B_783, B_784) | k2_xboole_0(B_784, B_783)=B_784)), inference(resolution, [status(thm)], [c_12374, c_20])).
% 11.22/3.87  tff(c_12892, plain, (![B_800, B_801]: (~r1_tarski(B_800, B_801) | k2_xboole_0(B_801, B_800)=B_801)), inference(resolution, [status(thm)], [c_12815, c_12414])).
% 11.22/3.87  tff(c_12949, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_170, c_12892])).
% 11.22/3.87  tff(c_12974, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1235, c_12949])).
% 11.22/3.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.22/3.87  
% 11.22/3.87  Inference rules
% 11.22/3.87  ----------------------
% 11.22/3.87  #Ref     : 0
% 11.22/3.87  #Sup     : 3007
% 11.22/3.87  #Fact    : 10
% 11.22/3.87  #Define  : 0
% 11.22/3.87  #Split   : 3
% 11.22/3.87  #Chain   : 0
% 11.22/3.87  #Close   : 0
% 11.22/3.87  
% 11.22/3.87  Ordering : KBO
% 11.22/3.87  
% 11.22/3.87  Simplification rules
% 11.22/3.87  ----------------------
% 11.22/3.87  #Subsume      : 637
% 11.22/3.87  #Demod        : 883
% 11.22/3.87  #Tautology    : 807
% 11.22/3.87  #SimpNegUnit  : 59
% 11.22/3.87  #BackRed      : 4
% 11.22/3.87  
% 11.22/3.87  #Partial instantiations: 0
% 11.22/3.87  #Strategies tried      : 1
% 11.22/3.87  
% 11.22/3.87  Timing (in seconds)
% 11.22/3.87  ----------------------
% 11.22/3.87  Preprocessing        : 0.32
% 11.22/3.87  Parsing              : 0.16
% 11.22/3.87  CNF conversion       : 0.02
% 11.22/3.87  Main loop            : 2.78
% 11.22/3.87  Inferencing          : 0.67
% 11.22/3.87  Reduction            : 0.97
% 11.22/3.87  Demodulation         : 0.77
% 11.22/3.87  BG Simplification    : 0.07
% 11.22/3.87  Subsumption          : 0.88
% 11.22/3.87  Abstraction          : 0.10
% 11.22/3.87  MUC search           : 0.00
% 11.22/3.87  Cooper               : 0.00
% 11.22/3.87  Total                : 3.13
% 11.22/3.87  Index Insertion      : 0.00
% 11.22/3.87  Index Deletion       : 0.00
% 11.22/3.87  Index Matching       : 0.00
% 11.22/3.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
