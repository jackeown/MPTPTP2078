%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:12 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 168 expanded)
%              Number of leaves         :   43 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :  121 ( 249 expanded)
%              Number of equality atoms :   45 (  98 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_73,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_75,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_99,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_106,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_58,plain,(
    ! [A_27] : r1_tarski(k1_xboole_0,A_27) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_213,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(A_66,B_67) = A_66
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_241,plain,(
    ! [A_71] : k3_xboole_0(k1_xboole_0,A_71) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_213])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_250,plain,(
    ! [A_71] : k3_xboole_0(A_71,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_2])).

tff(c_54,plain,(
    ! [A_24] : k2_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_62,plain,(
    ! [A_30] : k4_xboole_0(k1_xboole_0,A_30) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_580,plain,(
    ! [A_108,B_109] : k5_xboole_0(A_108,k4_xboole_0(B_109,A_108)) = k2_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_589,plain,(
    ! [A_30] : k5_xboole_0(A_30,k1_xboole_0) = k2_xboole_0(A_30,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_580])).

tff(c_592,plain,(
    ! [A_30] : k5_xboole_0(A_30,k1_xboole_0) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_589])).

tff(c_490,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_499,plain,(
    ! [A_71] : k5_xboole_0(A_71,k1_xboole_0) = k4_xboole_0(A_71,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_490])).

tff(c_652,plain,(
    ! [A_113] : k4_xboole_0(A_113,k1_xboole_0) = A_113 ),
    inference(demodulation,[status(thm),theory(equality)],[c_592,c_499])).

tff(c_60,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_658,plain,(
    ! [A_113] : k4_xboole_0(A_113,A_113) = k3_xboole_0(A_113,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_652,c_60])).

tff(c_680,plain,(
    ! [A_113] : k4_xboole_0(A_113,A_113) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_658])).

tff(c_88,plain,(
    ! [A_41] : k2_subset_1(A_41) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_106,plain,
    ( r1_tarski(k3_subset_1('#skF_8','#skF_9'),'#skF_9')
    | k2_subset_1('#skF_8') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_109,plain,
    ( r1_tarski(k3_subset_1('#skF_8','#skF_9'),'#skF_9')
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_106])).

tff(c_156,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_98,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_157,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_98])).

tff(c_829,plain,(
    ! [A_123,B_124] :
      ( k4_xboole_0(A_123,B_124) = k3_subset_1(A_123,B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(A_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_839,plain,(
    k4_xboole_0('#skF_8','#skF_8') = k3_subset_1('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_157,c_829])).

tff(c_843,plain,(
    k3_subset_1('#skF_8','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_839])).

tff(c_100,plain,
    ( k2_subset_1('#skF_8') != '#skF_9'
    | ~ r1_tarski(k3_subset_1('#skF_8','#skF_9'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_108,plain,
    ( '#skF_9' != '#skF_8'
    | ~ r1_tarski(k3_subset_1('#skF_8','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_100])).

tff(c_212,plain,(
    ~ r1_tarski(k3_subset_1('#skF_8','#skF_8'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_156,c_156,c_108])).

tff(c_844,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_212])).

tff(c_847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_844])).

tff(c_849,plain,(
    '#skF_9' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_92,plain,(
    ! [A_44] : ~ v1_xboole_0(k1_zfmisc_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1120,plain,(
    ! [B_155,A_156] :
      ( r2_hidden(B_155,A_156)
      | ~ m1_subset_1(B_155,A_156)
      | v1_xboole_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_66,plain,(
    ! [C_37,A_33] :
      ( r1_tarski(C_37,A_33)
      | ~ r2_hidden(C_37,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1135,plain,(
    ! [B_155,A_33] :
      ( r1_tarski(B_155,A_33)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(A_33))
      | v1_xboole_0(k1_zfmisc_1(A_33)) ) ),
    inference(resolution,[status(thm)],[c_1120,c_66])).

tff(c_1142,plain,(
    ! [B_157,A_158] :
      ( r1_tarski(B_157,A_158)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(A_158)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1135])).

tff(c_1151,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_98,c_1142])).

tff(c_46,plain,(
    ! [B_21,A_20] :
      ( B_21 = A_20
      | ~ r1_tarski(B_21,A_20)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1153,plain,
    ( '#skF_9' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_1151,c_46])).

tff(c_1159,plain,(
    ~ r1_tarski('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_849,c_1153])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1754,plain,(
    ! [A_202,B_203] :
      ( k4_xboole_0(A_202,B_203) = k3_subset_1(A_202,B_203)
      | ~ m1_subset_1(B_203,k1_zfmisc_1(A_202)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1767,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k3_subset_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_98,c_1754])).

tff(c_1935,plain,(
    ! [D_211,A_212,B_213] :
      ( r2_hidden(D_211,k4_xboole_0(A_212,B_213))
      | r2_hidden(D_211,B_213)
      | ~ r2_hidden(D_211,A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1992,plain,(
    ! [D_214] :
      ( r2_hidden(D_214,k3_subset_1('#skF_8','#skF_9'))
      | r2_hidden(D_214,'#skF_9')
      | ~ r2_hidden(D_214,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1767,c_1935])).

tff(c_848,plain,(
    r1_tarski(k3_subset_1('#skF_8','#skF_9'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_885,plain,(
    ! [A_127,B_128] :
      ( k3_xboole_0(A_127,B_128) = A_127
      | ~ r1_tarski(A_127,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_895,plain,(
    k3_xboole_0(k3_subset_1('#skF_8','#skF_9'),'#skF_9') = k3_subset_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_848,c_885])).

tff(c_1016,plain,(
    ! [D_140,B_141,A_142] :
      ( r2_hidden(D_140,B_141)
      | ~ r2_hidden(D_140,k3_xboole_0(A_142,B_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1019,plain,(
    ! [D_140] :
      ( r2_hidden(D_140,'#skF_9')
      | ~ r2_hidden(D_140,k3_subset_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_895,c_1016])).

tff(c_2017,plain,(
    ! [D_215] :
      ( r2_hidden(D_215,'#skF_9')
      | ~ r2_hidden(D_215,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1992,c_1019])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2035,plain,(
    ! [A_216] :
      ( r1_tarski(A_216,'#skF_9')
      | ~ r2_hidden('#skF_1'(A_216,'#skF_9'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2017,c_6])).

tff(c_2042,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_8,c_2035])).

tff(c_2047,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1159,c_1159,c_2042])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:51:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.70  
% 3.93/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.70  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1
% 3.93/1.70  
% 3.93/1.70  %Foreground sorts:
% 3.93/1.70  
% 3.93/1.70  
% 3.93/1.70  %Background operators:
% 3.93/1.70  
% 3.93/1.70  
% 3.93/1.70  %Foreground operators:
% 3.93/1.70  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.93/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.93/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.93/1.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.93/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.93/1.70  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.93/1.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.93/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.93/1.70  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.93/1.70  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.93/1.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.93/1.70  tff('#skF_9', type, '#skF_9': $i).
% 3.93/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.93/1.70  tff('#skF_8', type, '#skF_8': $i).
% 3.93/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.93/1.70  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.93/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.93/1.70  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.93/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.93/1.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.93/1.70  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.93/1.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.93/1.70  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.93/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.93/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.93/1.70  
% 3.93/1.72  tff(f_69, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.93/1.72  tff(f_67, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.93/1.72  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.93/1.72  tff(f_63, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.93/1.72  tff(f_73, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.93/1.72  tff(f_75, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.93/1.72  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.93/1.72  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.93/1.72  tff(f_99, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.93/1.72  tff(f_119, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 3.93/1.72  tff(f_103, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.93/1.72  tff(f_106, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.93/1.72  tff(f_95, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.93/1.72  tff(f_82, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.93/1.72  tff(f_59, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.93/1.72  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.93/1.72  tff(f_53, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.93/1.72  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.93/1.72  tff(c_58, plain, (![A_27]: (r1_tarski(k1_xboole_0, A_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.93/1.72  tff(c_213, plain, (![A_66, B_67]: (k3_xboole_0(A_66, B_67)=A_66 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.93/1.72  tff(c_241, plain, (![A_71]: (k3_xboole_0(k1_xboole_0, A_71)=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_213])).
% 3.93/1.72  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.93/1.72  tff(c_250, plain, (![A_71]: (k3_xboole_0(A_71, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_241, c_2])).
% 3.93/1.72  tff(c_54, plain, (![A_24]: (k2_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.93/1.72  tff(c_62, plain, (![A_30]: (k4_xboole_0(k1_xboole_0, A_30)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.93/1.72  tff(c_580, plain, (![A_108, B_109]: (k5_xboole_0(A_108, k4_xboole_0(B_109, A_108))=k2_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.93/1.72  tff(c_589, plain, (![A_30]: (k5_xboole_0(A_30, k1_xboole_0)=k2_xboole_0(A_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_62, c_580])).
% 3.93/1.72  tff(c_592, plain, (![A_30]: (k5_xboole_0(A_30, k1_xboole_0)=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_589])).
% 3.93/1.72  tff(c_490, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.93/1.72  tff(c_499, plain, (![A_71]: (k5_xboole_0(A_71, k1_xboole_0)=k4_xboole_0(A_71, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_250, c_490])).
% 3.93/1.72  tff(c_652, plain, (![A_113]: (k4_xboole_0(A_113, k1_xboole_0)=A_113)), inference(demodulation, [status(thm), theory('equality')], [c_592, c_499])).
% 3.93/1.72  tff(c_60, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.93/1.72  tff(c_658, plain, (![A_113]: (k4_xboole_0(A_113, A_113)=k3_xboole_0(A_113, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_652, c_60])).
% 3.93/1.72  tff(c_680, plain, (![A_113]: (k4_xboole_0(A_113, A_113)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_250, c_658])).
% 3.93/1.72  tff(c_88, plain, (![A_41]: (k2_subset_1(A_41)=A_41)), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.93/1.72  tff(c_106, plain, (r1_tarski(k3_subset_1('#skF_8', '#skF_9'), '#skF_9') | k2_subset_1('#skF_8')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.93/1.72  tff(c_109, plain, (r1_tarski(k3_subset_1('#skF_8', '#skF_9'), '#skF_9') | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_106])).
% 3.93/1.72  tff(c_156, plain, ('#skF_9'='#skF_8'), inference(splitLeft, [status(thm)], [c_109])).
% 3.93/1.72  tff(c_98, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.93/1.72  tff(c_157, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_98])).
% 3.93/1.72  tff(c_829, plain, (![A_123, B_124]: (k4_xboole_0(A_123, B_124)=k3_subset_1(A_123, B_124) | ~m1_subset_1(B_124, k1_zfmisc_1(A_123)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.93/1.72  tff(c_839, plain, (k4_xboole_0('#skF_8', '#skF_8')=k3_subset_1('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_157, c_829])).
% 3.93/1.72  tff(c_843, plain, (k3_subset_1('#skF_8', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_680, c_839])).
% 3.93/1.72  tff(c_100, plain, (k2_subset_1('#skF_8')!='#skF_9' | ~r1_tarski(k3_subset_1('#skF_8', '#skF_9'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.93/1.72  tff(c_108, plain, ('#skF_9'!='#skF_8' | ~r1_tarski(k3_subset_1('#skF_8', '#skF_9'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_100])).
% 3.93/1.72  tff(c_212, plain, (~r1_tarski(k3_subset_1('#skF_8', '#skF_8'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_156, c_156, c_108])).
% 3.93/1.72  tff(c_844, plain, (~r1_tarski(k1_xboole_0, '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_843, c_212])).
% 3.93/1.72  tff(c_847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_844])).
% 3.93/1.72  tff(c_849, plain, ('#skF_9'!='#skF_8'), inference(splitRight, [status(thm)], [c_109])).
% 3.93/1.72  tff(c_92, plain, (![A_44]: (~v1_xboole_0(k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.93/1.72  tff(c_1120, plain, (![B_155, A_156]: (r2_hidden(B_155, A_156) | ~m1_subset_1(B_155, A_156) | v1_xboole_0(A_156))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.93/1.72  tff(c_66, plain, (![C_37, A_33]: (r1_tarski(C_37, A_33) | ~r2_hidden(C_37, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.93/1.72  tff(c_1135, plain, (![B_155, A_33]: (r1_tarski(B_155, A_33) | ~m1_subset_1(B_155, k1_zfmisc_1(A_33)) | v1_xboole_0(k1_zfmisc_1(A_33)))), inference(resolution, [status(thm)], [c_1120, c_66])).
% 3.93/1.72  tff(c_1142, plain, (![B_157, A_158]: (r1_tarski(B_157, A_158) | ~m1_subset_1(B_157, k1_zfmisc_1(A_158)))), inference(negUnitSimplification, [status(thm)], [c_92, c_1135])).
% 3.93/1.72  tff(c_1151, plain, (r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_98, c_1142])).
% 3.93/1.72  tff(c_46, plain, (![B_21, A_20]: (B_21=A_20 | ~r1_tarski(B_21, A_20) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.93/1.72  tff(c_1153, plain, ('#skF_9'='#skF_8' | ~r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_1151, c_46])).
% 3.93/1.72  tff(c_1159, plain, (~r1_tarski('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_849, c_1153])).
% 3.93/1.72  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.93/1.72  tff(c_1754, plain, (![A_202, B_203]: (k4_xboole_0(A_202, B_203)=k3_subset_1(A_202, B_203) | ~m1_subset_1(B_203, k1_zfmisc_1(A_202)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.93/1.72  tff(c_1767, plain, (k4_xboole_0('#skF_8', '#skF_9')=k3_subset_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_98, c_1754])).
% 3.93/1.72  tff(c_1935, plain, (![D_211, A_212, B_213]: (r2_hidden(D_211, k4_xboole_0(A_212, B_213)) | r2_hidden(D_211, B_213) | ~r2_hidden(D_211, A_212))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.93/1.72  tff(c_1992, plain, (![D_214]: (r2_hidden(D_214, k3_subset_1('#skF_8', '#skF_9')) | r2_hidden(D_214, '#skF_9') | ~r2_hidden(D_214, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1767, c_1935])).
% 3.93/1.72  tff(c_848, plain, (r1_tarski(k3_subset_1('#skF_8', '#skF_9'), '#skF_9')), inference(splitRight, [status(thm)], [c_109])).
% 3.93/1.72  tff(c_885, plain, (![A_127, B_128]: (k3_xboole_0(A_127, B_128)=A_127 | ~r1_tarski(A_127, B_128))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.93/1.72  tff(c_895, plain, (k3_xboole_0(k3_subset_1('#skF_8', '#skF_9'), '#skF_9')=k3_subset_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_848, c_885])).
% 3.93/1.72  tff(c_1016, plain, (![D_140, B_141, A_142]: (r2_hidden(D_140, B_141) | ~r2_hidden(D_140, k3_xboole_0(A_142, B_141)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.93/1.72  tff(c_1019, plain, (![D_140]: (r2_hidden(D_140, '#skF_9') | ~r2_hidden(D_140, k3_subset_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_895, c_1016])).
% 3.93/1.72  tff(c_2017, plain, (![D_215]: (r2_hidden(D_215, '#skF_9') | ~r2_hidden(D_215, '#skF_8'))), inference(resolution, [status(thm)], [c_1992, c_1019])).
% 3.93/1.72  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.93/1.72  tff(c_2035, plain, (![A_216]: (r1_tarski(A_216, '#skF_9') | ~r2_hidden('#skF_1'(A_216, '#skF_9'), '#skF_8'))), inference(resolution, [status(thm)], [c_2017, c_6])).
% 3.93/1.72  tff(c_2042, plain, (r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_8, c_2035])).
% 3.93/1.72  tff(c_2047, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1159, c_1159, c_2042])).
% 3.93/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.72  
% 3.93/1.72  Inference rules
% 3.93/1.72  ----------------------
% 3.93/1.72  #Ref     : 0
% 3.93/1.72  #Sup     : 474
% 3.93/1.72  #Fact    : 0
% 3.93/1.72  #Define  : 0
% 3.93/1.72  #Split   : 6
% 3.93/1.72  #Chain   : 0
% 3.93/1.72  #Close   : 0
% 3.93/1.72  
% 3.93/1.72  Ordering : KBO
% 3.93/1.72  
% 3.93/1.72  Simplification rules
% 3.93/1.72  ----------------------
% 3.93/1.72  #Subsume      : 57
% 3.93/1.72  #Demod        : 147
% 3.93/1.72  #Tautology    : 279
% 3.93/1.72  #SimpNegUnit  : 8
% 3.93/1.72  #BackRed      : 6
% 3.93/1.72  
% 3.93/1.72  #Partial instantiations: 0
% 3.93/1.72  #Strategies tried      : 1
% 3.93/1.72  
% 3.93/1.72  Timing (in seconds)
% 3.93/1.72  ----------------------
% 3.93/1.72  Preprocessing        : 0.37
% 3.93/1.72  Parsing              : 0.19
% 3.93/1.72  CNF conversion       : 0.03
% 3.93/1.72  Main loop            : 0.57
% 3.93/1.72  Inferencing          : 0.20
% 3.93/1.73  Reduction            : 0.19
% 3.93/1.73  Demodulation         : 0.14
% 3.93/1.73  BG Simplification    : 0.03
% 3.93/1.73  Subsumption          : 0.11
% 3.93/1.73  Abstraction          : 0.03
% 3.93/1.73  MUC search           : 0.00
% 3.93/1.73  Cooper               : 0.00
% 3.93/1.73  Total                : 0.98
% 3.93/1.73  Index Insertion      : 0.00
% 3.93/1.73  Index Deletion       : 0.00
% 3.93/1.73  Index Matching       : 0.00
% 3.93/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
