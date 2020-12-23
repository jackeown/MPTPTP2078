%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:23 EST 2020

% Result     : Theorem 4.46s
% Output     : CNFRefutation 4.46s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 103 expanded)
%              Number of leaves         :   31 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :   91 ( 192 expanded)
%              Number of equality atoms :   25 (  48 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_34,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_964,plain,(
    ! [A_887,B_888] :
      ( '#skF_3'(A_887,B_888) = A_887
      | r2_hidden('#skF_4'(A_887,B_888),B_888)
      | k1_tarski(A_887) = B_888 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1111,plain,(
    ! [B_947,A_948] :
      ( ~ v1_xboole_0(B_947)
      | '#skF_3'(A_948,B_947) = A_948
      | k1_tarski(A_948) = B_947 ) ),
    inference(resolution,[status(thm)],[c_964,c_2])).

tff(c_1132,plain,(
    ! [A_985] :
      ( '#skF_3'(A_985,k1_xboole_0) = A_985
      | k1_tarski(A_985) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_1111])).

tff(c_16,plain,(
    ! [C_14] : r2_hidden(C_14,k1_tarski(C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    ! [B_25,A_26] :
      ( ~ r2_hidden(B_25,A_26)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ! [C_14] : ~ v1_xboole_0(k1_tarski(C_14)) ),
    inference(resolution,[status(thm)],[c_16,c_44])).

tff(c_1176,plain,(
    ! [A_985] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | '#skF_3'(A_985,k1_xboole_0) = A_985 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1132,c_51])).

tff(c_1234,plain,(
    ! [A_985] : '#skF_3'(A_985,k1_xboole_0) = A_985 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1176])).

tff(c_1256,plain,(
    ! [A_1023,B_1024] :
      ( ~ r2_hidden('#skF_3'(A_1023,B_1024),B_1024)
      | r2_hidden('#skF_4'(A_1023,B_1024),B_1024)
      | k1_tarski(A_1023) = B_1024 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2965,plain,(
    ! [A_7443] :
      ( ~ r2_hidden(A_7443,k1_xboole_0)
      | r2_hidden('#skF_4'(A_7443,k1_xboole_0),k1_xboole_0)
      | k1_tarski(A_7443) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1234,c_1256])).

tff(c_2980,plain,(
    ! [A_7443] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_7443,k1_xboole_0)
      | k1_tarski(A_7443) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2965,c_2])).

tff(c_3010,plain,(
    ! [A_7534] :
      ( ~ r2_hidden(A_7534,k1_xboole_0)
      | k1_tarski(A_7534) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2980])).

tff(c_3058,plain,(
    ! [B_7625] :
      ( k1_tarski('#skF_2'(k1_xboole_0,B_7625)) = k1_xboole_0
      | r1_tarski(k1_xboole_0,B_7625) ) ),
    inference(resolution,[status(thm)],[c_10,c_3010])).

tff(c_3113,plain,(
    ! [B_7625] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r1_tarski(k1_xboole_0,B_7625) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3058,c_51])).

tff(c_3177,plain,(
    ! [B_7625] : r1_tarski(k1_xboole_0,B_7625) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3113])).

tff(c_42,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_40,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_38,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1492,plain,(
    ! [D_1122,C_1123,B_1124,A_1125] :
      ( r2_hidden(k1_funct_1(D_1122,C_1123),B_1124)
      | k1_xboole_0 = B_1124
      | ~ r2_hidden(C_1123,A_1125)
      | ~ m1_subset_1(D_1122,k1_zfmisc_1(k2_zfmisc_1(A_1125,B_1124)))
      | ~ v1_funct_2(D_1122,A_1125,B_1124)
      | ~ v1_funct_1(D_1122) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3683,plain,(
    ! [D_8355,B_8356] :
      ( r2_hidden(k1_funct_1(D_8355,'#skF_7'),B_8356)
      | k1_xboole_0 = B_8356
      | ~ m1_subset_1(D_8355,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_8356)))
      | ~ v1_funct_2(D_8355,'#skF_5',B_8356)
      | ~ v1_funct_1(D_8355) ) ),
    inference(resolution,[status(thm)],[c_36,c_1492])).

tff(c_3696,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_3683])).

tff(c_3699,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_3696])).

tff(c_3700,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3699])).

tff(c_63,plain,(
    ! [B_29,A_30] :
      ( ~ r1_tarski(B_29,A_30)
      | ~ r2_hidden(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_70,plain,(
    ! [C_14] : ~ r1_tarski(k1_tarski(C_14),C_14) ),
    inference(resolution,[status(thm)],[c_16,c_63])).

tff(c_3759,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3700,c_70])).

tff(c_3822,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3177,c_3759])).

tff(c_3823,plain,(
    r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_3699])).

tff(c_14,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3841,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3823,c_14])).

tff(c_3904,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_3841])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:30:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.46/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.88  
% 4.46/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.88  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4
% 4.46/1.88  
% 4.46/1.88  %Foreground sorts:
% 4.46/1.88  
% 4.46/1.88  
% 4.46/1.88  %Background operators:
% 4.46/1.88  
% 4.46/1.88  
% 4.46/1.88  %Foreground operators:
% 4.46/1.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.46/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.46/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.46/1.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.46/1.88  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.46/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.46/1.88  tff('#skF_7', type, '#skF_7': $i).
% 4.46/1.88  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.46/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.46/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.46/1.88  tff('#skF_5', type, '#skF_5': $i).
% 4.46/1.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.46/1.88  tff('#skF_6', type, '#skF_6': $i).
% 4.46/1.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.46/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.46/1.88  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.46/1.88  tff('#skF_8', type, '#skF_8': $i).
% 4.46/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.46/1.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.46/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.46/1.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.46/1.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.46/1.88  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.46/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.46/1.88  
% 4.46/1.89  tff(f_78, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 4.46/1.89  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.46/1.89  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.46/1.89  tff(f_46, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.46/1.89  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.46/1.89  tff(f_67, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 4.46/1.89  tff(f_55, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.46/1.89  tff(c_34, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.46/1.89  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.46/1.89  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.46/1.89  tff(c_964, plain, (![A_887, B_888]: ('#skF_3'(A_887, B_888)=A_887 | r2_hidden('#skF_4'(A_887, B_888), B_888) | k1_tarski(A_887)=B_888)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.46/1.89  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.46/1.89  tff(c_1111, plain, (![B_947, A_948]: (~v1_xboole_0(B_947) | '#skF_3'(A_948, B_947)=A_948 | k1_tarski(A_948)=B_947)), inference(resolution, [status(thm)], [c_964, c_2])).
% 4.46/1.89  tff(c_1132, plain, (![A_985]: ('#skF_3'(A_985, k1_xboole_0)=A_985 | k1_tarski(A_985)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_1111])).
% 4.46/1.89  tff(c_16, plain, (![C_14]: (r2_hidden(C_14, k1_tarski(C_14)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.46/1.89  tff(c_44, plain, (![B_25, A_26]: (~r2_hidden(B_25, A_26) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.46/1.89  tff(c_51, plain, (![C_14]: (~v1_xboole_0(k1_tarski(C_14)))), inference(resolution, [status(thm)], [c_16, c_44])).
% 4.46/1.89  tff(c_1176, plain, (![A_985]: (~v1_xboole_0(k1_xboole_0) | '#skF_3'(A_985, k1_xboole_0)=A_985)), inference(superposition, [status(thm), theory('equality')], [c_1132, c_51])).
% 4.46/1.89  tff(c_1234, plain, (![A_985]: ('#skF_3'(A_985, k1_xboole_0)=A_985)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1176])).
% 4.46/1.89  tff(c_1256, plain, (![A_1023, B_1024]: (~r2_hidden('#skF_3'(A_1023, B_1024), B_1024) | r2_hidden('#skF_4'(A_1023, B_1024), B_1024) | k1_tarski(A_1023)=B_1024)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.46/1.89  tff(c_2965, plain, (![A_7443]: (~r2_hidden(A_7443, k1_xboole_0) | r2_hidden('#skF_4'(A_7443, k1_xboole_0), k1_xboole_0) | k1_tarski(A_7443)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1234, c_1256])).
% 4.46/1.89  tff(c_2980, plain, (![A_7443]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_7443, k1_xboole_0) | k1_tarski(A_7443)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2965, c_2])).
% 4.46/1.89  tff(c_3010, plain, (![A_7534]: (~r2_hidden(A_7534, k1_xboole_0) | k1_tarski(A_7534)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2980])).
% 4.46/1.89  tff(c_3058, plain, (![B_7625]: (k1_tarski('#skF_2'(k1_xboole_0, B_7625))=k1_xboole_0 | r1_tarski(k1_xboole_0, B_7625))), inference(resolution, [status(thm)], [c_10, c_3010])).
% 4.46/1.89  tff(c_3113, plain, (![B_7625]: (~v1_xboole_0(k1_xboole_0) | r1_tarski(k1_xboole_0, B_7625))), inference(superposition, [status(thm), theory('equality')], [c_3058, c_51])).
% 4.46/1.89  tff(c_3177, plain, (![B_7625]: (r1_tarski(k1_xboole_0, B_7625))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3113])).
% 4.46/1.89  tff(c_42, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.46/1.89  tff(c_40, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.46/1.89  tff(c_38, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.46/1.89  tff(c_36, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.46/1.89  tff(c_1492, plain, (![D_1122, C_1123, B_1124, A_1125]: (r2_hidden(k1_funct_1(D_1122, C_1123), B_1124) | k1_xboole_0=B_1124 | ~r2_hidden(C_1123, A_1125) | ~m1_subset_1(D_1122, k1_zfmisc_1(k2_zfmisc_1(A_1125, B_1124))) | ~v1_funct_2(D_1122, A_1125, B_1124) | ~v1_funct_1(D_1122))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.46/1.89  tff(c_3683, plain, (![D_8355, B_8356]: (r2_hidden(k1_funct_1(D_8355, '#skF_7'), B_8356) | k1_xboole_0=B_8356 | ~m1_subset_1(D_8355, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_8356))) | ~v1_funct_2(D_8355, '#skF_5', B_8356) | ~v1_funct_1(D_8355))), inference(resolution, [status(thm)], [c_36, c_1492])).
% 4.46/1.89  tff(c_3696, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0 | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_3683])).
% 4.46/1.89  tff(c_3699, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_3696])).
% 4.46/1.89  tff(c_3700, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3699])).
% 4.46/1.89  tff(c_63, plain, (![B_29, A_30]: (~r1_tarski(B_29, A_30) | ~r2_hidden(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.46/1.89  tff(c_70, plain, (![C_14]: (~r1_tarski(k1_tarski(C_14), C_14))), inference(resolution, [status(thm)], [c_16, c_63])).
% 4.46/1.89  tff(c_3759, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3700, c_70])).
% 4.46/1.89  tff(c_3822, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3177, c_3759])).
% 4.46/1.89  tff(c_3823, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_3699])).
% 4.46/1.89  tff(c_14, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.46/1.89  tff(c_3841, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_3823, c_14])).
% 4.46/1.89  tff(c_3904, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_3841])).
% 4.46/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.89  
% 4.46/1.89  Inference rules
% 4.46/1.89  ----------------------
% 4.46/1.89  #Ref     : 0
% 4.46/1.89  #Sup     : 591
% 4.46/1.89  #Fact    : 0
% 4.46/1.89  #Define  : 0
% 4.46/1.89  #Split   : 10
% 4.46/1.89  #Chain   : 0
% 4.46/1.89  #Close   : 0
% 4.46/1.89  
% 4.46/1.89  Ordering : KBO
% 4.46/1.89  
% 4.46/1.89  Simplification rules
% 4.46/1.89  ----------------------
% 4.46/1.89  #Subsume      : 153
% 4.46/1.89  #Demod        : 87
% 4.46/1.89  #Tautology    : 147
% 4.46/1.89  #SimpNegUnit  : 36
% 4.46/1.89  #BackRed      : 2
% 4.46/1.89  
% 4.46/1.89  #Partial instantiations: 4854
% 4.46/1.89  #Strategies tried      : 1
% 4.46/1.89  
% 4.46/1.89  Timing (in seconds)
% 4.46/1.89  ----------------------
% 4.46/1.90  Preprocessing        : 0.31
% 4.46/1.90  Parsing              : 0.16
% 4.46/1.90  CNF conversion       : 0.02
% 4.46/1.90  Main loop            : 0.79
% 4.46/1.90  Inferencing          : 0.40
% 4.46/1.90  Reduction            : 0.18
% 4.46/1.90  Demodulation         : 0.11
% 4.46/1.90  BG Simplification    : 0.03
% 4.46/1.90  Subsumption          : 0.12
% 4.46/1.90  Abstraction          : 0.04
% 4.46/1.90  MUC search           : 0.00
% 4.46/1.90  Cooper               : 0.00
% 4.46/1.90  Total                : 1.14
% 4.46/1.90  Index Insertion      : 0.00
% 4.46/1.90  Index Deletion       : 0.00
% 4.46/1.90  Index Matching       : 0.00
% 4.46/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
