%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:54 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 123 expanded)
%              Number of leaves         :   30 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  108 ( 222 expanded)
%              Number of equality atoms :   30 (  55 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_34,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_54,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_115,plain,(
    ! [B_44,A_45] :
      ( v1_xboole_0(B_44)
      | ~ m1_subset_1(B_44,A_45)
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_127,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_115])).

tff(c_128,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_40,plain,(
    ! [B_23,A_22] :
      ( r2_hidden(B_23,A_22)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_52,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_175,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54,B_55),A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_184,plain,(
    ! [A_54] : r1_tarski(A_54,A_54) ),
    inference(resolution,[status(thm)],[c_175,c_4])).

tff(c_36,plain,(
    ! [A_21] : k5_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_185,plain,(
    ! [A_56] : r1_tarski(A_56,A_56) ),
    inference(resolution,[status(thm)],[c_175,c_4])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_208,plain,(
    ! [A_59] : k3_xboole_0(A_59,A_59) = A_59 ),
    inference(resolution,[status(thm)],[c_185,c_26])).

tff(c_24,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_214,plain,(
    ! [A_59] : k5_xboole_0(A_59,A_59) = k4_xboole_0(A_59,A_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_24])).

tff(c_235,plain,(
    ! [A_59] : k4_xboole_0(A_59,A_59) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_214])).

tff(c_278,plain,(
    ! [A_61,B_62] :
      ( k2_xboole_0(A_61,k4_xboole_0(B_62,A_61)) = B_62
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_287,plain,(
    ! [A_59] :
      ( k2_xboole_0(A_59,k1_xboole_0) = A_59
      | ~ r1_tarski(A_59,A_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_278])).

tff(c_297,plain,(
    ! [A_59] : k2_xboole_0(A_59,k1_xboole_0) = A_59 ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_287])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_441,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k3_subset_1(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_450,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k3_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_441])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_460,plain,
    ( k2_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_32])).

tff(c_464,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_460])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_361,plain,(
    ! [C_69,A_70,B_71] :
      ( r2_hidden(C_69,A_70)
      | ~ r2_hidden(C_69,B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_732,plain,(
    ! [A_112,B_113,A_114] :
      ( r2_hidden('#skF_1'(A_112,B_113),A_114)
      | ~ m1_subset_1(A_112,k1_zfmisc_1(A_114))
      | r1_tarski(A_112,B_113) ) ),
    inference(resolution,[status(thm)],[c_6,c_361])).

tff(c_770,plain,(
    ! [A_115,A_116] :
      ( ~ m1_subset_1(A_115,k1_zfmisc_1(A_116))
      | r1_tarski(A_115,A_116) ) ),
    inference(resolution,[status(thm)],[c_732,c_4])).

tff(c_781,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_770])).

tff(c_787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_464,c_781])).

tff(c_789,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_460])).

tff(c_793,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_789,c_26])).

tff(c_797,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_793,c_24])).

tff(c_800,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_797])).

tff(c_8,plain,(
    ! [A_6,B_7] : k2_xboole_0(k4_xboole_0(A_6,B_7),k4_xboole_0(B_7,A_6)) = k5_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_454,plain,(
    k2_xboole_0(k3_subset_1('#skF_2','#skF_3'),k4_xboole_0('#skF_3','#skF_2')) = k5_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_8])).

tff(c_858,plain,(
    k5_xboole_0('#skF_2','#skF_3') = k3_subset_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_800,c_454])).

tff(c_889,plain,(
    ! [A_124,C_125,B_126] :
      ( r2_hidden(A_124,C_125)
      | ~ r2_hidden(A_124,B_126)
      | r2_hidden(A_124,k5_xboole_0(B_126,C_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1258,plain,(
    ! [A_162] :
      ( r2_hidden(A_162,'#skF_3')
      | ~ r2_hidden(A_162,'#skF_2')
      | r2_hidden(A_162,k3_subset_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_889])).

tff(c_50,plain,(
    ~ r2_hidden('#skF_4',k3_subset_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1276,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_1258,c_50])).

tff(c_1286,plain,(
    ~ r2_hidden('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1276])).

tff(c_1295,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_1286])).

tff(c_1302,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1295])).

tff(c_1304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_1302])).

tff(c_1306,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_10,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1313,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1306,c_10])).

tff(c_1317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1313])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:57:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.62  
% 3.30/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.62  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.30/1.62  
% 3.30/1.62  %Foreground sorts:
% 3.30/1.62  
% 3.30/1.62  
% 3.30/1.62  %Background operators:
% 3.30/1.62  
% 3.30/1.62  
% 3.30/1.62  %Foreground operators:
% 3.30/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.30/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.30/1.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.30/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.62  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.30/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.30/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.30/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.30/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.30/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.30/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.30/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.30/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.62  
% 3.30/1.64  tff(f_102, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 3.30/1.64  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.30/1.64  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.30/1.64  tff(f_63, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.30/1.64  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.30/1.64  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.30/1.64  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 3.30/1.64  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.30/1.64  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.30/1.64  tff(f_34, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 3.30/1.64  tff(f_45, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.30/1.64  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.30/1.64  tff(c_58, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.30/1.64  tff(c_54, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.30/1.64  tff(c_115, plain, (![B_44, A_45]: (v1_xboole_0(B_44) | ~m1_subset_1(B_44, A_45) | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.30/1.64  tff(c_127, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_115])).
% 3.30/1.64  tff(c_128, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_127])).
% 3.30/1.64  tff(c_40, plain, (![B_23, A_22]: (r2_hidden(B_23, A_22) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.30/1.64  tff(c_52, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.30/1.64  tff(c_175, plain, (![A_54, B_55]: (r2_hidden('#skF_1'(A_54, B_55), A_54) | r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.30/1.64  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.30/1.64  tff(c_184, plain, (![A_54]: (r1_tarski(A_54, A_54))), inference(resolution, [status(thm)], [c_175, c_4])).
% 3.30/1.64  tff(c_36, plain, (![A_21]: (k5_xboole_0(A_21, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.30/1.64  tff(c_185, plain, (![A_56]: (r1_tarski(A_56, A_56))), inference(resolution, [status(thm)], [c_175, c_4])).
% 3.30/1.64  tff(c_26, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.30/1.64  tff(c_208, plain, (![A_59]: (k3_xboole_0(A_59, A_59)=A_59)), inference(resolution, [status(thm)], [c_185, c_26])).
% 3.30/1.64  tff(c_24, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.30/1.64  tff(c_214, plain, (![A_59]: (k5_xboole_0(A_59, A_59)=k4_xboole_0(A_59, A_59))), inference(superposition, [status(thm), theory('equality')], [c_208, c_24])).
% 3.30/1.64  tff(c_235, plain, (![A_59]: (k4_xboole_0(A_59, A_59)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_214])).
% 3.30/1.64  tff(c_278, plain, (![A_61, B_62]: (k2_xboole_0(A_61, k4_xboole_0(B_62, A_61))=B_62 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.30/1.64  tff(c_287, plain, (![A_59]: (k2_xboole_0(A_59, k1_xboole_0)=A_59 | ~r1_tarski(A_59, A_59))), inference(superposition, [status(thm), theory('equality')], [c_235, c_278])).
% 3.30/1.64  tff(c_297, plain, (![A_59]: (k2_xboole_0(A_59, k1_xboole_0)=A_59)), inference(demodulation, [status(thm), theory('equality')], [c_184, c_287])).
% 3.30/1.64  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.30/1.64  tff(c_441, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k3_subset_1(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.30/1.64  tff(c_450, plain, (k4_xboole_0('#skF_2', '#skF_3')=k3_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_441])).
% 3.30/1.64  tff(c_32, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k4_xboole_0(B_19, A_18))=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.30/1.64  tff(c_460, plain, (k2_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_3'))='#skF_2' | ~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_450, c_32])).
% 3.30/1.64  tff(c_464, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_460])).
% 3.30/1.64  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.30/1.64  tff(c_361, plain, (![C_69, A_70, B_71]: (r2_hidden(C_69, A_70) | ~r2_hidden(C_69, B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.30/1.64  tff(c_732, plain, (![A_112, B_113, A_114]: (r2_hidden('#skF_1'(A_112, B_113), A_114) | ~m1_subset_1(A_112, k1_zfmisc_1(A_114)) | r1_tarski(A_112, B_113))), inference(resolution, [status(thm)], [c_6, c_361])).
% 3.30/1.64  tff(c_770, plain, (![A_115, A_116]: (~m1_subset_1(A_115, k1_zfmisc_1(A_116)) | r1_tarski(A_115, A_116))), inference(resolution, [status(thm)], [c_732, c_4])).
% 3.30/1.64  tff(c_781, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_770])).
% 3.30/1.64  tff(c_787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_464, c_781])).
% 3.30/1.64  tff(c_789, plain, (r1_tarski('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_460])).
% 3.30/1.64  tff(c_793, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_789, c_26])).
% 3.30/1.64  tff(c_797, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_793, c_24])).
% 3.30/1.64  tff(c_800, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_797])).
% 3.30/1.64  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(k4_xboole_0(A_6, B_7), k4_xboole_0(B_7, A_6))=k5_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.30/1.64  tff(c_454, plain, (k2_xboole_0(k3_subset_1('#skF_2', '#skF_3'), k4_xboole_0('#skF_3', '#skF_2'))=k5_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_450, c_8])).
% 3.30/1.64  tff(c_858, plain, (k5_xboole_0('#skF_2', '#skF_3')=k3_subset_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_297, c_800, c_454])).
% 3.30/1.64  tff(c_889, plain, (![A_124, C_125, B_126]: (r2_hidden(A_124, C_125) | ~r2_hidden(A_124, B_126) | r2_hidden(A_124, k5_xboole_0(B_126, C_125)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.30/1.64  tff(c_1258, plain, (![A_162]: (r2_hidden(A_162, '#skF_3') | ~r2_hidden(A_162, '#skF_2') | r2_hidden(A_162, k3_subset_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_858, c_889])).
% 3.30/1.64  tff(c_50, plain, (~r2_hidden('#skF_4', k3_subset_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.30/1.64  tff(c_1276, plain, (r2_hidden('#skF_4', '#skF_3') | ~r2_hidden('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_1258, c_50])).
% 3.30/1.64  tff(c_1286, plain, (~r2_hidden('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_1276])).
% 3.30/1.64  tff(c_1295, plain, (~m1_subset_1('#skF_4', '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_1286])).
% 3.30/1.64  tff(c_1302, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1295])).
% 3.30/1.64  tff(c_1304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_1302])).
% 3.30/1.64  tff(c_1306, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_127])).
% 3.30/1.64  tff(c_10, plain, (![A_8]: (k1_xboole_0=A_8 | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.30/1.64  tff(c_1313, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1306, c_10])).
% 3.30/1.64  tff(c_1317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1313])).
% 3.30/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.64  
% 3.30/1.64  Inference rules
% 3.30/1.64  ----------------------
% 3.30/1.64  #Ref     : 0
% 3.30/1.64  #Sup     : 297
% 3.30/1.64  #Fact    : 0
% 3.30/1.64  #Define  : 0
% 3.30/1.64  #Split   : 11
% 3.30/1.64  #Chain   : 0
% 3.30/1.64  #Close   : 0
% 3.30/1.64  
% 3.30/1.64  Ordering : KBO
% 3.30/1.64  
% 3.30/1.64  Simplification rules
% 3.30/1.64  ----------------------
% 3.30/1.64  #Subsume      : 26
% 3.30/1.64  #Demod        : 60
% 3.30/1.64  #Tautology    : 123
% 3.30/1.64  #SimpNegUnit  : 11
% 3.30/1.64  #BackRed      : 0
% 3.30/1.64  
% 3.30/1.64  #Partial instantiations: 0
% 3.30/1.64  #Strategies tried      : 1
% 3.30/1.64  
% 3.30/1.64  Timing (in seconds)
% 3.30/1.64  ----------------------
% 3.30/1.64  Preprocessing        : 0.39
% 3.30/1.64  Parsing              : 0.19
% 3.30/1.64  CNF conversion       : 0.03
% 3.30/1.64  Main loop            : 0.46
% 3.30/1.64  Inferencing          : 0.17
% 3.30/1.64  Reduction            : 0.13
% 3.30/1.64  Demodulation         : 0.09
% 3.30/1.64  BG Simplification    : 0.03
% 3.30/1.64  Subsumption          : 0.09
% 3.30/1.64  Abstraction          : 0.02
% 3.30/1.64  MUC search           : 0.00
% 3.30/1.64  Cooper               : 0.00
% 3.30/1.64  Total                : 0.88
% 3.30/1.64  Index Insertion      : 0.00
% 3.30/1.64  Index Deletion       : 0.00
% 3.30/1.64  Index Matching       : 0.00
% 3.30/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
