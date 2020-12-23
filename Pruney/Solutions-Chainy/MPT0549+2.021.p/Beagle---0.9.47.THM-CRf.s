%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:50 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 118 expanded)
%              Number of leaves         :   32 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  103 ( 198 expanded)
%              Number of equality atoms :   41 (  77 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_98,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1100,plain,(
    ! [B_147,A_148] :
      ( r1_xboole_0(k1_relat_1(B_147),A_148)
      | k7_relat_1(B_147,A_148) != k1_xboole_0
      | ~ v1_relat_1(B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_50,plain,
    ( k9_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_100,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_44,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k9_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_116,plain,(
    k9_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_44])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_428,plain,(
    ! [B_69,A_70] :
      ( k7_relat_1(B_69,A_70) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_69),A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_435,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_428])).

tff(c_446,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_435])).

tff(c_32,plain,(
    ! [B_23,A_22] :
      ( k2_relat_1(k7_relat_1(B_23,A_22)) = k9_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_453,plain,
    ( k9_relat_1('#skF_4','#skF_3') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_32])).

tff(c_460,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34,c_453])).

tff(c_462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_460])).

tff(c_464,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1111,plain,
    ( k7_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1100,c_464])).

tff(c_1124,plain,(
    k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1111])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k7_relat_1(A_17,B_18))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_463,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_790,plain,(
    ! [B_117,A_118] :
      ( k2_relat_1(k7_relat_1(B_117,A_118)) = k9_relat_1(B_117,A_118)
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_30,plain,(
    ! [A_21] :
      ( k8_relat_1(k2_relat_1(A_21),A_21) = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1553,plain,(
    ! [B_175,A_176] :
      ( k8_relat_1(k9_relat_1(B_175,A_176),k7_relat_1(B_175,A_176)) = k7_relat_1(B_175,A_176)
      | ~ v1_relat_1(k7_relat_1(B_175,A_176))
      | ~ v1_relat_1(B_175) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_790,c_30])).

tff(c_1583,plain,
    ( k8_relat_1(k1_xboole_0,k7_relat_1('#skF_4','#skF_3')) = k7_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_1553])).

tff(c_1597,plain,
    ( k8_relat_1(k1_xboole_0,k7_relat_1('#skF_4','#skF_3')) = k7_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1583])).

tff(c_1739,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1597])).

tff(c_1742,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_1739])).

tff(c_1746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1742])).

tff(c_1748,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1597])).

tff(c_12,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_766,plain,(
    ! [A_112,B_113,C_114] :
      ( ~ r1_xboole_0(A_112,B_113)
      | ~ r2_hidden(C_114,k3_xboole_0(A_112,B_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_802,plain,(
    ! [A_119,B_120,A_121] :
      ( ~ r1_xboole_0(A_119,B_120)
      | r1_xboole_0(A_121,k3_xboole_0(A_119,B_120)) ) ),
    inference(resolution,[status(thm)],[c_4,c_766])).

tff(c_16,plain,(
    ! [A_12] :
      ( ~ r1_xboole_0(A_12,A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_808,plain,(
    ! [A_122,B_123] :
      ( k3_xboole_0(A_122,B_123) = k1_xboole_0
      | ~ r1_xboole_0(A_122,B_123) ) ),
    inference(resolution,[status(thm)],[c_802,c_16])).

tff(c_816,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_808])).

tff(c_20,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1146,plain,(
    ! [B_149,A_150] :
      ( k3_xboole_0(B_149,k2_zfmisc_1(k1_relat_1(B_149),A_150)) = k8_relat_1(A_150,B_149)
      | ~ v1_relat_1(B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1190,plain,(
    ! [B_149] :
      ( k8_relat_1(k1_xboole_0,B_149) = k3_xboole_0(B_149,k1_xboole_0)
      | ~ v1_relat_1(B_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1146])).

tff(c_1200,plain,(
    ! [B_149] :
      ( k8_relat_1(k1_xboole_0,B_149) = k1_xboole_0
      | ~ v1_relat_1(B_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_1190])).

tff(c_1755,plain,(
    k8_relat_1(k1_xboole_0,k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1748,c_1200])).

tff(c_1747,plain,(
    k8_relat_1(k1_xboole_0,k7_relat_1('#skF_4','#skF_3')) = k7_relat_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1597])).

tff(c_1910,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1755,c_1747])).

tff(c_1911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1124,c_1910])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:52:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.50  
% 3.19/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.50  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.19/1.50  
% 3.19/1.50  %Foreground sorts:
% 3.19/1.50  
% 3.19/1.50  
% 3.19/1.50  %Background operators:
% 3.19/1.50  
% 3.19/1.50  
% 3.19/1.50  %Foreground operators:
% 3.19/1.50  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.19/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.19/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.19/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.19/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.19/1.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.19/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.19/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.19/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.19/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.19/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.19/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.19/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.19/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.19/1.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.19/1.50  
% 3.19/1.51  tff(f_111, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 3.19/1.51  tff(f_104, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 3.19/1.51  tff(f_98, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.19/1.51  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.19/1.51  tff(f_83, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.19/1.51  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_relat_1)).
% 3.19/1.51  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.19/1.51  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.19/1.51  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.19/1.51  tff(f_71, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.19/1.51  tff(f_77, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.19/1.51  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_relat_1)).
% 3.19/1.51  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.19/1.51  tff(c_1100, plain, (![B_147, A_148]: (r1_xboole_0(k1_relat_1(B_147), A_148) | k7_relat_1(B_147, A_148)!=k1_xboole_0 | ~v1_relat_1(B_147))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.19/1.51  tff(c_50, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.19/1.51  tff(c_100, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 3.19/1.51  tff(c_44, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.19/1.51  tff(c_116, plain, (k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_100, c_44])).
% 3.19/1.51  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.19/1.51  tff(c_428, plain, (![B_69, A_70]: (k7_relat_1(B_69, A_70)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_69), A_70) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.19/1.51  tff(c_435, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_428])).
% 3.19/1.51  tff(c_446, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_435])).
% 3.19/1.51  tff(c_32, plain, (![B_23, A_22]: (k2_relat_1(k7_relat_1(B_23, A_22))=k9_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.19/1.51  tff(c_453, plain, (k9_relat_1('#skF_4', '#skF_3')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_446, c_32])).
% 3.19/1.51  tff(c_460, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34, c_453])).
% 3.19/1.51  tff(c_462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_460])).
% 3.19/1.51  tff(c_464, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 3.19/1.51  tff(c_1111, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1100, c_464])).
% 3.19/1.51  tff(c_1124, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1111])).
% 3.19/1.51  tff(c_26, plain, (![A_17, B_18]: (v1_relat_1(k7_relat_1(A_17, B_18)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.19/1.51  tff(c_463, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 3.19/1.51  tff(c_790, plain, (![B_117, A_118]: (k2_relat_1(k7_relat_1(B_117, A_118))=k9_relat_1(B_117, A_118) | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.19/1.51  tff(c_30, plain, (![A_21]: (k8_relat_1(k2_relat_1(A_21), A_21)=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.19/1.51  tff(c_1553, plain, (![B_175, A_176]: (k8_relat_1(k9_relat_1(B_175, A_176), k7_relat_1(B_175, A_176))=k7_relat_1(B_175, A_176) | ~v1_relat_1(k7_relat_1(B_175, A_176)) | ~v1_relat_1(B_175))), inference(superposition, [status(thm), theory('equality')], [c_790, c_30])).
% 3.19/1.51  tff(c_1583, plain, (k8_relat_1(k1_xboole_0, k7_relat_1('#skF_4', '#skF_3'))=k7_relat_1('#skF_4', '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_463, c_1553])).
% 3.19/1.51  tff(c_1597, plain, (k8_relat_1(k1_xboole_0, k7_relat_1('#skF_4', '#skF_3'))=k7_relat_1('#skF_4', '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1583])).
% 3.19/1.51  tff(c_1739, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1597])).
% 3.19/1.51  tff(c_1742, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_1739])).
% 3.19/1.51  tff(c_1746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_1742])).
% 3.19/1.51  tff(c_1748, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_1597])).
% 3.19/1.51  tff(c_12, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.19/1.51  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.19/1.51  tff(c_766, plain, (![A_112, B_113, C_114]: (~r1_xboole_0(A_112, B_113) | ~r2_hidden(C_114, k3_xboole_0(A_112, B_113)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.19/1.51  tff(c_802, plain, (![A_119, B_120, A_121]: (~r1_xboole_0(A_119, B_120) | r1_xboole_0(A_121, k3_xboole_0(A_119, B_120)))), inference(resolution, [status(thm)], [c_4, c_766])).
% 3.19/1.51  tff(c_16, plain, (![A_12]: (~r1_xboole_0(A_12, A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.19/1.51  tff(c_808, plain, (![A_122, B_123]: (k3_xboole_0(A_122, B_123)=k1_xboole_0 | ~r1_xboole_0(A_122, B_123))), inference(resolution, [status(thm)], [c_802, c_16])).
% 3.19/1.51  tff(c_816, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_808])).
% 3.19/1.51  tff(c_20, plain, (![A_13]: (k2_zfmisc_1(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.19/1.51  tff(c_1146, plain, (![B_149, A_150]: (k3_xboole_0(B_149, k2_zfmisc_1(k1_relat_1(B_149), A_150))=k8_relat_1(A_150, B_149) | ~v1_relat_1(B_149))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.19/1.51  tff(c_1190, plain, (![B_149]: (k8_relat_1(k1_xboole_0, B_149)=k3_xboole_0(B_149, k1_xboole_0) | ~v1_relat_1(B_149))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1146])).
% 3.19/1.51  tff(c_1200, plain, (![B_149]: (k8_relat_1(k1_xboole_0, B_149)=k1_xboole_0 | ~v1_relat_1(B_149))), inference(demodulation, [status(thm), theory('equality')], [c_816, c_1190])).
% 3.19/1.51  tff(c_1755, plain, (k8_relat_1(k1_xboole_0, k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1748, c_1200])).
% 3.19/1.51  tff(c_1747, plain, (k8_relat_1(k1_xboole_0, k7_relat_1('#skF_4', '#skF_3'))=k7_relat_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_1597])).
% 3.19/1.51  tff(c_1910, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1755, c_1747])).
% 3.19/1.51  tff(c_1911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1124, c_1910])).
% 3.19/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.51  
% 3.19/1.51  Inference rules
% 3.19/1.51  ----------------------
% 3.19/1.51  #Ref     : 0
% 3.19/1.51  #Sup     : 417
% 3.19/1.51  #Fact    : 0
% 3.19/1.51  #Define  : 0
% 3.19/1.51  #Split   : 4
% 3.19/1.51  #Chain   : 0
% 3.19/1.51  #Close   : 0
% 3.19/1.51  
% 3.19/1.51  Ordering : KBO
% 3.19/1.51  
% 3.19/1.51  Simplification rules
% 3.19/1.51  ----------------------
% 3.19/1.51  #Subsume      : 54
% 3.19/1.51  #Demod        : 295
% 3.19/1.51  #Tautology    : 265
% 3.19/1.51  #SimpNegUnit  : 14
% 3.19/1.51  #BackRed      : 0
% 3.19/1.51  
% 3.19/1.51  #Partial instantiations: 0
% 3.19/1.51  #Strategies tried      : 1
% 3.19/1.51  
% 3.19/1.51  Timing (in seconds)
% 3.19/1.52  ----------------------
% 3.19/1.52  Preprocessing        : 0.30
% 3.19/1.52  Parsing              : 0.17
% 3.19/1.52  CNF conversion       : 0.02
% 3.19/1.52  Main loop            : 0.46
% 3.19/1.52  Inferencing          : 0.18
% 3.19/1.52  Reduction            : 0.14
% 3.19/1.52  Demodulation         : 0.10
% 3.19/1.52  BG Simplification    : 0.02
% 3.19/1.52  Subsumption          : 0.09
% 3.19/1.52  Abstraction          : 0.02
% 3.19/1.52  MUC search           : 0.00
% 3.19/1.52  Cooper               : 0.00
% 3.19/1.52  Total                : 0.80
% 3.19/1.52  Index Insertion      : 0.00
% 3.19/1.52  Index Deletion       : 0.00
% 3.19/1.52  Index Matching       : 0.00
% 3.19/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
