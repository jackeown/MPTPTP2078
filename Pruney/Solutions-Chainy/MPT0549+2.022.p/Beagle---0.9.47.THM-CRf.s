%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:51 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 115 expanded)
%              Number of leaves         :   31 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 186 expanded)
%              Number of equality atoms :   40 (  77 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_76,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_396,plain,(
    ! [B_77,A_78] :
      ( r1_xboole_0(k1_relat_1(B_77),A_78)
      | k7_relat_1(B_77,A_78) != k1_xboole_0
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k9_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_88,plain,(
    k9_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_42,plain,
    ( k9_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_99,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_42])).

tff(c_166,plain,(
    ! [B_42,A_43] :
      ( k7_relat_1(B_42,A_43) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_42),A_43)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_169,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_99,c_166])).

tff(c_179,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_169])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(k7_relat_1(B_19,A_18)) = k9_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_184,plain,
    ( k9_relat_1('#skF_4','#skF_3') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_24])).

tff(c_191,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_26,c_184])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_191])).

tff(c_194,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_402,plain,
    ( k7_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_396,c_194])).

tff(c_409,plain,(
    k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_402])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k7_relat_1(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_195,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_384,plain,(
    ! [B_75,A_76] :
      ( k2_relat_1(k7_relat_1(B_75,A_76)) = k9_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    ! [A_17] :
      ( k8_relat_1(k2_relat_1(A_17),A_17) = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_733,plain,(
    ! [B_104,A_105] :
      ( k8_relat_1(k9_relat_1(B_104,A_105),k7_relat_1(B_104,A_105)) = k7_relat_1(B_104,A_105)
      | ~ v1_relat_1(k7_relat_1(B_104,A_105))
      | ~ v1_relat_1(B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_22])).

tff(c_760,plain,
    ( k8_relat_1(k1_xboole_0,k7_relat_1('#skF_4','#skF_3')) = k7_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_733])).

tff(c_773,plain,
    ( k8_relat_1(k1_xboole_0,k7_relat_1('#skF_4','#skF_3')) = k7_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_760])).

tff(c_794,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_773])).

tff(c_797,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_794])).

tff(c_801,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_797])).

tff(c_803,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_773])).

tff(c_8,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_343,plain,(
    ! [A_66,B_67,C_68] :
      ( ~ r1_xboole_0(A_66,B_67)
      | ~ r2_hidden(C_68,k3_xboole_0(A_66,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_349,plain,(
    ! [A_69,B_70] :
      ( ~ r1_xboole_0(A_69,B_70)
      | k3_xboole_0(A_69,B_70) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_343])).

tff(c_353,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_349])).

tff(c_12,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_443,plain,(
    ! [B_85,A_86] :
      ( k3_xboole_0(B_85,k2_zfmisc_1(k1_relat_1(B_85),A_86)) = k8_relat_1(A_86,B_85)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_459,plain,(
    ! [B_85] :
      ( k8_relat_1(k1_xboole_0,B_85) = k3_xboole_0(B_85,k1_xboole_0)
      | ~ v1_relat_1(B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_443])).

tff(c_465,plain,(
    ! [B_85] :
      ( k8_relat_1(k1_xboole_0,B_85) = k1_xboole_0
      | ~ v1_relat_1(B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_459])).

tff(c_810,plain,(
    k8_relat_1(k1_xboole_0,k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_803,c_465])).

tff(c_802,plain,(
    k8_relat_1(k1_xboole_0,k7_relat_1('#skF_4','#skF_3')) = k7_relat_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_773])).

tff(c_900,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_802])).

tff(c_901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_409,c_900])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:17:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.35  
% 2.49/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.36  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.49/1.36  
% 2.49/1.36  %Foreground sorts:
% 2.49/1.36  
% 2.49/1.36  
% 2.49/1.36  %Background operators:
% 2.49/1.36  
% 2.49/1.36  
% 2.49/1.36  %Foreground operators:
% 2.49/1.36  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.49/1.36  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.49/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.49/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.49/1.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.49/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.49/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.49/1.36  
% 2.71/1.37  tff(f_89, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 2.71/1.37  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.71/1.37  tff(f_76, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.71/1.37  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.71/1.37  tff(f_61, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.71/1.37  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_relat_1)).
% 2.71/1.37  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.71/1.37  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.71/1.37  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.71/1.37  tff(f_55, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.71/1.37  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_relat_1)).
% 2.71/1.37  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.71/1.37  tff(c_396, plain, (![B_77, A_78]: (r1_xboole_0(k1_relat_1(B_77), A_78) | k7_relat_1(B_77, A_78)!=k1_xboole_0 | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.71/1.37  tff(c_36, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.71/1.37  tff(c_88, plain, (k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 2.71/1.37  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.71/1.37  tff(c_42, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.71/1.37  tff(c_99, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_88, c_42])).
% 2.71/1.37  tff(c_166, plain, (![B_42, A_43]: (k7_relat_1(B_42, A_43)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_42), A_43) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.71/1.37  tff(c_169, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_99, c_166])).
% 2.71/1.37  tff(c_179, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_169])).
% 2.71/1.37  tff(c_24, plain, (![B_19, A_18]: (k2_relat_1(k7_relat_1(B_19, A_18))=k9_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.71/1.37  tff(c_184, plain, (k9_relat_1('#skF_4', '#skF_3')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_179, c_24])).
% 2.71/1.37  tff(c_191, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_26, c_184])).
% 2.71/1.37  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_191])).
% 2.71/1.37  tff(c_194, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 2.71/1.37  tff(c_402, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_396, c_194])).
% 2.71/1.37  tff(c_409, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_402])).
% 2.71/1.37  tff(c_18, plain, (![A_13, B_14]: (v1_relat_1(k7_relat_1(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.71/1.37  tff(c_195, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.71/1.37  tff(c_384, plain, (![B_75, A_76]: (k2_relat_1(k7_relat_1(B_75, A_76))=k9_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.71/1.37  tff(c_22, plain, (![A_17]: (k8_relat_1(k2_relat_1(A_17), A_17)=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.71/1.37  tff(c_733, plain, (![B_104, A_105]: (k8_relat_1(k9_relat_1(B_104, A_105), k7_relat_1(B_104, A_105))=k7_relat_1(B_104, A_105) | ~v1_relat_1(k7_relat_1(B_104, A_105)) | ~v1_relat_1(B_104))), inference(superposition, [status(thm), theory('equality')], [c_384, c_22])).
% 2.71/1.37  tff(c_760, plain, (k8_relat_1(k1_xboole_0, k7_relat_1('#skF_4', '#skF_3'))=k7_relat_1('#skF_4', '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_195, c_733])).
% 2.71/1.37  tff(c_773, plain, (k8_relat_1(k1_xboole_0, k7_relat_1('#skF_4', '#skF_3'))=k7_relat_1('#skF_4', '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_760])).
% 2.71/1.37  tff(c_794, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_773])).
% 2.71/1.37  tff(c_797, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_794])).
% 2.71/1.37  tff(c_801, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_797])).
% 2.71/1.37  tff(c_803, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_773])).
% 2.71/1.37  tff(c_8, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.71/1.37  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.71/1.37  tff(c_343, plain, (![A_66, B_67, C_68]: (~r1_xboole_0(A_66, B_67) | ~r2_hidden(C_68, k3_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.71/1.37  tff(c_349, plain, (![A_69, B_70]: (~r1_xboole_0(A_69, B_70) | k3_xboole_0(A_69, B_70)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_343])).
% 2.71/1.37  tff(c_353, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_349])).
% 2.71/1.37  tff(c_12, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.71/1.37  tff(c_443, plain, (![B_85, A_86]: (k3_xboole_0(B_85, k2_zfmisc_1(k1_relat_1(B_85), A_86))=k8_relat_1(A_86, B_85) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.71/1.37  tff(c_459, plain, (![B_85]: (k8_relat_1(k1_xboole_0, B_85)=k3_xboole_0(B_85, k1_xboole_0) | ~v1_relat_1(B_85))), inference(superposition, [status(thm), theory('equality')], [c_12, c_443])).
% 2.71/1.37  tff(c_465, plain, (![B_85]: (k8_relat_1(k1_xboole_0, B_85)=k1_xboole_0 | ~v1_relat_1(B_85))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_459])).
% 2.71/1.37  tff(c_810, plain, (k8_relat_1(k1_xboole_0, k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_803, c_465])).
% 2.71/1.37  tff(c_802, plain, (k8_relat_1(k1_xboole_0, k7_relat_1('#skF_4', '#skF_3'))=k7_relat_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_773])).
% 2.71/1.37  tff(c_900, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_810, c_802])).
% 2.71/1.37  tff(c_901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_409, c_900])).
% 2.71/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.37  
% 2.71/1.37  Inference rules
% 2.71/1.37  ----------------------
% 2.71/1.37  #Ref     : 0
% 2.71/1.37  #Sup     : 194
% 2.71/1.37  #Fact    : 0
% 2.71/1.37  #Define  : 0
% 2.71/1.37  #Split   : 4
% 2.71/1.37  #Chain   : 0
% 2.71/1.37  #Close   : 0
% 2.71/1.37  
% 2.71/1.37  Ordering : KBO
% 2.71/1.37  
% 2.71/1.37  Simplification rules
% 2.71/1.37  ----------------------
% 2.71/1.37  #Subsume      : 16
% 2.71/1.37  #Demod        : 130
% 2.71/1.37  #Tautology    : 127
% 2.71/1.37  #SimpNegUnit  : 9
% 2.71/1.37  #BackRed      : 0
% 2.71/1.37  
% 2.71/1.37  #Partial instantiations: 0
% 2.71/1.37  #Strategies tried      : 1
% 2.71/1.37  
% 2.71/1.37  Timing (in seconds)
% 2.71/1.37  ----------------------
% 2.71/1.37  Preprocessing        : 0.29
% 2.71/1.37  Parsing              : 0.16
% 2.71/1.37  CNF conversion       : 0.02
% 2.71/1.37  Main loop            : 0.31
% 2.71/1.37  Inferencing          : 0.13
% 2.71/1.37  Reduction            : 0.09
% 2.71/1.37  Demodulation         : 0.06
% 2.71/1.37  BG Simplification    : 0.02
% 2.71/1.37  Subsumption          : 0.05
% 2.71/1.37  Abstraction          : 0.01
% 2.71/1.37  MUC search           : 0.00
% 2.71/1.37  Cooper               : 0.00
% 2.71/1.37  Total                : 0.63
% 2.71/1.38  Index Insertion      : 0.00
% 2.71/1.38  Index Deletion       : 0.00
% 2.71/1.38  Index Matching       : 0.00
% 2.71/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
