%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:52 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 109 expanded)
%              Number of leaves         :   29 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :   99 ( 198 expanded)
%              Number of equality atoms :   14 (  33 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
       => ~ ( r2_hidden(A,D)
            & ! [E,F] :
                ~ ( A = k4_tarski(E,F)
                  & r2_hidden(E,B)
                  & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_57,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_40,plain,(
    r2_hidden('#skF_5','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_322,plain,(
    ! [A_89,B_90,C_91] :
      ( k4_tarski('#skF_3'(A_89,B_90,C_91),'#skF_4'(A_89,B_90,C_91)) = A_89
      | ~ r2_hidden(A_89,k2_zfmisc_1(B_90,C_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    ! [A_21] : ~ v1_xboole_0(k1_zfmisc_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_66,plain,(
    ! [A_44,B_45] :
      ( r2_hidden(A_44,B_45)
      | v1_xboole_0(B_45)
      | ~ m1_subset_1(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    ! [A_20] : k3_tarski(k1_zfmisc_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_53,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,k3_tarski(B_31))
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_56,plain,(
    ! [A_30,A_20] :
      ( r1_tarski(A_30,A_20)
      | ~ r2_hidden(A_30,k1_zfmisc_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_53])).

tff(c_81,plain,(
    ! [A_44,A_20] :
      ( r1_tarski(A_44,A_20)
      | v1_xboole_0(k1_zfmisc_1(A_20))
      | ~ m1_subset_1(A_44,k1_zfmisc_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_66,c_56])).

tff(c_88,plain,(
    ! [A_46,A_47] :
      ( r1_tarski(A_46,A_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(A_47)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_81])).

tff(c_92,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_42,c_88])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_96,plain,(
    k3_xboole_0('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_92,c_20])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_103,plain,(
    ! [D_6] :
      ( r2_hidden(D_6,k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(D_6,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_4])).

tff(c_156,plain,(
    ! [A_61,C_62,B_63,D_64] :
      ( r2_hidden(A_61,C_62)
      | ~ r2_hidden(k4_tarski(A_61,B_63),k2_zfmisc_1(C_62,D_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_164,plain,(
    ! [A_61,B_63] :
      ( r2_hidden(A_61,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_61,B_63),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_103,c_156])).

tff(c_331,plain,(
    ! [A_89,B_90,C_91] :
      ( r2_hidden('#skF_3'(A_89,B_90,C_91),'#skF_6')
      | ~ r2_hidden(A_89,'#skF_8')
      | ~ r2_hidden(A_89,k2_zfmisc_1(B_90,C_91)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_164])).

tff(c_22,plain,(
    ! [A_9,B_10,C_11] :
      ( k4_tarski('#skF_3'(A_9,B_10,C_11),'#skF_4'(A_9,B_10,C_11)) = A_9
      | ~ r2_hidden(A_9,k2_zfmisc_1(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ! [A_22,B_23] :
      ( r2_hidden(A_22,B_23)
      | v1_xboole_0(B_23)
      | ~ m1_subset_1(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,k3_tarski(B_15))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_57,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = A_32
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_107,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,k3_tarski(B_49)) = A_48
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_24,c_57])).

tff(c_176,plain,(
    ! [D_69,B_70,A_71] :
      ( r2_hidden(D_69,k3_tarski(B_70))
      | ~ r2_hidden(D_69,A_71)
      | ~ r2_hidden(A_71,B_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_4])).

tff(c_204,plain,(
    ! [B_75] :
      ( r2_hidden('#skF_5',k3_tarski(B_75))
      | ~ r2_hidden('#skF_8',B_75) ) ),
    inference(resolution,[status(thm)],[c_40,c_176])).

tff(c_211,plain,(
    ! [A_76] :
      ( r2_hidden('#skF_5',A_76)
      | ~ r2_hidden('#skF_8',k1_zfmisc_1(A_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_204])).

tff(c_214,plain,(
    ! [A_76] :
      ( r2_hidden('#skF_5',A_76)
      | v1_xboole_0(k1_zfmisc_1(A_76))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_76)) ) ),
    inference(resolution,[status(thm)],[c_36,c_211])).

tff(c_218,plain,(
    ! [A_77] :
      ( r2_hidden('#skF_5',A_77)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_77)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_214])).

tff(c_222,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_42,c_218])).

tff(c_28,plain,(
    ! [B_17,D_19,A_16,C_18] :
      ( r2_hidden(B_17,D_19)
      | ~ r2_hidden(k4_tarski(A_16,B_17),k2_zfmisc_1(C_18,D_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1526,plain,(
    ! [C_244,A_246,B_245,C_248,D_247] :
      ( r2_hidden('#skF_4'(A_246,B_245,C_244),D_247)
      | ~ r2_hidden(A_246,k2_zfmisc_1(C_248,D_247))
      | ~ r2_hidden(A_246,k2_zfmisc_1(B_245,C_244)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_28])).

tff(c_1580,plain,(
    ! [B_249,C_250] :
      ( r2_hidden('#skF_4'('#skF_5',B_249,C_250),'#skF_7')
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_249,C_250)) ) ),
    inference(resolution,[status(thm)],[c_222,c_1526])).

tff(c_38,plain,(
    ! [F_27,E_26] :
      ( ~ r2_hidden(F_27,'#skF_7')
      | ~ r2_hidden(E_26,'#skF_6')
      | k4_tarski(E_26,F_27) != '#skF_5' ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1606,plain,(
    ! [E_254,B_255,C_256] :
      ( ~ r2_hidden(E_254,'#skF_6')
      | k4_tarski(E_254,'#skF_4'('#skF_5',B_255,C_256)) != '#skF_5'
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_255,C_256)) ) ),
    inference(resolution,[status(thm)],[c_1580,c_38])).

tff(c_1611,plain,(
    ! [B_257,C_258] :
      ( ~ r2_hidden('#skF_3'('#skF_5',B_257,C_258),'#skF_6')
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_257,C_258)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1606])).

tff(c_1615,plain,(
    ! [B_90,C_91] :
      ( ~ r2_hidden('#skF_5','#skF_8')
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_90,C_91)) ) ),
    inference(resolution,[status(thm)],[c_331,c_1611])).

tff(c_1624,plain,(
    ! [B_90,C_91] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_90,C_91)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1615])).

tff(c_1628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1624,c_222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.12/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.77  
% 4.12/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.77  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3
% 4.12/1.77  
% 4.12/1.77  %Foreground sorts:
% 4.12/1.77  
% 4.12/1.77  
% 4.12/1.77  %Background operators:
% 4.12/1.77  
% 4.12/1.77  
% 4.12/1.77  %Foreground operators:
% 4.12/1.77  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.12/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.12/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.12/1.77  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.12/1.77  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.12/1.77  tff('#skF_7', type, '#skF_7': $i).
% 4.12/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.12/1.77  tff('#skF_5', type, '#skF_5': $i).
% 4.12/1.77  tff('#skF_6', type, '#skF_6': $i).
% 4.12/1.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.12/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.12/1.77  tff('#skF_8', type, '#skF_8': $i).
% 4.12/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.12/1.77  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.12/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.12/1.77  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.12/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.12/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.12/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.12/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.12/1.77  
% 4.12/1.78  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_relset_1)).
% 4.12/1.78  tff(f_45, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 4.12/1.78  tff(f_60, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.12/1.78  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.12/1.78  tff(f_57, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 4.12/1.78  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 4.12/1.78  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.12/1.78  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.12/1.78  tff(f_55, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.12/1.78  tff(c_40, plain, (r2_hidden('#skF_5', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.12/1.78  tff(c_322, plain, (![A_89, B_90, C_91]: (k4_tarski('#skF_3'(A_89, B_90, C_91), '#skF_4'(A_89, B_90, C_91))=A_89 | ~r2_hidden(A_89, k2_zfmisc_1(B_90, C_91)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.12/1.78  tff(c_42, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.12/1.78  tff(c_34, plain, (![A_21]: (~v1_xboole_0(k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.12/1.78  tff(c_66, plain, (![A_44, B_45]: (r2_hidden(A_44, B_45) | v1_xboole_0(B_45) | ~m1_subset_1(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.12/1.78  tff(c_32, plain, (![A_20]: (k3_tarski(k1_zfmisc_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.12/1.78  tff(c_53, plain, (![A_30, B_31]: (r1_tarski(A_30, k3_tarski(B_31)) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.12/1.78  tff(c_56, plain, (![A_30, A_20]: (r1_tarski(A_30, A_20) | ~r2_hidden(A_30, k1_zfmisc_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_53])).
% 4.12/1.78  tff(c_81, plain, (![A_44, A_20]: (r1_tarski(A_44, A_20) | v1_xboole_0(k1_zfmisc_1(A_20)) | ~m1_subset_1(A_44, k1_zfmisc_1(A_20)))), inference(resolution, [status(thm)], [c_66, c_56])).
% 4.12/1.78  tff(c_88, plain, (![A_46, A_47]: (r1_tarski(A_46, A_47) | ~m1_subset_1(A_46, k1_zfmisc_1(A_47)))), inference(negUnitSimplification, [status(thm)], [c_34, c_81])).
% 4.12/1.78  tff(c_92, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_42, c_88])).
% 4.12/1.78  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.12/1.78  tff(c_96, plain, (k3_xboole_0('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))='#skF_8'), inference(resolution, [status(thm)], [c_92, c_20])).
% 4.12/1.78  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.12/1.78  tff(c_103, plain, (![D_6]: (r2_hidden(D_6, k2_zfmisc_1('#skF_6', '#skF_7')) | ~r2_hidden(D_6, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_4])).
% 4.12/1.78  tff(c_156, plain, (![A_61, C_62, B_63, D_64]: (r2_hidden(A_61, C_62) | ~r2_hidden(k4_tarski(A_61, B_63), k2_zfmisc_1(C_62, D_64)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.12/1.78  tff(c_164, plain, (![A_61, B_63]: (r2_hidden(A_61, '#skF_6') | ~r2_hidden(k4_tarski(A_61, B_63), '#skF_8'))), inference(resolution, [status(thm)], [c_103, c_156])).
% 4.12/1.78  tff(c_331, plain, (![A_89, B_90, C_91]: (r2_hidden('#skF_3'(A_89, B_90, C_91), '#skF_6') | ~r2_hidden(A_89, '#skF_8') | ~r2_hidden(A_89, k2_zfmisc_1(B_90, C_91)))), inference(superposition, [status(thm), theory('equality')], [c_322, c_164])).
% 4.12/1.78  tff(c_22, plain, (![A_9, B_10, C_11]: (k4_tarski('#skF_3'(A_9, B_10, C_11), '#skF_4'(A_9, B_10, C_11))=A_9 | ~r2_hidden(A_9, k2_zfmisc_1(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.12/1.78  tff(c_36, plain, (![A_22, B_23]: (r2_hidden(A_22, B_23) | v1_xboole_0(B_23) | ~m1_subset_1(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.12/1.78  tff(c_24, plain, (![A_14, B_15]: (r1_tarski(A_14, k3_tarski(B_15)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.12/1.78  tff(c_57, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=A_32 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.12/1.78  tff(c_107, plain, (![A_48, B_49]: (k3_xboole_0(A_48, k3_tarski(B_49))=A_48 | ~r2_hidden(A_48, B_49))), inference(resolution, [status(thm)], [c_24, c_57])).
% 4.12/1.78  tff(c_176, plain, (![D_69, B_70, A_71]: (r2_hidden(D_69, k3_tarski(B_70)) | ~r2_hidden(D_69, A_71) | ~r2_hidden(A_71, B_70))), inference(superposition, [status(thm), theory('equality')], [c_107, c_4])).
% 4.12/1.78  tff(c_204, plain, (![B_75]: (r2_hidden('#skF_5', k3_tarski(B_75)) | ~r2_hidden('#skF_8', B_75))), inference(resolution, [status(thm)], [c_40, c_176])).
% 4.12/1.78  tff(c_211, plain, (![A_76]: (r2_hidden('#skF_5', A_76) | ~r2_hidden('#skF_8', k1_zfmisc_1(A_76)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_204])).
% 4.12/1.78  tff(c_214, plain, (![A_76]: (r2_hidden('#skF_5', A_76) | v1_xboole_0(k1_zfmisc_1(A_76)) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_76)))), inference(resolution, [status(thm)], [c_36, c_211])).
% 4.12/1.78  tff(c_218, plain, (![A_77]: (r2_hidden('#skF_5', A_77) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_77)))), inference(negUnitSimplification, [status(thm)], [c_34, c_214])).
% 4.12/1.78  tff(c_222, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_42, c_218])).
% 4.12/1.78  tff(c_28, plain, (![B_17, D_19, A_16, C_18]: (r2_hidden(B_17, D_19) | ~r2_hidden(k4_tarski(A_16, B_17), k2_zfmisc_1(C_18, D_19)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.12/1.78  tff(c_1526, plain, (![C_244, A_246, B_245, C_248, D_247]: (r2_hidden('#skF_4'(A_246, B_245, C_244), D_247) | ~r2_hidden(A_246, k2_zfmisc_1(C_248, D_247)) | ~r2_hidden(A_246, k2_zfmisc_1(B_245, C_244)))), inference(superposition, [status(thm), theory('equality')], [c_322, c_28])).
% 4.12/1.78  tff(c_1580, plain, (![B_249, C_250]: (r2_hidden('#skF_4'('#skF_5', B_249, C_250), '#skF_7') | ~r2_hidden('#skF_5', k2_zfmisc_1(B_249, C_250)))), inference(resolution, [status(thm)], [c_222, c_1526])).
% 4.12/1.78  tff(c_38, plain, (![F_27, E_26]: (~r2_hidden(F_27, '#skF_7') | ~r2_hidden(E_26, '#skF_6') | k4_tarski(E_26, F_27)!='#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.12/1.78  tff(c_1606, plain, (![E_254, B_255, C_256]: (~r2_hidden(E_254, '#skF_6') | k4_tarski(E_254, '#skF_4'('#skF_5', B_255, C_256))!='#skF_5' | ~r2_hidden('#skF_5', k2_zfmisc_1(B_255, C_256)))), inference(resolution, [status(thm)], [c_1580, c_38])).
% 4.12/1.78  tff(c_1611, plain, (![B_257, C_258]: (~r2_hidden('#skF_3'('#skF_5', B_257, C_258), '#skF_6') | ~r2_hidden('#skF_5', k2_zfmisc_1(B_257, C_258)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1606])).
% 4.12/1.78  tff(c_1615, plain, (![B_90, C_91]: (~r2_hidden('#skF_5', '#skF_8') | ~r2_hidden('#skF_5', k2_zfmisc_1(B_90, C_91)))), inference(resolution, [status(thm)], [c_331, c_1611])).
% 4.12/1.78  tff(c_1624, plain, (![B_90, C_91]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_90, C_91)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1615])).
% 4.12/1.78  tff(c_1628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1624, c_222])).
% 4.12/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.78  
% 4.12/1.78  Inference rules
% 4.12/1.78  ----------------------
% 4.12/1.78  #Ref     : 0
% 4.12/1.78  #Sup     : 366
% 4.12/1.78  #Fact    : 0
% 4.12/1.78  #Define  : 0
% 4.12/1.78  #Split   : 10
% 4.12/1.78  #Chain   : 0
% 4.12/1.78  #Close   : 0
% 4.12/1.78  
% 4.12/1.78  Ordering : KBO
% 4.12/1.78  
% 4.12/1.78  Simplification rules
% 4.12/1.78  ----------------------
% 4.12/1.78  #Subsume      : 37
% 4.12/1.78  #Demod        : 23
% 4.12/1.78  #Tautology    : 38
% 4.12/1.78  #SimpNegUnit  : 19
% 4.12/1.78  #BackRed      : 1
% 4.12/1.78  
% 4.12/1.78  #Partial instantiations: 0
% 4.12/1.78  #Strategies tried      : 1
% 4.12/1.78  
% 4.12/1.78  Timing (in seconds)
% 4.12/1.79  ----------------------
% 4.12/1.79  Preprocessing        : 0.33
% 4.12/1.79  Parsing              : 0.17
% 4.12/1.79  CNF conversion       : 0.03
% 4.12/1.79  Main loop            : 0.65
% 4.12/1.79  Inferencing          : 0.23
% 4.12/1.79  Reduction            : 0.16
% 4.12/1.79  Demodulation         : 0.10
% 4.12/1.79  BG Simplification    : 0.03
% 4.12/1.79  Subsumption          : 0.17
% 4.12/1.79  Abstraction          : 0.03
% 4.12/1.79  MUC search           : 0.00
% 4.12/1.79  Cooper               : 0.00
% 4.12/1.79  Total                : 1.01
% 4.12/1.79  Index Insertion      : 0.00
% 4.12/1.79  Index Deletion       : 0.00
% 4.12/1.79  Index Matching       : 0.00
% 4.12/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
