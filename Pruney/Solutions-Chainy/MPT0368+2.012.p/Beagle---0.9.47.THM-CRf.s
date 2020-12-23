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
% DateTime   : Thu Dec  3 09:56:49 EST 2020

% Result     : Theorem 5.04s
% Output     : CNFRefutation 5.26s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 176 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  132 ( 397 expanded)
%              Number of equality atoms :    7 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(c_1722,plain,(
    ! [B_231,A_232] :
      ( m1_subset_1(B_231,A_232)
      | ~ v1_xboole_0(B_231)
      | ~ v1_xboole_0(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_52,plain,(
    ! [C_32] :
      ( r2_hidden(C_32,'#skF_6')
      | ~ m1_subset_1(C_32,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [C_32] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_32,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_2])).

tff(c_57,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_82,plain,(
    ! [B_46,A_47] :
      ( v1_xboole_0(B_46)
      | ~ m1_subset_1(B_46,A_47)
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_88,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_48,c_82])).

tff(c_92,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_88])).

tff(c_44,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [B_48,A_49] :
      ( m1_subset_1(B_48,A_49)
      | ~ r2_hidden(B_48,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_104,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_93])).

tff(c_46,plain,(
    ! [C_26] :
      ( r2_hidden(C_26,'#skF_6')
      | ~ m1_subset_1(C_26,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_102,plain,(
    ! [C_26] :
      ( m1_subset_1(C_26,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_26,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_93])).

tff(c_113,plain,(
    ! [C_51] :
      ( m1_subset_1(C_51,'#skF_6')
      | ~ m1_subset_1(C_51,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_102])).

tff(c_122,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),'#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_104,c_113])).

tff(c_124,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_196,plain,(
    ! [B_66,A_67] :
      ( r2_hidden(B_66,A_67)
      | ~ m1_subset_1(B_66,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    ! [C_22,A_18] :
      ( r1_tarski(C_22,A_18)
      | ~ r2_hidden(C_22,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1045,plain,(
    ! [B_142,A_143] :
      ( r1_tarski(B_142,A_143)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(A_143))
      | v1_xboole_0(k1_zfmisc_1(A_143)) ) ),
    inference(resolution,[status(thm)],[c_196,c_24])).

tff(c_1065,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_48,c_1045])).

tff(c_1076,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1065])).

tff(c_246,plain,(
    ! [C_74,B_75,A_76] :
      ( r2_hidden(C_74,B_75)
      | ~ r2_hidden(C_74,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_365,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_1'(A_88),B_89)
      | ~ r1_tarski(A_88,B_89)
      | v1_xboole_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_4,c_246])).

tff(c_381,plain,(
    ! [B_89,A_88] :
      ( ~ v1_xboole_0(B_89)
      | ~ r1_tarski(A_88,B_89)
      | v1_xboole_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_365,c_2])).

tff(c_1081,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1076,c_381])).

tff(c_1094,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_1081])).

tff(c_1096,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_1094])).

tff(c_1098,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_1132,plain,(
    ! [A_148,B_149] :
      ( r2_hidden('#skF_2'(A_148,B_149),A_148)
      | r1_tarski(A_148,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36,plain,(
    ! [B_24,A_23] :
      ( m1_subset_1(B_24,A_23)
      | ~ r2_hidden(B_24,A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1521,plain,(
    ! [A_211,B_212] :
      ( m1_subset_1('#skF_2'(A_211,B_212),A_211)
      | v1_xboole_0(A_211)
      | r1_tarski(A_211,B_212) ) ),
    inference(resolution,[status(thm)],[c_1132,c_36])).

tff(c_1147,plain,(
    ! [A_152,B_153] :
      ( ~ r2_hidden('#skF_2'(A_152,B_153),B_153)
      | r1_tarski(A_152,B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1167,plain,(
    ! [A_152] :
      ( r1_tarski(A_152,'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_152,'#skF_6'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_1147])).

tff(c_1529,plain,
    ( v1_xboole_0('#skF_5')
    | r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1521,c_1167])).

tff(c_1542,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1098,c_1529])).

tff(c_1099,plain,(
    ! [A_144,B_145] :
      ( r2_xboole_0(A_144,B_145)
      | B_145 = A_144
      | ~ r1_tarski(A_144,B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( ~ r2_xboole_0(B_17,A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1111,plain,(
    ! [B_145,A_144] :
      ( ~ r1_tarski(B_145,A_144)
      | B_145 = A_144
      | ~ r1_tarski(A_144,B_145) ) ),
    inference(resolution,[status(thm)],[c_1099,c_22])).

tff(c_1560,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_1542,c_1111])).

tff(c_1567,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1560])).

tff(c_1118,plain,(
    ! [B_146,A_147] :
      ( r2_hidden(B_146,A_147)
      | ~ m1_subset_1(B_146,A_147)
      | v1_xboole_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1680,plain,(
    ! [B_223,A_224] :
      ( r1_tarski(B_223,A_224)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(A_224))
      | v1_xboole_0(k1_zfmisc_1(A_224)) ) ),
    inference(resolution,[status(thm)],[c_1118,c_24])).

tff(c_1701,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_48,c_1680])).

tff(c_1711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1567,c_1701])).

tff(c_1712,plain,(
    ! [C_32] : ~ m1_subset_1(C_32,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1727,plain,(
    ! [B_231] :
      ( ~ v1_xboole_0(B_231)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1722,c_1712])).

tff(c_1728,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1727])).

tff(c_1764,plain,(
    ! [B_243,A_244] :
      ( m1_subset_1(B_243,A_244)
      | ~ r2_hidden(B_243,A_244)
      | v1_xboole_0(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1773,plain,(
    ! [A_245] :
      ( m1_subset_1('#skF_1'(A_245),A_245)
      | v1_xboole_0(A_245) ) ),
    inference(resolution,[status(thm)],[c_4,c_1764])).

tff(c_1780,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1773,c_1712])).

tff(c_1785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1728,c_1780])).

tff(c_1786,plain,(
    ! [B_231] : ~ v1_xboole_0(B_231) ),
    inference(splitRight,[status(thm)],[c_1727])).

tff(c_1713,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1786,c_1713])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.04/2.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.04/2.32  
% 5.04/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.04/2.32  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 5.04/2.32  
% 5.04/2.32  %Foreground sorts:
% 5.04/2.32  
% 5.04/2.32  
% 5.04/2.32  %Background operators:
% 5.04/2.32  
% 5.04/2.32  
% 5.04/2.32  %Foreground operators:
% 5.04/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.04/2.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.04/2.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.04/2.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.04/2.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.04/2.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.04/2.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.04/2.32  tff('#skF_5', type, '#skF_5': $i).
% 5.04/2.32  tff('#skF_6', type, '#skF_6': $i).
% 5.04/2.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.04/2.32  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 5.04/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.04/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.04/2.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.04/2.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.04/2.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.04/2.32  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.04/2.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.04/2.32  
% 5.26/2.35  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.26/2.35  tff(f_84, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 5.26/2.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.26/2.35  tff(f_61, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.26/2.35  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.26/2.35  tff(f_45, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 5.26/2.35  tff(f_54, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 5.26/2.35  tff(c_1722, plain, (![B_231, A_232]: (m1_subset_1(B_231, A_232) | ~v1_xboole_0(B_231) | ~v1_xboole_0(A_232))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.26/2.35  tff(c_52, plain, (![C_32]: (r2_hidden(C_32, '#skF_6') | ~m1_subset_1(C_32, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.26/2.35  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.26/2.35  tff(c_56, plain, (![C_32]: (~v1_xboole_0('#skF_6') | ~m1_subset_1(C_32, '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_2])).
% 5.26/2.35  tff(c_57, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_56])).
% 5.26/2.35  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.26/2.35  tff(c_82, plain, (![B_46, A_47]: (v1_xboole_0(B_46) | ~m1_subset_1(B_46, A_47) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.26/2.35  tff(c_88, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_82])).
% 5.26/2.35  tff(c_92, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_57, c_88])).
% 5.26/2.35  tff(c_44, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.26/2.35  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.26/2.35  tff(c_93, plain, (![B_48, A_49]: (m1_subset_1(B_48, A_49) | ~r2_hidden(B_48, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.26/2.35  tff(c_104, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_93])).
% 5.26/2.35  tff(c_46, plain, (![C_26]: (r2_hidden(C_26, '#skF_6') | ~m1_subset_1(C_26, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.26/2.35  tff(c_102, plain, (![C_26]: (m1_subset_1(C_26, '#skF_6') | v1_xboole_0('#skF_6') | ~m1_subset_1(C_26, '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_93])).
% 5.26/2.35  tff(c_113, plain, (![C_51]: (m1_subset_1(C_51, '#skF_6') | ~m1_subset_1(C_51, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_57, c_102])).
% 5.26/2.35  tff(c_122, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_104, c_113])).
% 5.26/2.35  tff(c_124, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_122])).
% 5.26/2.35  tff(c_196, plain, (![B_66, A_67]: (r2_hidden(B_66, A_67) | ~m1_subset_1(B_66, A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.26/2.35  tff(c_24, plain, (![C_22, A_18]: (r1_tarski(C_22, A_18) | ~r2_hidden(C_22, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.26/2.35  tff(c_1045, plain, (![B_142, A_143]: (r1_tarski(B_142, A_143) | ~m1_subset_1(B_142, k1_zfmisc_1(A_143)) | v1_xboole_0(k1_zfmisc_1(A_143)))), inference(resolution, [status(thm)], [c_196, c_24])).
% 5.26/2.35  tff(c_1065, plain, (r1_tarski('#skF_6', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_1045])).
% 5.26/2.35  tff(c_1076, plain, (r1_tarski('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_92, c_1065])).
% 5.26/2.35  tff(c_246, plain, (![C_74, B_75, A_76]: (r2_hidden(C_74, B_75) | ~r2_hidden(C_74, A_76) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.26/2.35  tff(c_365, plain, (![A_88, B_89]: (r2_hidden('#skF_1'(A_88), B_89) | ~r1_tarski(A_88, B_89) | v1_xboole_0(A_88))), inference(resolution, [status(thm)], [c_4, c_246])).
% 5.26/2.35  tff(c_381, plain, (![B_89, A_88]: (~v1_xboole_0(B_89) | ~r1_tarski(A_88, B_89) | v1_xboole_0(A_88))), inference(resolution, [status(thm)], [c_365, c_2])).
% 5.26/2.35  tff(c_1081, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_1076, c_381])).
% 5.26/2.35  tff(c_1094, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_1081])).
% 5.26/2.35  tff(c_1096, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_1094])).
% 5.26/2.35  tff(c_1098, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_122])).
% 5.26/2.35  tff(c_1132, plain, (![A_148, B_149]: (r2_hidden('#skF_2'(A_148, B_149), A_148) | r1_tarski(A_148, B_149))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.26/2.35  tff(c_36, plain, (![B_24, A_23]: (m1_subset_1(B_24, A_23) | ~r2_hidden(B_24, A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.26/2.35  tff(c_1521, plain, (![A_211, B_212]: (m1_subset_1('#skF_2'(A_211, B_212), A_211) | v1_xboole_0(A_211) | r1_tarski(A_211, B_212))), inference(resolution, [status(thm)], [c_1132, c_36])).
% 5.26/2.35  tff(c_1147, plain, (![A_152, B_153]: (~r2_hidden('#skF_2'(A_152, B_153), B_153) | r1_tarski(A_152, B_153))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.26/2.35  tff(c_1167, plain, (![A_152]: (r1_tarski(A_152, '#skF_6') | ~m1_subset_1('#skF_2'(A_152, '#skF_6'), '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_1147])).
% 5.26/2.35  tff(c_1529, plain, (v1_xboole_0('#skF_5') | r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1521, c_1167])).
% 5.26/2.35  tff(c_1542, plain, (r1_tarski('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1098, c_1529])).
% 5.26/2.35  tff(c_1099, plain, (![A_144, B_145]: (r2_xboole_0(A_144, B_145) | B_145=A_144 | ~r1_tarski(A_144, B_145))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.26/2.35  tff(c_22, plain, (![B_17, A_16]: (~r2_xboole_0(B_17, A_16) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.26/2.35  tff(c_1111, plain, (![B_145, A_144]: (~r1_tarski(B_145, A_144) | B_145=A_144 | ~r1_tarski(A_144, B_145))), inference(resolution, [status(thm)], [c_1099, c_22])).
% 5.26/2.35  tff(c_1560, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_1542, c_1111])).
% 5.26/2.35  tff(c_1567, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_1560])).
% 5.26/2.35  tff(c_1118, plain, (![B_146, A_147]: (r2_hidden(B_146, A_147) | ~m1_subset_1(B_146, A_147) | v1_xboole_0(A_147))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.26/2.35  tff(c_1680, plain, (![B_223, A_224]: (r1_tarski(B_223, A_224) | ~m1_subset_1(B_223, k1_zfmisc_1(A_224)) | v1_xboole_0(k1_zfmisc_1(A_224)))), inference(resolution, [status(thm)], [c_1118, c_24])).
% 5.26/2.35  tff(c_1701, plain, (r1_tarski('#skF_6', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_1680])).
% 5.26/2.35  tff(c_1711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_1567, c_1701])).
% 5.26/2.35  tff(c_1712, plain, (![C_32]: (~m1_subset_1(C_32, '#skF_5'))), inference(splitRight, [status(thm)], [c_56])).
% 5.26/2.35  tff(c_1727, plain, (![B_231]: (~v1_xboole_0(B_231) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_1722, c_1712])).
% 5.26/2.35  tff(c_1728, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1727])).
% 5.26/2.35  tff(c_1764, plain, (![B_243, A_244]: (m1_subset_1(B_243, A_244) | ~r2_hidden(B_243, A_244) | v1_xboole_0(A_244))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.26/2.35  tff(c_1773, plain, (![A_245]: (m1_subset_1('#skF_1'(A_245), A_245) | v1_xboole_0(A_245))), inference(resolution, [status(thm)], [c_4, c_1764])).
% 5.26/2.35  tff(c_1780, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1773, c_1712])).
% 5.26/2.35  tff(c_1785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1728, c_1780])).
% 5.26/2.35  tff(c_1786, plain, (![B_231]: (~v1_xboole_0(B_231))), inference(splitRight, [status(thm)], [c_1727])).
% 5.26/2.35  tff(c_1713, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_56])).
% 5.26/2.35  tff(c_1790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1786, c_1713])).
% 5.26/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.26/2.35  
% 5.26/2.35  Inference rules
% 5.26/2.35  ----------------------
% 5.26/2.35  #Ref     : 0
% 5.26/2.35  #Sup     : 390
% 5.26/2.35  #Fact    : 0
% 5.26/2.35  #Define  : 0
% 5.26/2.35  #Split   : 6
% 5.26/2.35  #Chain   : 0
% 5.26/2.35  #Close   : 0
% 5.26/2.35  
% 5.26/2.35  Ordering : KBO
% 5.26/2.35  
% 5.26/2.35  Simplification rules
% 5.26/2.35  ----------------------
% 5.26/2.35  #Subsume      : 116
% 5.26/2.35  #Demod        : 64
% 5.26/2.35  #Tautology    : 91
% 5.26/2.35  #SimpNegUnit  : 34
% 5.26/2.35  #BackRed      : 8
% 5.26/2.35  
% 5.26/2.35  #Partial instantiations: 0
% 5.26/2.35  #Strategies tried      : 1
% 5.26/2.35  
% 5.26/2.35  Timing (in seconds)
% 5.26/2.35  ----------------------
% 5.26/2.35  Preprocessing        : 0.50
% 5.26/2.35  Parsing              : 0.26
% 5.26/2.36  CNF conversion       : 0.04
% 5.26/2.36  Main loop            : 0.92
% 5.26/2.36  Inferencing          : 0.34
% 5.26/2.36  Reduction            : 0.22
% 5.26/2.36  Demodulation         : 0.13
% 5.26/2.36  BG Simplification    : 0.04
% 5.26/2.36  Subsumption          : 0.23
% 5.26/2.36  Abstraction          : 0.04
% 5.26/2.36  MUC search           : 0.00
% 5.26/2.36  Cooper               : 0.00
% 5.26/2.36  Total                : 1.47
% 5.26/2.36  Index Insertion      : 0.00
% 5.26/2.36  Index Deletion       : 0.00
% 5.26/2.36  Index Matching       : 0.00
% 5.26/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
