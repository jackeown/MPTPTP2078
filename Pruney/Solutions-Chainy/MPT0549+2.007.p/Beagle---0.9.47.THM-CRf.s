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
% DateTime   : Thu Dec  3 10:00:49 EST 2020

% Result     : Theorem 55.37s
% Output     : CNFRefutation 55.37s
% Verified   : 
% Statistics : Number of formulae       :   70 (  92 expanded)
%              Number of leaves         :   35 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   96 ( 160 expanded)
%              Number of equality atoms :   20 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_4 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_89,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

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

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

tff(c_58,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_12'),'#skF_11')
    | k9_relat_1('#skF_12','#skF_11') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_81,plain,(
    k9_relat_1('#skF_12','#skF_11') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_56,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_48,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_64,plain,
    ( k9_relat_1('#skF_12','#skF_11') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_12'),'#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_94,plain,(
    r1_xboole_0(k1_relat_1('#skF_12'),'#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_64])).

tff(c_188,plain,(
    ! [B_109,A_110] :
      ( k7_relat_1(B_109,A_110) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_109),A_110)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_198,plain,
    ( k7_relat_1('#skF_12','#skF_11') = k1_xboole_0
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_94,c_188])).

tff(c_210,plain,(
    k7_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_198])).

tff(c_46,plain,(
    ! [B_75,A_74] :
      ( k2_relat_1(k7_relat_1(B_75,A_74)) = k9_relat_1(B_75,A_74)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_217,plain,
    ( k9_relat_1('#skF_12','#skF_11') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_46])).

tff(c_221,plain,(
    k9_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48,c_217])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_221])).

tff(c_224,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_12'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_233,plain,(
    ! [A_113,B_114,C_115] :
      ( ~ r1_xboole_0(A_113,B_114)
      | ~ r2_hidden(C_115,k3_xboole_0(A_113,B_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_240,plain,(
    ! [A_11,C_115] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_115,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_233])).

tff(c_243,plain,(
    ! [C_115] : ~ r2_hidden(C_115,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_240])).

tff(c_225,plain,(
    k9_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_34,plain,(
    ! [C_70,A_55] :
      ( r2_hidden(k4_tarski(C_70,'#skF_10'(A_55,k1_relat_1(A_55),C_70)),A_55)
      | ~ r2_hidden(C_70,k1_relat_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_485,plain,(
    ! [D_166,A_167,B_168,E_169] :
      ( r2_hidden(D_166,k9_relat_1(A_167,B_168))
      | ~ r2_hidden(E_169,B_168)
      | ~ r2_hidden(k4_tarski(E_169,D_166),A_167)
      | ~ v1_relat_1(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10872,plain,(
    ! [D_501,A_502,A_503,B_504] :
      ( r2_hidden(D_501,k9_relat_1(A_502,A_503))
      | ~ r2_hidden(k4_tarski('#skF_1'(A_503,B_504),D_501),A_502)
      | ~ v1_relat_1(A_502)
      | r1_xboole_0(A_503,B_504) ) ),
    inference(resolution,[status(thm)],[c_6,c_485])).

tff(c_204086,plain,(
    ! [A_1895,A_1896,B_1897] :
      ( r2_hidden('#skF_10'(A_1895,k1_relat_1(A_1895),'#skF_1'(A_1896,B_1897)),k9_relat_1(A_1895,A_1896))
      | ~ v1_relat_1(A_1895)
      | r1_xboole_0(A_1896,B_1897)
      | ~ r2_hidden('#skF_1'(A_1896,B_1897),k1_relat_1(A_1895)) ) ),
    inference(resolution,[status(thm)],[c_34,c_10872])).

tff(c_204524,plain,(
    ! [B_1897] :
      ( r2_hidden('#skF_10'('#skF_12',k1_relat_1('#skF_12'),'#skF_1'('#skF_11',B_1897)),k1_xboole_0)
      | ~ v1_relat_1('#skF_12')
      | r1_xboole_0('#skF_11',B_1897)
      | ~ r2_hidden('#skF_1'('#skF_11',B_1897),k1_relat_1('#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_204086])).

tff(c_204586,plain,(
    ! [B_1897] :
      ( r2_hidden('#skF_10'('#skF_12',k1_relat_1('#skF_12'),'#skF_1'('#skF_11',B_1897)),k1_xboole_0)
      | r1_xboole_0('#skF_11',B_1897)
      | ~ r2_hidden('#skF_1'('#skF_11',B_1897),k1_relat_1('#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_204524])).

tff(c_204589,plain,(
    ! [B_1898] :
      ( r1_xboole_0('#skF_11',B_1898)
      | ~ r2_hidden('#skF_1'('#skF_11',B_1898),k1_relat_1('#skF_12')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_243,c_204586])).

tff(c_204594,plain,(
    r1_xboole_0('#skF_11',k1_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_4,c_204589])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_205524,plain,(
    ! [C_1899] :
      ( ~ r2_hidden(C_1899,k1_relat_1('#skF_12'))
      | ~ r2_hidden(C_1899,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_204594,c_2])).

tff(c_206463,plain,(
    ! [B_1905] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1('#skF_12'),B_1905),'#skF_11')
      | r1_xboole_0(k1_relat_1('#skF_12'),B_1905) ) ),
    inference(resolution,[status(thm)],[c_6,c_205524])).

tff(c_206467,plain,(
    r1_xboole_0(k1_relat_1('#skF_12'),'#skF_11') ),
    inference(resolution,[status(thm)],[c_4,c_206463])).

tff(c_206471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_224,c_206467])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:38:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 55.37/44.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.37/44.16  
% 55.37/44.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.37/44.16  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_4 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_12 > #skF_10
% 55.37/44.16  
% 55.37/44.16  %Foreground sorts:
% 55.37/44.16  
% 55.37/44.16  
% 55.37/44.16  %Background operators:
% 55.37/44.16  
% 55.37/44.16  
% 55.37/44.16  %Foreground operators:
% 55.37/44.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 55.37/44.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 55.37/44.16  tff('#skF_11', type, '#skF_11': $i).
% 55.37/44.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 55.37/44.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 55.37/44.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 55.37/44.16  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 55.37/44.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 55.37/44.16  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 55.37/44.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 55.37/44.16  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 55.37/44.16  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 55.37/44.16  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 55.37/44.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 55.37/44.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 55.37/44.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 55.37/44.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 55.37/44.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 55.37/44.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 55.37/44.16  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 55.37/44.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 55.37/44.16  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 55.37/44.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 55.37/44.16  tff('#skF_12', type, '#skF_12': $i).
% 55.37/44.16  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 55.37/44.16  
% 55.37/44.17  tff(f_102, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 55.37/44.17  tff(f_89, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 55.37/44.17  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 55.37/44.17  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 55.37/44.17  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 55.37/44.17  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 55.37/44.17  tff(f_59, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 55.37/44.17  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 55.37/44.17  tff(f_82, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 55.37/44.17  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 55.37/44.17  tff(c_58, plain, (~r1_xboole_0(k1_relat_1('#skF_12'), '#skF_11') | k9_relat_1('#skF_12', '#skF_11')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 55.37/44.17  tff(c_81, plain, (k9_relat_1('#skF_12', '#skF_11')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 55.37/44.17  tff(c_56, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_102])).
% 55.37/44.17  tff(c_48, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 55.37/44.17  tff(c_64, plain, (k9_relat_1('#skF_12', '#skF_11')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_12'), '#skF_11')), inference(cnfTransformation, [status(thm)], [f_102])).
% 55.37/44.17  tff(c_94, plain, (r1_xboole_0(k1_relat_1('#skF_12'), '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_81, c_64])).
% 55.37/44.17  tff(c_188, plain, (![B_109, A_110]: (k7_relat_1(B_109, A_110)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_109), A_110) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_95])).
% 55.37/44.17  tff(c_198, plain, (k7_relat_1('#skF_12', '#skF_11')=k1_xboole_0 | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_94, c_188])).
% 55.37/44.17  tff(c_210, plain, (k7_relat_1('#skF_12', '#skF_11')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_198])).
% 55.37/44.17  tff(c_46, plain, (![B_75, A_74]: (k2_relat_1(k7_relat_1(B_75, A_74))=k9_relat_1(B_75, A_74) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_86])).
% 55.37/44.17  tff(c_217, plain, (k9_relat_1('#skF_12', '#skF_11')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_210, c_46])).
% 55.37/44.17  tff(c_221, plain, (k9_relat_1('#skF_12', '#skF_11')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48, c_217])).
% 55.37/44.17  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_221])).
% 55.37/44.17  tff(c_224, plain, (~r1_xboole_0(k1_relat_1('#skF_12'), '#skF_11')), inference(splitRight, [status(thm)], [c_58])).
% 55.37/44.17  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 55.37/44.17  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 55.37/44.17  tff(c_14, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 55.37/44.17  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 55.37/44.17  tff(c_233, plain, (![A_113, B_114, C_115]: (~r1_xboole_0(A_113, B_114) | ~r2_hidden(C_115, k3_xboole_0(A_113, B_114)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 55.37/44.17  tff(c_240, plain, (![A_11, C_115]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_115, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_233])).
% 55.37/44.17  tff(c_243, plain, (![C_115]: (~r2_hidden(C_115, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_240])).
% 55.37/44.17  tff(c_225, plain, (k9_relat_1('#skF_12', '#skF_11')=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 55.37/44.17  tff(c_34, plain, (![C_70, A_55]: (r2_hidden(k4_tarski(C_70, '#skF_10'(A_55, k1_relat_1(A_55), C_70)), A_55) | ~r2_hidden(C_70, k1_relat_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 55.37/44.17  tff(c_485, plain, (![D_166, A_167, B_168, E_169]: (r2_hidden(D_166, k9_relat_1(A_167, B_168)) | ~r2_hidden(E_169, B_168) | ~r2_hidden(k4_tarski(E_169, D_166), A_167) | ~v1_relat_1(A_167))), inference(cnfTransformation, [status(thm)], [f_74])).
% 55.37/44.17  tff(c_10872, plain, (![D_501, A_502, A_503, B_504]: (r2_hidden(D_501, k9_relat_1(A_502, A_503)) | ~r2_hidden(k4_tarski('#skF_1'(A_503, B_504), D_501), A_502) | ~v1_relat_1(A_502) | r1_xboole_0(A_503, B_504))), inference(resolution, [status(thm)], [c_6, c_485])).
% 55.37/44.17  tff(c_204086, plain, (![A_1895, A_1896, B_1897]: (r2_hidden('#skF_10'(A_1895, k1_relat_1(A_1895), '#skF_1'(A_1896, B_1897)), k9_relat_1(A_1895, A_1896)) | ~v1_relat_1(A_1895) | r1_xboole_0(A_1896, B_1897) | ~r2_hidden('#skF_1'(A_1896, B_1897), k1_relat_1(A_1895)))), inference(resolution, [status(thm)], [c_34, c_10872])).
% 55.37/44.17  tff(c_204524, plain, (![B_1897]: (r2_hidden('#skF_10'('#skF_12', k1_relat_1('#skF_12'), '#skF_1'('#skF_11', B_1897)), k1_xboole_0) | ~v1_relat_1('#skF_12') | r1_xboole_0('#skF_11', B_1897) | ~r2_hidden('#skF_1'('#skF_11', B_1897), k1_relat_1('#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_225, c_204086])).
% 55.37/44.17  tff(c_204586, plain, (![B_1897]: (r2_hidden('#skF_10'('#skF_12', k1_relat_1('#skF_12'), '#skF_1'('#skF_11', B_1897)), k1_xboole_0) | r1_xboole_0('#skF_11', B_1897) | ~r2_hidden('#skF_1'('#skF_11', B_1897), k1_relat_1('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_204524])).
% 55.37/44.17  tff(c_204589, plain, (![B_1898]: (r1_xboole_0('#skF_11', B_1898) | ~r2_hidden('#skF_1'('#skF_11', B_1898), k1_relat_1('#skF_12')))), inference(negUnitSimplification, [status(thm)], [c_243, c_204586])).
% 55.37/44.17  tff(c_204594, plain, (r1_xboole_0('#skF_11', k1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_4, c_204589])).
% 55.37/44.17  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 55.37/44.17  tff(c_205524, plain, (![C_1899]: (~r2_hidden(C_1899, k1_relat_1('#skF_12')) | ~r2_hidden(C_1899, '#skF_11'))), inference(resolution, [status(thm)], [c_204594, c_2])).
% 55.37/44.17  tff(c_206463, plain, (![B_1905]: (~r2_hidden('#skF_1'(k1_relat_1('#skF_12'), B_1905), '#skF_11') | r1_xboole_0(k1_relat_1('#skF_12'), B_1905))), inference(resolution, [status(thm)], [c_6, c_205524])).
% 55.37/44.17  tff(c_206467, plain, (r1_xboole_0(k1_relat_1('#skF_12'), '#skF_11')), inference(resolution, [status(thm)], [c_4, c_206463])).
% 55.37/44.17  tff(c_206471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_224, c_206467])).
% 55.37/44.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.37/44.17  
% 55.37/44.17  Inference rules
% 55.37/44.17  ----------------------
% 55.37/44.17  #Ref     : 0
% 55.37/44.17  #Sup     : 55825
% 55.37/44.17  #Fact    : 0
% 55.37/44.17  #Define  : 0
% 55.37/44.17  #Split   : 19
% 55.37/44.17  #Chain   : 0
% 55.37/44.17  #Close   : 0
% 55.37/44.17  
% 55.37/44.17  Ordering : KBO
% 55.37/44.17  
% 55.37/44.17  Simplification rules
% 55.37/44.17  ----------------------
% 55.37/44.17  #Subsume      : 23425
% 55.37/44.17  #Demod        : 55019
% 55.37/44.17  #Tautology    : 19658
% 55.37/44.17  #SimpNegUnit  : 600
% 55.37/44.17  #BackRed      : 0
% 55.37/44.17  
% 55.37/44.17  #Partial instantiations: 0
% 55.37/44.17  #Strategies tried      : 1
% 55.37/44.17  
% 55.37/44.17  Timing (in seconds)
% 55.37/44.17  ----------------------
% 55.37/44.18  Preprocessing        : 0.31
% 55.37/44.18  Parsing              : 0.16
% 55.37/44.18  CNF conversion       : 0.03
% 55.37/44.18  Main loop            : 43.10
% 55.37/44.18  Inferencing          : 3.99
% 55.37/44.18  Reduction            : 5.27
% 55.37/44.18  Demodulation         : 3.65
% 55.37/44.18  BG Simplification    : 0.38
% 55.37/44.18  Subsumption          : 32.28
% 55.37/44.18  Abstraction          : 0.70
% 55.37/44.18  MUC search           : 0.00
% 55.37/44.18  Cooper               : 0.00
% 55.37/44.18  Total                : 43.44
% 55.37/44.18  Index Insertion      : 0.00
% 55.37/44.18  Index Deletion       : 0.00
% 55.37/44.18  Index Matching       : 0.00
% 55.37/44.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
