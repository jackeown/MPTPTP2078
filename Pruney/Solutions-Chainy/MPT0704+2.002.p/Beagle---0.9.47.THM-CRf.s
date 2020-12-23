%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:15 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 145 expanded)
%              Number of leaves         :   23 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 337 expanded)
%              Number of equality atoms :   26 (  53 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
        <=> ! [B] :
            ? [C] : r1_tarski(k10_relat_1(A,k1_tarski(B)),k1_tarski(C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ! [B] :
            ~ ( r2_hidden(B,k2_relat_1(A))
              & ! [C] : k10_relat_1(A,k1_tarski(B)) != k1_tarski(C) )
      <=> v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(c_38,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_1'(A_35,B_36),A_35)
      | r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,(
    ! [A_35] : r1_tarski(A_35,A_35) ),
    inference(resolution,[status(thm)],[c_38,c_4])).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    ! [C_28] :
      ( ~ r1_tarski(k10_relat_1('#skF_4',k1_tarski('#skF_5')),k1_tarski(C_28))
      | ~ v2_funct_1('#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_62,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,(
    ! [B_29] :
      ( v2_funct_1('#skF_4')
      | r1_tarski(k10_relat_1('#skF_4',k1_tarski(B_29)),k1_tarski('#skF_6'(B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_64,plain,(
    ! [B_43] : r1_tarski(k10_relat_1('#skF_4',k1_tarski(B_43)),k1_tarski('#skF_6'(B_43))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_34])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k1_tarski(B_7) = A_6
      | k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_tarski(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_116,plain,(
    ! [B_55] :
      ( k10_relat_1('#skF_4',k1_tarski(B_55)) = k1_tarski('#skF_6'(B_55))
      | k10_relat_1('#skF_4',k1_tarski(B_55)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_64,c_8])).

tff(c_20,plain,(
    ! [C_18,A_10] :
      ( k1_tarski(C_18) != k10_relat_1(A_10,k1_tarski('#skF_2'(A_10)))
      | v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_127,plain,(
    ! [C_18] :
      ( k1_tarski(C_18) != k1_tarski('#skF_6'('#skF_2'('#skF_4')))
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | k10_relat_1('#skF_4',k1_tarski('#skF_2'('#skF_4'))) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_20])).

tff(c_139,plain,(
    ! [C_18] :
      ( k1_tarski(C_18) != k1_tarski('#skF_6'('#skF_2'('#skF_4')))
      | v2_funct_1('#skF_4')
      | k10_relat_1('#skF_4',k1_tarski('#skF_2'('#skF_4'))) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_127])).

tff(c_140,plain,(
    ! [C_18] :
      ( k1_tarski(C_18) != k1_tarski('#skF_6'('#skF_2'('#skF_4')))
      | k10_relat_1('#skF_4',k1_tarski('#skF_2'('#skF_4'))) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_139])).

tff(c_178,plain,(
    ! [C_18] : k1_tarski(C_18) != k1_tarski('#skF_6'('#skF_2'('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_201,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_178])).

tff(c_202,plain,(
    k10_relat_1('#skF_4',k1_tarski('#skF_2'('#skF_4'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_22,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),k2_relat_1(A_10))
      | v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_73,plain,(
    ! [B_45,A_46] :
      ( k10_relat_1(B_45,k1_tarski(A_46)) != k1_xboole_0
      | ~ r2_hidden(A_46,k2_relat_1(B_45))
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,(
    ! [A_10] :
      ( k10_relat_1(A_10,k1_tarski('#skF_2'(A_10))) != k1_xboole_0
      | v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_212,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_81])).

tff(c_231,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_212])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_231])).

tff(c_235,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,k2_relat_1(B_9))
      | k10_relat_1(B_9,k1_tarski(A_8)) = k1_xboole_0
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_344,plain,(
    ! [A_89,B_90] :
      ( k10_relat_1(A_89,k1_tarski(B_90)) = k1_tarski('#skF_3'(A_89,B_90))
      | ~ r2_hidden(B_90,k2_relat_1(A_89))
      | ~ v2_funct_1(A_89)
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_415,plain,(
    ! [B_111,A_112] :
      ( k10_relat_1(B_111,k1_tarski(A_112)) = k1_tarski('#skF_3'(B_111,A_112))
      | ~ v2_funct_1(B_111)
      | ~ v1_funct_1(B_111)
      | k10_relat_1(B_111,k1_tarski(A_112)) = k1_xboole_0
      | ~ v1_relat_1(B_111) ) ),
    inference(resolution,[status(thm)],[c_14,c_344])).

tff(c_234,plain,(
    ! [C_28] : ~ r1_tarski(k10_relat_1('#skF_4',k1_tarski('#skF_5')),k1_tarski(C_28)) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_444,plain,(
    ! [C_28] :
      ( ~ r1_tarski(k1_tarski('#skF_3'('#skF_4','#skF_5')),k1_tarski(C_28))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | k10_relat_1('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_234])).

tff(c_455,plain,(
    ! [C_28] :
      ( ~ r1_tarski(k1_tarski('#skF_3'('#skF_4','#skF_5')),k1_tarski(C_28))
      | k10_relat_1('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_235,c_444])).

tff(c_458,plain,(
    ! [C_113] : ~ r1_tarski(k1_tarski('#skF_3'('#skF_4','#skF_5')),k1_tarski(C_113)) ),
    inference(splitLeft,[status(thm)],[c_455])).

tff(c_468,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_43,c_458])).

tff(c_469,plain,(
    k10_relat_1('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_455])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(k1_xboole_0,k1_tarski(B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    ! [C_38,B_39,A_40] :
      ( r2_hidden(C_38,B_39)
      | ~ r2_hidden(C_38,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_265,plain,(
    ! [A_65,B_66,B_67] :
      ( r2_hidden('#skF_1'(A_65,B_66),B_67)
      | ~ r1_tarski(A_65,B_67)
      | r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_6,c_46])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_311,plain,(
    ! [A_80,B_81,B_82,B_83] :
      ( r2_hidden('#skF_1'(A_80,B_81),B_82)
      | ~ r1_tarski(B_83,B_82)
      | ~ r1_tarski(A_80,B_83)
      | r1_tarski(A_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_265,c_2])).

tff(c_318,plain,(
    ! [A_84,B_85,B_86] :
      ( r2_hidden('#skF_1'(A_84,B_85),k1_tarski(B_86))
      | ~ r1_tarski(A_84,k1_xboole_0)
      | r1_tarski(A_84,B_85) ) ),
    inference(resolution,[status(thm)],[c_12,c_311])).

tff(c_327,plain,(
    ! [A_87,B_88] :
      ( ~ r1_tarski(A_87,k1_xboole_0)
      | r1_tarski(A_87,k1_tarski(B_88)) ) ),
    inference(resolution,[status(thm)],[c_318,c_4])).

tff(c_342,plain,(
    ~ r1_tarski(k10_relat_1('#skF_4',k1_tarski('#skF_5')),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_327,c_234])).

tff(c_470,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_342])).

tff(c_474,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_470])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:36:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.31  
% 2.07/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.32  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1 > #skF_6
% 2.07/1.32  
% 2.07/1.32  %Foreground sorts:
% 2.07/1.32  
% 2.07/1.32  
% 2.07/1.32  %Background operators:
% 2.07/1.32  
% 2.07/1.32  
% 2.07/1.32  %Foreground operators:
% 2.07/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.07/1.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.07/1.32  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.07/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.07/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.07/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.07/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.32  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.07/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.07/1.32  tff('#skF_6', type, '#skF_6': $i > $i).
% 2.07/1.32  
% 2.45/1.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.45/1.33  tff(f_70, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B]: (?[C]: r1_tarski(k10_relat_1(A, k1_tarski(B)), k1_tarski(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_funct_1)).
% 2.45/1.33  tff(f_38, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 2.45/1.33  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((![B]: ~(r2_hidden(B, k2_relat_1(A)) & (![C]: ~(k10_relat_1(A, k1_tarski(B)) = k1_tarski(C))))) <=> v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_funct_1)).
% 2.45/1.33  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 2.45/1.33  tff(c_38, plain, (![A_35, B_36]: (r2_hidden('#skF_1'(A_35, B_36), A_35) | r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.45/1.33  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.45/1.33  tff(c_43, plain, (![A_35]: (r1_tarski(A_35, A_35))), inference(resolution, [status(thm)], [c_38, c_4])).
% 2.45/1.33  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.45/1.33  tff(c_24, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.45/1.33  tff(c_28, plain, (![C_28]: (~r1_tarski(k10_relat_1('#skF_4', k1_tarski('#skF_5')), k1_tarski(C_28)) | ~v2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.45/1.33  tff(c_62, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_28])).
% 2.45/1.33  tff(c_34, plain, (![B_29]: (v2_funct_1('#skF_4') | r1_tarski(k10_relat_1('#skF_4', k1_tarski(B_29)), k1_tarski('#skF_6'(B_29))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.45/1.33  tff(c_64, plain, (![B_43]: (r1_tarski(k10_relat_1('#skF_4', k1_tarski(B_43)), k1_tarski('#skF_6'(B_43))))), inference(negUnitSimplification, [status(thm)], [c_62, c_34])).
% 2.45/1.33  tff(c_8, plain, (![B_7, A_6]: (k1_tarski(B_7)=A_6 | k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_tarski(B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.45/1.33  tff(c_116, plain, (![B_55]: (k10_relat_1('#skF_4', k1_tarski(B_55))=k1_tarski('#skF_6'(B_55)) | k10_relat_1('#skF_4', k1_tarski(B_55))=k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_8])).
% 2.45/1.33  tff(c_20, plain, (![C_18, A_10]: (k1_tarski(C_18)!=k10_relat_1(A_10, k1_tarski('#skF_2'(A_10))) | v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.45/1.33  tff(c_127, plain, (![C_18]: (k1_tarski(C_18)!=k1_tarski('#skF_6'('#skF_2'('#skF_4'))) | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | k10_relat_1('#skF_4', k1_tarski('#skF_2'('#skF_4')))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_116, c_20])).
% 2.45/1.33  tff(c_139, plain, (![C_18]: (k1_tarski(C_18)!=k1_tarski('#skF_6'('#skF_2'('#skF_4'))) | v2_funct_1('#skF_4') | k10_relat_1('#skF_4', k1_tarski('#skF_2'('#skF_4')))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_127])).
% 2.45/1.33  tff(c_140, plain, (![C_18]: (k1_tarski(C_18)!=k1_tarski('#skF_6'('#skF_2'('#skF_4'))) | k10_relat_1('#skF_4', k1_tarski('#skF_2'('#skF_4')))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_62, c_139])).
% 2.45/1.33  tff(c_178, plain, (![C_18]: (k1_tarski(C_18)!=k1_tarski('#skF_6'('#skF_2'('#skF_4'))))), inference(splitLeft, [status(thm)], [c_140])).
% 2.45/1.33  tff(c_201, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_178])).
% 2.45/1.33  tff(c_202, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_2'('#skF_4')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_140])).
% 2.45/1.33  tff(c_22, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), k2_relat_1(A_10)) | v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.45/1.33  tff(c_73, plain, (![B_45, A_46]: (k10_relat_1(B_45, k1_tarski(A_46))!=k1_xboole_0 | ~r2_hidden(A_46, k2_relat_1(B_45)) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.45/1.33  tff(c_81, plain, (![A_10]: (k10_relat_1(A_10, k1_tarski('#skF_2'(A_10)))!=k1_xboole_0 | v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_22, c_73])).
% 2.45/1.33  tff(c_212, plain, (v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_202, c_81])).
% 2.45/1.33  tff(c_231, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_212])).
% 2.45/1.33  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_231])).
% 2.45/1.33  tff(c_235, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_28])).
% 2.45/1.33  tff(c_14, plain, (![A_8, B_9]: (r2_hidden(A_8, k2_relat_1(B_9)) | k10_relat_1(B_9, k1_tarski(A_8))=k1_xboole_0 | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.45/1.33  tff(c_344, plain, (![A_89, B_90]: (k10_relat_1(A_89, k1_tarski(B_90))=k1_tarski('#skF_3'(A_89, B_90)) | ~r2_hidden(B_90, k2_relat_1(A_89)) | ~v2_funct_1(A_89) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.45/1.33  tff(c_415, plain, (![B_111, A_112]: (k10_relat_1(B_111, k1_tarski(A_112))=k1_tarski('#skF_3'(B_111, A_112)) | ~v2_funct_1(B_111) | ~v1_funct_1(B_111) | k10_relat_1(B_111, k1_tarski(A_112))=k1_xboole_0 | ~v1_relat_1(B_111))), inference(resolution, [status(thm)], [c_14, c_344])).
% 2.45/1.33  tff(c_234, plain, (![C_28]: (~r1_tarski(k10_relat_1('#skF_4', k1_tarski('#skF_5')), k1_tarski(C_28)))), inference(splitRight, [status(thm)], [c_28])).
% 2.45/1.33  tff(c_444, plain, (![C_28]: (~r1_tarski(k1_tarski('#skF_3'('#skF_4', '#skF_5')), k1_tarski(C_28)) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | k10_relat_1('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0 | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_415, c_234])).
% 2.45/1.33  tff(c_455, plain, (![C_28]: (~r1_tarski(k1_tarski('#skF_3'('#skF_4', '#skF_5')), k1_tarski(C_28)) | k10_relat_1('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_235, c_444])).
% 2.45/1.33  tff(c_458, plain, (![C_113]: (~r1_tarski(k1_tarski('#skF_3'('#skF_4', '#skF_5')), k1_tarski(C_113)))), inference(splitLeft, [status(thm)], [c_455])).
% 2.45/1.33  tff(c_468, plain, $false, inference(resolution, [status(thm)], [c_43, c_458])).
% 2.45/1.33  tff(c_469, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_455])).
% 2.45/1.33  tff(c_12, plain, (![B_7]: (r1_tarski(k1_xboole_0, k1_tarski(B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.45/1.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.45/1.33  tff(c_46, plain, (![C_38, B_39, A_40]: (r2_hidden(C_38, B_39) | ~r2_hidden(C_38, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.45/1.33  tff(c_265, plain, (![A_65, B_66, B_67]: (r2_hidden('#skF_1'(A_65, B_66), B_67) | ~r1_tarski(A_65, B_67) | r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_6, c_46])).
% 2.45/1.33  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.45/1.33  tff(c_311, plain, (![A_80, B_81, B_82, B_83]: (r2_hidden('#skF_1'(A_80, B_81), B_82) | ~r1_tarski(B_83, B_82) | ~r1_tarski(A_80, B_83) | r1_tarski(A_80, B_81))), inference(resolution, [status(thm)], [c_265, c_2])).
% 2.45/1.33  tff(c_318, plain, (![A_84, B_85, B_86]: (r2_hidden('#skF_1'(A_84, B_85), k1_tarski(B_86)) | ~r1_tarski(A_84, k1_xboole_0) | r1_tarski(A_84, B_85))), inference(resolution, [status(thm)], [c_12, c_311])).
% 2.45/1.33  tff(c_327, plain, (![A_87, B_88]: (~r1_tarski(A_87, k1_xboole_0) | r1_tarski(A_87, k1_tarski(B_88)))), inference(resolution, [status(thm)], [c_318, c_4])).
% 2.45/1.33  tff(c_342, plain, (~r1_tarski(k10_relat_1('#skF_4', k1_tarski('#skF_5')), k1_xboole_0)), inference(resolution, [status(thm)], [c_327, c_234])).
% 2.45/1.33  tff(c_470, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_469, c_342])).
% 2.45/1.33  tff(c_474, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43, c_470])).
% 2.45/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.33  
% 2.45/1.33  Inference rules
% 2.45/1.33  ----------------------
% 2.45/1.33  #Ref     : 1
% 2.45/1.33  #Sup     : 89
% 2.45/1.33  #Fact    : 2
% 2.45/1.33  #Define  : 0
% 2.45/1.33  #Split   : 4
% 2.45/1.33  #Chain   : 0
% 2.45/1.33  #Close   : 0
% 2.45/1.33  
% 2.45/1.33  Ordering : KBO
% 2.45/1.33  
% 2.45/1.33  Simplification rules
% 2.45/1.33  ----------------------
% 2.45/1.33  #Subsume      : 17
% 2.45/1.33  #Demod        : 26
% 2.45/1.33  #Tautology    : 29
% 2.45/1.33  #SimpNegUnit  : 7
% 2.45/1.33  #BackRed      : 2
% 2.45/1.33  
% 2.45/1.33  #Partial instantiations: 0
% 2.45/1.33  #Strategies tried      : 1
% 2.45/1.33  
% 2.45/1.33  Timing (in seconds)
% 2.45/1.33  ----------------------
% 2.45/1.33  Preprocessing        : 0.30
% 2.45/1.34  Parsing              : 0.15
% 2.45/1.34  CNF conversion       : 0.02
% 2.45/1.34  Main loop            : 0.27
% 2.45/1.34  Inferencing          : 0.10
% 2.45/1.34  Reduction            : 0.07
% 2.45/1.34  Demodulation         : 0.05
% 2.45/1.34  BG Simplification    : 0.02
% 2.45/1.34  Subsumption          : 0.06
% 2.45/1.34  Abstraction          : 0.02
% 2.45/1.34  MUC search           : 0.00
% 2.45/1.34  Cooper               : 0.00
% 2.45/1.34  Total                : 0.60
% 2.45/1.34  Index Insertion      : 0.00
% 2.45/1.34  Index Deletion       : 0.00
% 2.45/1.34  Index Matching       : 0.00
% 2.45/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
