%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:15 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 128 expanded)
%              Number of leaves         :   29 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 369 expanded)
%              Number of equality atoms :    6 (  19 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

tff(c_60,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_58,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_40,plain,(
    ! [A_62,B_63] :
      ( v1_funct_1(k7_relat_1(A_62,B_63))
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_56,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k7_relat_1(A_20,B_21))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_54,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_66,plain,(
    ! [C_82,B_83,A_84] :
      ( k1_funct_1(k7_relat_1(C_82,B_83),A_84) = k1_funct_1(C_82,A_84)
      | ~ r2_hidden(A_84,B_83)
      | ~ v1_funct_1(C_82)
      | ~ v1_relat_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    ! [A_22,D_61] :
      ( r2_hidden(k1_funct_1(A_22,D_61),k2_relat_1(A_22))
      | ~ r2_hidden(D_61,k1_relat_1(A_22))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1076,plain,(
    ! [C_201,A_202,B_203] :
      ( r2_hidden(k1_funct_1(C_201,A_202),k2_relat_1(k7_relat_1(C_201,B_203)))
      | ~ r2_hidden(A_202,k1_relat_1(k7_relat_1(C_201,B_203)))
      | ~ v1_funct_1(k7_relat_1(C_201,B_203))
      | ~ v1_relat_1(k7_relat_1(C_201,B_203))
      | ~ r2_hidden(A_202,B_203)
      | ~ v1_funct_1(C_201)
      | ~ v1_relat_1(C_201) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_22])).

tff(c_52,plain,(
    ~ r2_hidden(k1_funct_1('#skF_11','#skF_9'),k2_relat_1(k7_relat_1('#skF_11','#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1079,plain,
    ( ~ r2_hidden('#skF_9',k1_relat_1(k7_relat_1('#skF_11','#skF_10')))
    | ~ v1_funct_1(k7_relat_1('#skF_11','#skF_10'))
    | ~ v1_relat_1(k7_relat_1('#skF_11','#skF_10'))
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_1076,c_52])).

tff(c_1100,plain,
    ( ~ r2_hidden('#skF_9',k1_relat_1(k7_relat_1('#skF_11','#skF_10')))
    | ~ v1_funct_1(k7_relat_1('#skF_11','#skF_10'))
    | ~ v1_relat_1(k7_relat_1('#skF_11','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_1079])).

tff(c_1171,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_11','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_1100])).

tff(c_1174,plain,(
    ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_20,c_1171])).

tff(c_1178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1174])).

tff(c_1180,plain,(
    v1_relat_1(k7_relat_1('#skF_11','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_1100])).

tff(c_46,plain,(
    ! [A_67,C_69] :
      ( r2_hidden(k4_tarski(A_67,k1_funct_1(C_69,A_67)),C_69)
      | ~ r2_hidden(A_67,k1_relat_1(C_69))
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_183,plain,(
    ! [D_108,E_109,A_110,B_111] :
      ( r2_hidden(k4_tarski(D_108,E_109),k7_relat_1(A_110,B_111))
      | ~ r2_hidden(k4_tarski(D_108,E_109),A_110)
      | ~ r2_hidden(D_108,B_111)
      | ~ v1_relat_1(k7_relat_1(A_110,B_111))
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,(
    ! [A_67,C_69,B_68] :
      ( r2_hidden(A_67,k1_relat_1(C_69))
      | ~ r2_hidden(k4_tarski(A_67,B_68),C_69)
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_208,plain,(
    ! [D_118,A_119,B_120,E_121] :
      ( r2_hidden(D_118,k1_relat_1(k7_relat_1(A_119,B_120)))
      | ~ v1_funct_1(k7_relat_1(A_119,B_120))
      | ~ r2_hidden(k4_tarski(D_118,E_121),A_119)
      | ~ r2_hidden(D_118,B_120)
      | ~ v1_relat_1(k7_relat_1(A_119,B_120))
      | ~ v1_relat_1(A_119) ) ),
    inference(resolution,[status(thm)],[c_183,c_50])).

tff(c_214,plain,(
    ! [A_67,C_69,B_120] :
      ( r2_hidden(A_67,k1_relat_1(k7_relat_1(C_69,B_120)))
      | ~ v1_funct_1(k7_relat_1(C_69,B_120))
      | ~ r2_hidden(A_67,B_120)
      | ~ v1_relat_1(k7_relat_1(C_69,B_120))
      | ~ r2_hidden(A_67,k1_relat_1(C_69))
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69) ) ),
    inference(resolution,[status(thm)],[c_46,c_208])).

tff(c_1179,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_11','#skF_10'))
    | ~ r2_hidden('#skF_9',k1_relat_1(k7_relat_1('#skF_11','#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_1100])).

tff(c_1181,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1(k7_relat_1('#skF_11','#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_1179])).

tff(c_1184,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_11','#skF_10'))
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ v1_relat_1(k7_relat_1('#skF_11','#skF_10'))
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_11'))
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_214,c_1181])).

tff(c_1187,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_11','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_1180,c_54,c_1184])).

tff(c_1190,plain,
    ( ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_40,c_1187])).

tff(c_1194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1190])).

tff(c_1195,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_11','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_1179])).

tff(c_1199,plain,
    ( ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_40,c_1195])).

tff(c_1203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:22:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.65  
% 4.01/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.65  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_5
% 4.01/1.65  
% 4.01/1.65  %Foreground sorts:
% 4.01/1.65  
% 4.01/1.65  
% 4.01/1.65  %Background operators:
% 4.01/1.65  
% 4.01/1.65  
% 4.01/1.65  %Foreground operators:
% 4.01/1.65  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.01/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.01/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.01/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.01/1.65  tff('#skF_11', type, '#skF_11': $i).
% 4.01/1.65  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.01/1.65  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.01/1.65  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.01/1.65  tff('#skF_10', type, '#skF_10': $i).
% 4.01/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.01/1.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.01/1.65  tff('#skF_9', type, '#skF_9': $i).
% 4.01/1.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.01/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.01/1.65  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.01/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.65  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 4.01/1.65  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.01/1.65  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.01/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.01/1.65  
% 4.01/1.66  tff(f_95, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_1)).
% 4.01/1.66  tff(f_66, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 4.01/1.66  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.01/1.66  tff(f_74, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 4.01/1.66  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 4.01/1.66  tff(f_84, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 4.01/1.66  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_relat_1)).
% 4.01/1.66  tff(c_60, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.01/1.66  tff(c_58, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.01/1.66  tff(c_40, plain, (![A_62, B_63]: (v1_funct_1(k7_relat_1(A_62, B_63)) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.01/1.66  tff(c_56, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.01/1.66  tff(c_20, plain, (![A_20, B_21]: (v1_relat_1(k7_relat_1(A_20, B_21)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.01/1.66  tff(c_54, plain, (r2_hidden('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.01/1.66  tff(c_66, plain, (![C_82, B_83, A_84]: (k1_funct_1(k7_relat_1(C_82, B_83), A_84)=k1_funct_1(C_82, A_84) | ~r2_hidden(A_84, B_83) | ~v1_funct_1(C_82) | ~v1_relat_1(C_82))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.01/1.66  tff(c_22, plain, (![A_22, D_61]: (r2_hidden(k1_funct_1(A_22, D_61), k2_relat_1(A_22)) | ~r2_hidden(D_61, k1_relat_1(A_22)) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.01/1.66  tff(c_1076, plain, (![C_201, A_202, B_203]: (r2_hidden(k1_funct_1(C_201, A_202), k2_relat_1(k7_relat_1(C_201, B_203))) | ~r2_hidden(A_202, k1_relat_1(k7_relat_1(C_201, B_203))) | ~v1_funct_1(k7_relat_1(C_201, B_203)) | ~v1_relat_1(k7_relat_1(C_201, B_203)) | ~r2_hidden(A_202, B_203) | ~v1_funct_1(C_201) | ~v1_relat_1(C_201))), inference(superposition, [status(thm), theory('equality')], [c_66, c_22])).
% 4.01/1.66  tff(c_52, plain, (~r2_hidden(k1_funct_1('#skF_11', '#skF_9'), k2_relat_1(k7_relat_1('#skF_11', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.01/1.66  tff(c_1079, plain, (~r2_hidden('#skF_9', k1_relat_1(k7_relat_1('#skF_11', '#skF_10'))) | ~v1_funct_1(k7_relat_1('#skF_11', '#skF_10')) | ~v1_relat_1(k7_relat_1('#skF_11', '#skF_10')) | ~r2_hidden('#skF_9', '#skF_10') | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_1076, c_52])).
% 4.01/1.66  tff(c_1100, plain, (~r2_hidden('#skF_9', k1_relat_1(k7_relat_1('#skF_11', '#skF_10'))) | ~v1_funct_1(k7_relat_1('#skF_11', '#skF_10')) | ~v1_relat_1(k7_relat_1('#skF_11', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_1079])).
% 4.01/1.66  tff(c_1171, plain, (~v1_relat_1(k7_relat_1('#skF_11', '#skF_10'))), inference(splitLeft, [status(thm)], [c_1100])).
% 4.01/1.66  tff(c_1174, plain, (~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_20, c_1171])).
% 4.01/1.66  tff(c_1178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_1174])).
% 4.01/1.66  tff(c_1180, plain, (v1_relat_1(k7_relat_1('#skF_11', '#skF_10'))), inference(splitRight, [status(thm)], [c_1100])).
% 4.01/1.66  tff(c_46, plain, (![A_67, C_69]: (r2_hidden(k4_tarski(A_67, k1_funct_1(C_69, A_67)), C_69) | ~r2_hidden(A_67, k1_relat_1(C_69)) | ~v1_funct_1(C_69) | ~v1_relat_1(C_69))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.01/1.66  tff(c_183, plain, (![D_108, E_109, A_110, B_111]: (r2_hidden(k4_tarski(D_108, E_109), k7_relat_1(A_110, B_111)) | ~r2_hidden(k4_tarski(D_108, E_109), A_110) | ~r2_hidden(D_108, B_111) | ~v1_relat_1(k7_relat_1(A_110, B_111)) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.01/1.66  tff(c_50, plain, (![A_67, C_69, B_68]: (r2_hidden(A_67, k1_relat_1(C_69)) | ~r2_hidden(k4_tarski(A_67, B_68), C_69) | ~v1_funct_1(C_69) | ~v1_relat_1(C_69))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.01/1.66  tff(c_208, plain, (![D_118, A_119, B_120, E_121]: (r2_hidden(D_118, k1_relat_1(k7_relat_1(A_119, B_120))) | ~v1_funct_1(k7_relat_1(A_119, B_120)) | ~r2_hidden(k4_tarski(D_118, E_121), A_119) | ~r2_hidden(D_118, B_120) | ~v1_relat_1(k7_relat_1(A_119, B_120)) | ~v1_relat_1(A_119))), inference(resolution, [status(thm)], [c_183, c_50])).
% 4.01/1.66  tff(c_214, plain, (![A_67, C_69, B_120]: (r2_hidden(A_67, k1_relat_1(k7_relat_1(C_69, B_120))) | ~v1_funct_1(k7_relat_1(C_69, B_120)) | ~r2_hidden(A_67, B_120) | ~v1_relat_1(k7_relat_1(C_69, B_120)) | ~r2_hidden(A_67, k1_relat_1(C_69)) | ~v1_funct_1(C_69) | ~v1_relat_1(C_69))), inference(resolution, [status(thm)], [c_46, c_208])).
% 4.01/1.66  tff(c_1179, plain, (~v1_funct_1(k7_relat_1('#skF_11', '#skF_10')) | ~r2_hidden('#skF_9', k1_relat_1(k7_relat_1('#skF_11', '#skF_10')))), inference(splitRight, [status(thm)], [c_1100])).
% 4.01/1.66  tff(c_1181, plain, (~r2_hidden('#skF_9', k1_relat_1(k7_relat_1('#skF_11', '#skF_10')))), inference(splitLeft, [status(thm)], [c_1179])).
% 4.01/1.66  tff(c_1184, plain, (~v1_funct_1(k7_relat_1('#skF_11', '#skF_10')) | ~r2_hidden('#skF_9', '#skF_10') | ~v1_relat_1(k7_relat_1('#skF_11', '#skF_10')) | ~r2_hidden('#skF_9', k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_214, c_1181])).
% 4.01/1.66  tff(c_1187, plain, (~v1_funct_1(k7_relat_1('#skF_11', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_1180, c_54, c_1184])).
% 4.01/1.66  tff(c_1190, plain, (~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_40, c_1187])).
% 4.01/1.66  tff(c_1194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1190])).
% 4.01/1.66  tff(c_1195, plain, (~v1_funct_1(k7_relat_1('#skF_11', '#skF_10'))), inference(splitRight, [status(thm)], [c_1179])).
% 4.01/1.66  tff(c_1199, plain, (~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_40, c_1195])).
% 4.01/1.66  tff(c_1203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1199])).
% 4.01/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.66  
% 4.01/1.66  Inference rules
% 4.01/1.66  ----------------------
% 4.01/1.66  #Ref     : 0
% 4.01/1.66  #Sup     : 261
% 4.01/1.66  #Fact    : 0
% 4.01/1.66  #Define  : 0
% 4.01/1.66  #Split   : 2
% 4.01/1.66  #Chain   : 0
% 4.01/1.66  #Close   : 0
% 4.01/1.66  
% 4.01/1.66  Ordering : KBO
% 4.01/1.66  
% 4.01/1.66  Simplification rules
% 4.01/1.66  ----------------------
% 4.01/1.66  #Subsume      : 22
% 4.01/1.66  #Demod        : 13
% 4.01/1.66  #Tautology    : 40
% 4.01/1.66  #SimpNegUnit  : 0
% 4.01/1.66  #BackRed      : 0
% 4.01/1.66  
% 4.01/1.66  #Partial instantiations: 0
% 4.01/1.66  #Strategies tried      : 1
% 4.01/1.66  
% 4.01/1.66  Timing (in seconds)
% 4.01/1.66  ----------------------
% 4.36/1.66  Preprocessing        : 0.31
% 4.36/1.66  Parsing              : 0.16
% 4.36/1.66  CNF conversion       : 0.03
% 4.36/1.66  Main loop            : 0.59
% 4.36/1.66  Inferencing          : 0.22
% 4.36/1.66  Reduction            : 0.13
% 4.36/1.66  Demodulation         : 0.09
% 4.36/1.66  BG Simplification    : 0.04
% 4.36/1.66  Subsumption          : 0.16
% 4.36/1.66  Abstraction          : 0.04
% 4.36/1.66  MUC search           : 0.00
% 4.36/1.67  Cooper               : 0.00
% 4.36/1.67  Total                : 0.93
% 4.36/1.67  Index Insertion      : 0.00
% 4.36/1.67  Index Deletion       : 0.00
% 4.36/1.67  Index Matching       : 0.00
% 4.36/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
