%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:15 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 272 expanded)
%              Number of leaves         :   28 ( 110 expanded)
%              Depth                    :   19
%              Number of atoms          :  138 ( 822 expanded)
%              Number of equality atoms :   15 (  71 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_73,axiom,(
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

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_50,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_32,plain,(
    ! [A_39,B_40] :
      ( v1_funct_1(k7_relat_1(A_39,B_40))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    ! [A_39,B_40] :
      ( v1_relat_1(k7_relat_1(A_39,B_40))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    ! [C_35,A_20] :
      ( r2_hidden(k4_tarski(C_35,'#skF_8'(A_20,k1_relat_1(A_20),C_35)),A_20)
      | ~ r2_hidden(C_35,k1_relat_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    ! [C_57,A_58,B_59] :
      ( k1_funct_1(C_57,A_58) = B_59
      | ~ r2_hidden(k4_tarski(A_58,B_59),C_57)
      | ~ v1_funct_1(C_57)
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_137,plain,(
    ! [A_78,C_79] :
      ( '#skF_8'(A_78,k1_relat_1(A_78),C_79) = k1_funct_1(A_78,C_79)
      | ~ v1_funct_1(A_78)
      | ~ v1_relat_1(A_78)
      | ~ r2_hidden(C_79,k1_relat_1(A_78)) ) ),
    inference(resolution,[status(thm)],[c_20,c_62])).

tff(c_156,plain,
    ( '#skF_8'('#skF_11',k1_relat_1('#skF_11'),'#skF_9') = k1_funct_1('#skF_11','#skF_9')
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_48,c_137])).

tff(c_165,plain,(
    '#skF_8'('#skF_11',k1_relat_1('#skF_11'),'#skF_9') = k1_funct_1('#skF_11','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_156])).

tff(c_169,plain,
    ( r2_hidden(k4_tarski('#skF_9',k1_funct_1('#skF_11','#skF_9')),'#skF_11')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_20])).

tff(c_173,plain,(
    r2_hidden(k4_tarski('#skF_9',k1_funct_1('#skF_11','#skF_9')),'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_169])).

tff(c_253,plain,(
    ! [D_91,E_92,A_93,B_94] :
      ( r2_hidden(k4_tarski(D_91,E_92),k7_relat_1(A_93,B_94))
      | ~ r2_hidden(k4_tarski(D_91,E_92),A_93)
      | ~ r2_hidden(D_91,B_94)
      | ~ v1_relat_1(k7_relat_1(A_93,B_94))
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,(
    ! [C_45,A_43,B_44] :
      ( k1_funct_1(C_45,A_43) = B_44
      | ~ r2_hidden(k4_tarski(A_43,B_44),C_45)
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_455,plain,(
    ! [A_114,B_115,D_116,E_117] :
      ( k1_funct_1(k7_relat_1(A_114,B_115),D_116) = E_117
      | ~ v1_funct_1(k7_relat_1(A_114,B_115))
      | ~ r2_hidden(k4_tarski(D_116,E_117),A_114)
      | ~ r2_hidden(D_116,B_115)
      | ~ v1_relat_1(k7_relat_1(A_114,B_115))
      | ~ v1_relat_1(A_114) ) ),
    inference(resolution,[status(thm)],[c_253,c_40])).

tff(c_466,plain,(
    ! [B_115] :
      ( k1_funct_1(k7_relat_1('#skF_11',B_115),'#skF_9') = k1_funct_1('#skF_11','#skF_9')
      | ~ v1_funct_1(k7_relat_1('#skF_11',B_115))
      | ~ r2_hidden('#skF_9',B_115)
      | ~ v1_relat_1(k7_relat_1('#skF_11',B_115))
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_173,c_455])).

tff(c_483,plain,(
    ! [B_118] :
      ( k1_funct_1(k7_relat_1('#skF_11',B_118),'#skF_9') = k1_funct_1('#skF_11','#skF_9')
      | ~ v1_funct_1(k7_relat_1('#skF_11',B_118))
      | ~ r2_hidden('#skF_9',B_118)
      | ~ v1_relat_1(k7_relat_1('#skF_11',B_118)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_466])).

tff(c_487,plain,(
    ! [B_40] :
      ( k1_funct_1(k7_relat_1('#skF_11',B_40),'#skF_9') = k1_funct_1('#skF_11','#skF_9')
      | ~ v1_funct_1(k7_relat_1('#skF_11',B_40))
      | ~ r2_hidden('#skF_9',B_40)
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_34,c_483])).

tff(c_491,plain,(
    ! [B_119] :
      ( k1_funct_1(k7_relat_1('#skF_11',B_119),'#skF_9') = k1_funct_1('#skF_11','#skF_9')
      | ~ v1_funct_1(k7_relat_1('#skF_11',B_119))
      | ~ r2_hidden('#skF_9',B_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_487])).

tff(c_495,plain,(
    ! [B_40] :
      ( k1_funct_1(k7_relat_1('#skF_11',B_40),'#skF_9') = k1_funct_1('#skF_11','#skF_9')
      | ~ r2_hidden('#skF_9',B_40)
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_32,c_491])).

tff(c_499,plain,(
    ! [B_120] :
      ( k1_funct_1(k7_relat_1('#skF_11',B_120),'#skF_9') = k1_funct_1('#skF_11','#skF_9')
      | ~ r2_hidden('#skF_9',B_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_495])).

tff(c_36,plain,(
    ! [B_42,A_41] :
      ( r2_hidden(k1_funct_1(B_42,A_41),k2_relat_1(B_42))
      | ~ r2_hidden(A_41,k1_relat_1(B_42))
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1067,plain,(
    ! [B_156] :
      ( r2_hidden(k1_funct_1('#skF_11','#skF_9'),k2_relat_1(k7_relat_1('#skF_11',B_156)))
      | ~ r2_hidden('#skF_9',k1_relat_1(k7_relat_1('#skF_11',B_156)))
      | ~ v1_funct_1(k7_relat_1('#skF_11',B_156))
      | ~ v1_relat_1(k7_relat_1('#skF_11',B_156))
      | ~ r2_hidden('#skF_9',B_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_36])).

tff(c_44,plain,(
    ~ r2_hidden(k1_funct_1('#skF_11','#skF_9'),k2_relat_1(k7_relat_1('#skF_11','#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1070,plain,
    ( ~ r2_hidden('#skF_9',k1_relat_1(k7_relat_1('#skF_11','#skF_10')))
    | ~ v1_funct_1(k7_relat_1('#skF_11','#skF_10'))
    | ~ v1_relat_1(k7_relat_1('#skF_11','#skF_10'))
    | ~ r2_hidden('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_1067,c_44])).

tff(c_1073,plain,
    ( ~ r2_hidden('#skF_9',k1_relat_1(k7_relat_1('#skF_11','#skF_10')))
    | ~ v1_funct_1(k7_relat_1('#skF_11','#skF_10'))
    | ~ v1_relat_1(k7_relat_1('#skF_11','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1070])).

tff(c_1180,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_11','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_1073])).

tff(c_1183,plain,
    ( ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_34,c_1180])).

tff(c_1187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1183])).

tff(c_1189,plain,(
    v1_relat_1(k7_relat_1('#skF_11','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_1073])).

tff(c_22,plain,(
    ! [C_35,A_20,D_38] :
      ( r2_hidden(C_35,k1_relat_1(A_20))
      | ~ r2_hidden(k4_tarski(C_35,D_38),A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_274,plain,(
    ! [D_95,A_96,B_97,E_98] :
      ( r2_hidden(D_95,k1_relat_1(k7_relat_1(A_96,B_97)))
      | ~ r2_hidden(k4_tarski(D_95,E_98),A_96)
      | ~ r2_hidden(D_95,B_97)
      | ~ v1_relat_1(k7_relat_1(A_96,B_97))
      | ~ v1_relat_1(A_96) ) ),
    inference(resolution,[status(thm)],[c_253,c_22])).

tff(c_294,plain,(
    ! [C_35,A_20,B_97] :
      ( r2_hidden(C_35,k1_relat_1(k7_relat_1(A_20,B_97)))
      | ~ r2_hidden(C_35,B_97)
      | ~ v1_relat_1(k7_relat_1(A_20,B_97))
      | ~ v1_relat_1(A_20)
      | ~ r2_hidden(C_35,k1_relat_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_20,c_274])).

tff(c_1188,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_11','#skF_10'))
    | ~ r2_hidden('#skF_9',k1_relat_1(k7_relat_1('#skF_11','#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_1073])).

tff(c_1190,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1(k7_relat_1('#skF_11','#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_1188])).

tff(c_1193,plain,
    ( ~ r2_hidden('#skF_9','#skF_10')
    | ~ v1_relat_1(k7_relat_1('#skF_11','#skF_10'))
    | ~ v1_relat_1('#skF_11')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_294,c_1190])).

tff(c_1200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_1189,c_46,c_1193])).

tff(c_1201,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_11','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_1188])).

tff(c_1205,plain,
    ( ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_32,c_1201])).

tff(c_1209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:29:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.57  
% 3.59/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.58  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_5
% 3.59/1.58  
% 3.59/1.58  %Foreground sorts:
% 3.59/1.58  
% 3.59/1.58  
% 3.59/1.58  %Background operators:
% 3.59/1.58  
% 3.59/1.58  
% 3.59/1.58  %Foreground operators:
% 3.59/1.58  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.59/1.58  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.59/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.59/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.59/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.59/1.58  tff('#skF_11', type, '#skF_11': $i).
% 3.59/1.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.59/1.58  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.59/1.58  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.59/1.58  tff('#skF_10', type, '#skF_10': $i).
% 3.59/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.59/1.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.59/1.58  tff('#skF_9', type, '#skF_9': $i).
% 3.59/1.58  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.59/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.59/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.59/1.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.59/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.59/1.58  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.59/1.58  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.59/1.58  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.59/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.59/1.58  
% 3.59/1.59  tff(f_84, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_1)).
% 3.59/1.59  tff(f_55, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 3.59/1.59  tff(f_47, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.59/1.59  tff(f_73, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.59/1.59  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_relat_1)).
% 3.59/1.59  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 3.59/1.59  tff(c_52, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.59/1.59  tff(c_50, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.59/1.59  tff(c_32, plain, (![A_39, B_40]: (v1_funct_1(k7_relat_1(A_39, B_40)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.59/1.59  tff(c_48, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.59/1.59  tff(c_34, plain, (![A_39, B_40]: (v1_relat_1(k7_relat_1(A_39, B_40)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.59/1.59  tff(c_46, plain, (r2_hidden('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.59/1.59  tff(c_20, plain, (![C_35, A_20]: (r2_hidden(k4_tarski(C_35, '#skF_8'(A_20, k1_relat_1(A_20), C_35)), A_20) | ~r2_hidden(C_35, k1_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.59/1.59  tff(c_62, plain, (![C_57, A_58, B_59]: (k1_funct_1(C_57, A_58)=B_59 | ~r2_hidden(k4_tarski(A_58, B_59), C_57) | ~v1_funct_1(C_57) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.59/1.59  tff(c_137, plain, (![A_78, C_79]: ('#skF_8'(A_78, k1_relat_1(A_78), C_79)=k1_funct_1(A_78, C_79) | ~v1_funct_1(A_78) | ~v1_relat_1(A_78) | ~r2_hidden(C_79, k1_relat_1(A_78)))), inference(resolution, [status(thm)], [c_20, c_62])).
% 3.59/1.59  tff(c_156, plain, ('#skF_8'('#skF_11', k1_relat_1('#skF_11'), '#skF_9')=k1_funct_1('#skF_11', '#skF_9') | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_48, c_137])).
% 3.59/1.59  tff(c_165, plain, ('#skF_8'('#skF_11', k1_relat_1('#skF_11'), '#skF_9')=k1_funct_1('#skF_11', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_156])).
% 3.59/1.59  tff(c_169, plain, (r2_hidden(k4_tarski('#skF_9', k1_funct_1('#skF_11', '#skF_9')), '#skF_11') | ~r2_hidden('#skF_9', k1_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_20])).
% 3.59/1.59  tff(c_173, plain, (r2_hidden(k4_tarski('#skF_9', k1_funct_1('#skF_11', '#skF_9')), '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_169])).
% 3.59/1.59  tff(c_253, plain, (![D_91, E_92, A_93, B_94]: (r2_hidden(k4_tarski(D_91, E_92), k7_relat_1(A_93, B_94)) | ~r2_hidden(k4_tarski(D_91, E_92), A_93) | ~r2_hidden(D_91, B_94) | ~v1_relat_1(k7_relat_1(A_93, B_94)) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.59/1.59  tff(c_40, plain, (![C_45, A_43, B_44]: (k1_funct_1(C_45, A_43)=B_44 | ~r2_hidden(k4_tarski(A_43, B_44), C_45) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.59/1.59  tff(c_455, plain, (![A_114, B_115, D_116, E_117]: (k1_funct_1(k7_relat_1(A_114, B_115), D_116)=E_117 | ~v1_funct_1(k7_relat_1(A_114, B_115)) | ~r2_hidden(k4_tarski(D_116, E_117), A_114) | ~r2_hidden(D_116, B_115) | ~v1_relat_1(k7_relat_1(A_114, B_115)) | ~v1_relat_1(A_114))), inference(resolution, [status(thm)], [c_253, c_40])).
% 3.59/1.59  tff(c_466, plain, (![B_115]: (k1_funct_1(k7_relat_1('#skF_11', B_115), '#skF_9')=k1_funct_1('#skF_11', '#skF_9') | ~v1_funct_1(k7_relat_1('#skF_11', B_115)) | ~r2_hidden('#skF_9', B_115) | ~v1_relat_1(k7_relat_1('#skF_11', B_115)) | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_173, c_455])).
% 3.59/1.59  tff(c_483, plain, (![B_118]: (k1_funct_1(k7_relat_1('#skF_11', B_118), '#skF_9')=k1_funct_1('#skF_11', '#skF_9') | ~v1_funct_1(k7_relat_1('#skF_11', B_118)) | ~r2_hidden('#skF_9', B_118) | ~v1_relat_1(k7_relat_1('#skF_11', B_118)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_466])).
% 3.59/1.59  tff(c_487, plain, (![B_40]: (k1_funct_1(k7_relat_1('#skF_11', B_40), '#skF_9')=k1_funct_1('#skF_11', '#skF_9') | ~v1_funct_1(k7_relat_1('#skF_11', B_40)) | ~r2_hidden('#skF_9', B_40) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_34, c_483])).
% 3.59/1.59  tff(c_491, plain, (![B_119]: (k1_funct_1(k7_relat_1('#skF_11', B_119), '#skF_9')=k1_funct_1('#skF_11', '#skF_9') | ~v1_funct_1(k7_relat_1('#skF_11', B_119)) | ~r2_hidden('#skF_9', B_119))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_487])).
% 3.59/1.59  tff(c_495, plain, (![B_40]: (k1_funct_1(k7_relat_1('#skF_11', B_40), '#skF_9')=k1_funct_1('#skF_11', '#skF_9') | ~r2_hidden('#skF_9', B_40) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_32, c_491])).
% 3.59/1.59  tff(c_499, plain, (![B_120]: (k1_funct_1(k7_relat_1('#skF_11', B_120), '#skF_9')=k1_funct_1('#skF_11', '#skF_9') | ~r2_hidden('#skF_9', B_120))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_495])).
% 3.59/1.59  tff(c_36, plain, (![B_42, A_41]: (r2_hidden(k1_funct_1(B_42, A_41), k2_relat_1(B_42)) | ~r2_hidden(A_41, k1_relat_1(B_42)) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.59/1.59  tff(c_1067, plain, (![B_156]: (r2_hidden(k1_funct_1('#skF_11', '#skF_9'), k2_relat_1(k7_relat_1('#skF_11', B_156))) | ~r2_hidden('#skF_9', k1_relat_1(k7_relat_1('#skF_11', B_156))) | ~v1_funct_1(k7_relat_1('#skF_11', B_156)) | ~v1_relat_1(k7_relat_1('#skF_11', B_156)) | ~r2_hidden('#skF_9', B_156))), inference(superposition, [status(thm), theory('equality')], [c_499, c_36])).
% 3.59/1.59  tff(c_44, plain, (~r2_hidden(k1_funct_1('#skF_11', '#skF_9'), k2_relat_1(k7_relat_1('#skF_11', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.59/1.59  tff(c_1070, plain, (~r2_hidden('#skF_9', k1_relat_1(k7_relat_1('#skF_11', '#skF_10'))) | ~v1_funct_1(k7_relat_1('#skF_11', '#skF_10')) | ~v1_relat_1(k7_relat_1('#skF_11', '#skF_10')) | ~r2_hidden('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_1067, c_44])).
% 3.59/1.59  tff(c_1073, plain, (~r2_hidden('#skF_9', k1_relat_1(k7_relat_1('#skF_11', '#skF_10'))) | ~v1_funct_1(k7_relat_1('#skF_11', '#skF_10')) | ~v1_relat_1(k7_relat_1('#skF_11', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1070])).
% 3.59/1.59  tff(c_1180, plain, (~v1_relat_1(k7_relat_1('#skF_11', '#skF_10'))), inference(splitLeft, [status(thm)], [c_1073])).
% 3.59/1.59  tff(c_1183, plain, (~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_34, c_1180])).
% 3.59/1.59  tff(c_1187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1183])).
% 3.59/1.59  tff(c_1189, plain, (v1_relat_1(k7_relat_1('#skF_11', '#skF_10'))), inference(splitRight, [status(thm)], [c_1073])).
% 3.59/1.59  tff(c_22, plain, (![C_35, A_20, D_38]: (r2_hidden(C_35, k1_relat_1(A_20)) | ~r2_hidden(k4_tarski(C_35, D_38), A_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.59/1.59  tff(c_274, plain, (![D_95, A_96, B_97, E_98]: (r2_hidden(D_95, k1_relat_1(k7_relat_1(A_96, B_97))) | ~r2_hidden(k4_tarski(D_95, E_98), A_96) | ~r2_hidden(D_95, B_97) | ~v1_relat_1(k7_relat_1(A_96, B_97)) | ~v1_relat_1(A_96))), inference(resolution, [status(thm)], [c_253, c_22])).
% 3.59/1.59  tff(c_294, plain, (![C_35, A_20, B_97]: (r2_hidden(C_35, k1_relat_1(k7_relat_1(A_20, B_97))) | ~r2_hidden(C_35, B_97) | ~v1_relat_1(k7_relat_1(A_20, B_97)) | ~v1_relat_1(A_20) | ~r2_hidden(C_35, k1_relat_1(A_20)))), inference(resolution, [status(thm)], [c_20, c_274])).
% 3.59/1.59  tff(c_1188, plain, (~v1_funct_1(k7_relat_1('#skF_11', '#skF_10')) | ~r2_hidden('#skF_9', k1_relat_1(k7_relat_1('#skF_11', '#skF_10')))), inference(splitRight, [status(thm)], [c_1073])).
% 3.59/1.59  tff(c_1190, plain, (~r2_hidden('#skF_9', k1_relat_1(k7_relat_1('#skF_11', '#skF_10')))), inference(splitLeft, [status(thm)], [c_1188])).
% 3.59/1.59  tff(c_1193, plain, (~r2_hidden('#skF_9', '#skF_10') | ~v1_relat_1(k7_relat_1('#skF_11', '#skF_10')) | ~v1_relat_1('#skF_11') | ~r2_hidden('#skF_9', k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_294, c_1190])).
% 3.59/1.59  tff(c_1200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_1189, c_46, c_1193])).
% 3.59/1.59  tff(c_1201, plain, (~v1_funct_1(k7_relat_1('#skF_11', '#skF_10'))), inference(splitRight, [status(thm)], [c_1188])).
% 3.59/1.59  tff(c_1205, plain, (~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_32, c_1201])).
% 3.59/1.59  tff(c_1209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1205])).
% 3.59/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.59  
% 3.59/1.59  Inference rules
% 3.59/1.59  ----------------------
% 3.59/1.59  #Ref     : 0
% 3.59/1.59  #Sup     : 250
% 3.59/1.59  #Fact    : 0
% 3.59/1.59  #Define  : 0
% 3.59/1.59  #Split   : 2
% 3.59/1.59  #Chain   : 0
% 3.59/1.59  #Close   : 0
% 3.59/1.59  
% 3.59/1.59  Ordering : KBO
% 3.59/1.59  
% 3.59/1.59  Simplification rules
% 3.59/1.59  ----------------------
% 3.59/1.59  #Subsume      : 15
% 3.59/1.59  #Demod        : 30
% 3.59/1.59  #Tautology    : 34
% 3.59/1.59  #SimpNegUnit  : 0
% 3.59/1.59  #BackRed      : 0
% 3.59/1.59  
% 3.59/1.59  #Partial instantiations: 0
% 3.59/1.59  #Strategies tried      : 1
% 3.59/1.59  
% 3.59/1.59  Timing (in seconds)
% 3.59/1.59  ----------------------
% 3.59/1.59  Preprocessing        : 0.30
% 3.59/1.59  Parsing              : 0.16
% 3.59/1.59  CNF conversion       : 0.03
% 3.59/1.59  Main loop            : 0.52
% 3.59/1.59  Inferencing          : 0.19
% 3.59/1.59  Reduction            : 0.12
% 3.59/1.59  Demodulation         : 0.08
% 3.59/1.59  BG Simplification    : 0.03
% 3.59/1.59  Subsumption          : 0.13
% 3.59/1.59  Abstraction          : 0.04
% 3.59/1.59  MUC search           : 0.00
% 3.59/1.59  Cooper               : 0.00
% 3.59/1.59  Total                : 0.85
% 3.59/1.59  Index Insertion      : 0.00
% 3.59/1.59  Index Deletion       : 0.00
% 3.59/1.59  Index Matching       : 0.00
% 3.59/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
