%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:30 EST 2020

% Result     : Theorem 6.59s
% Output     : CNFRefutation 6.86s
% Verified   : 
% Statistics : Number of formulae       :   65 (  78 expanded)
%              Number of leaves         :   35 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :   93 ( 130 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_68,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_66,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_64,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_54,plain,(
    ! [A_47,B_49] :
      ( r1_tarski(k2_relat_1(A_47),k2_relat_1(B_49))
      | ~ r1_tarski(A_47,B_49)
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_176,plain,(
    ! [A_83] :
      ( k2_xboole_0(k1_relat_1(A_83),k2_relat_1(A_83)) = k3_relat_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(A_12,k2_xboole_0(C_14,B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_182,plain,(
    ! [A_12,A_83] :
      ( r1_tarski(A_12,k3_relat_1(A_83))
      | ~ r1_tarski(A_12,k2_relat_1(A_83))
      | ~ v1_relat_1(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_26])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_626,plain,(
    ! [C_151,A_152] :
      ( r2_hidden(k4_tarski(C_151,'#skF_7'(A_152,k1_relat_1(A_152),C_151)),A_152)
      | ~ r2_hidden(C_151,k1_relat_1(A_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_75,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,B_59) = A_58
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_79,plain,(
    k3_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_64,c_75])).

tff(c_97,plain,(
    ! [D_65,B_66,A_67] :
      ( r2_hidden(D_65,B_66)
      | ~ r2_hidden(D_65,k3_xboole_0(A_67,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_100,plain,(
    ! [D_65] :
      ( r2_hidden(D_65,'#skF_9')
      | ~ r2_hidden(D_65,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_97])).

tff(c_265,plain,(
    ! [A_105,C_106,B_107] :
      ( r2_hidden(A_105,k3_relat_1(C_106))
      | ~ r2_hidden(k4_tarski(A_105,B_107),C_106)
      | ~ v1_relat_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_269,plain,(
    ! [A_105,B_107] :
      ( r2_hidden(A_105,k3_relat_1('#skF_9'))
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(k4_tarski(A_105,B_107),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_100,c_265])).

tff(c_272,plain,(
    ! [A_105,B_107] :
      ( r2_hidden(A_105,k3_relat_1('#skF_9'))
      | ~ r2_hidden(k4_tarski(A_105,B_107),'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_269])).

tff(c_671,plain,(
    ! [C_153] :
      ( r2_hidden(C_153,k3_relat_1('#skF_9'))
      | ~ r2_hidden(C_153,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_626,c_272])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1046,plain,(
    ! [A_178] :
      ( r1_tarski(A_178,k3_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_1'(A_178,k3_relat_1('#skF_9')),k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_671,c_4])).

tff(c_1066,plain,(
    r1_tarski(k1_relat_1('#skF_8'),k3_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_6,c_1046])).

tff(c_52,plain,(
    ! [A_46] :
      ( k2_xboole_0(k1_relat_1(A_46),k2_relat_1(A_46)) = k3_relat_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_232,plain,(
    ! [A_96,C_97,B_98] :
      ( r1_tarski(k2_xboole_0(A_96,C_97),B_98)
      | ~ r1_tarski(C_97,B_98)
      | ~ r1_tarski(A_96,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5800,plain,(
    ! [A_377,B_378] :
      ( r1_tarski(k3_relat_1(A_377),B_378)
      | ~ r1_tarski(k2_relat_1(A_377),B_378)
      | ~ r1_tarski(k1_relat_1(A_377),B_378)
      | ~ v1_relat_1(A_377) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_232])).

tff(c_62,plain,(
    ~ r1_tarski(k3_relat_1('#skF_8'),k3_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_5864,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_8'),k3_relat_1('#skF_9'))
    | ~ r1_tarski(k1_relat_1('#skF_8'),k3_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_5800,c_62])).

tff(c_5893,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),k3_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1066,c_5864])).

tff(c_5899,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_8'),k2_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_182,c_5893])).

tff(c_5903,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5899])).

tff(c_5906,plain,
    ( ~ r1_tarski('#skF_8','#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_5903])).

tff(c_5910,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_5906])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.59/2.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.86/2.37  
% 6.86/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.86/2.37  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 6.86/2.37  
% 6.86/2.37  %Foreground sorts:
% 6.86/2.37  
% 6.86/2.37  
% 6.86/2.37  %Background operators:
% 6.86/2.37  
% 6.86/2.37  
% 6.86/2.37  %Foreground operators:
% 6.86/2.37  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 6.86/2.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.86/2.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.86/2.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.86/2.37  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 6.86/2.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.86/2.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.86/2.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.86/2.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.86/2.37  tff('#skF_9', type, '#skF_9': $i).
% 6.86/2.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.86/2.37  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 6.86/2.37  tff('#skF_8', type, '#skF_8': $i).
% 6.86/2.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.86/2.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.86/2.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.86/2.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.86/2.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.86/2.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.86/2.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.86/2.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.86/2.37  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.86/2.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.86/2.37  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.86/2.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.86/2.37  
% 6.86/2.38  tff(f_109, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 6.86/2.38  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 6.86/2.38  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 6.86/2.38  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 6.86/2.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.86/2.38  tff(f_76, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 6.86/2.38  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.86/2.38  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 6.86/2.38  tff(f_99, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 6.86/2.38  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 6.86/2.38  tff(c_68, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.86/2.38  tff(c_66, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.86/2.38  tff(c_64, plain, (r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.86/2.38  tff(c_54, plain, (![A_47, B_49]: (r1_tarski(k2_relat_1(A_47), k2_relat_1(B_49)) | ~r1_tarski(A_47, B_49) | ~v1_relat_1(B_49) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.86/2.38  tff(c_176, plain, (![A_83]: (k2_xboole_0(k1_relat_1(A_83), k2_relat_1(A_83))=k3_relat_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.86/2.38  tff(c_26, plain, (![A_12, C_14, B_13]: (r1_tarski(A_12, k2_xboole_0(C_14, B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.86/2.38  tff(c_182, plain, (![A_12, A_83]: (r1_tarski(A_12, k3_relat_1(A_83)) | ~r1_tarski(A_12, k2_relat_1(A_83)) | ~v1_relat_1(A_83))), inference(superposition, [status(thm), theory('equality')], [c_176, c_26])).
% 6.86/2.38  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.86/2.38  tff(c_626, plain, (![C_151, A_152]: (r2_hidden(k4_tarski(C_151, '#skF_7'(A_152, k1_relat_1(A_152), C_151)), A_152) | ~r2_hidden(C_151, k1_relat_1(A_152)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.86/2.38  tff(c_75, plain, (![A_58, B_59]: (k3_xboole_0(A_58, B_59)=A_58 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.86/2.38  tff(c_79, plain, (k3_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_64, c_75])).
% 6.86/2.38  tff(c_97, plain, (![D_65, B_66, A_67]: (r2_hidden(D_65, B_66) | ~r2_hidden(D_65, k3_xboole_0(A_67, B_66)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.86/2.38  tff(c_100, plain, (![D_65]: (r2_hidden(D_65, '#skF_9') | ~r2_hidden(D_65, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_79, c_97])).
% 6.86/2.38  tff(c_265, plain, (![A_105, C_106, B_107]: (r2_hidden(A_105, k3_relat_1(C_106)) | ~r2_hidden(k4_tarski(A_105, B_107), C_106) | ~v1_relat_1(C_106))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.86/2.38  tff(c_269, plain, (![A_105, B_107]: (r2_hidden(A_105, k3_relat_1('#skF_9')) | ~v1_relat_1('#skF_9') | ~r2_hidden(k4_tarski(A_105, B_107), '#skF_8'))), inference(resolution, [status(thm)], [c_100, c_265])).
% 6.86/2.38  tff(c_272, plain, (![A_105, B_107]: (r2_hidden(A_105, k3_relat_1('#skF_9')) | ~r2_hidden(k4_tarski(A_105, B_107), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_269])).
% 6.86/2.38  tff(c_671, plain, (![C_153]: (r2_hidden(C_153, k3_relat_1('#skF_9')) | ~r2_hidden(C_153, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_626, c_272])).
% 6.86/2.38  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.86/2.38  tff(c_1046, plain, (![A_178]: (r1_tarski(A_178, k3_relat_1('#skF_9')) | ~r2_hidden('#skF_1'(A_178, k3_relat_1('#skF_9')), k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_671, c_4])).
% 6.86/2.38  tff(c_1066, plain, (r1_tarski(k1_relat_1('#skF_8'), k3_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_6, c_1046])).
% 6.86/2.38  tff(c_52, plain, (![A_46]: (k2_xboole_0(k1_relat_1(A_46), k2_relat_1(A_46))=k3_relat_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.86/2.38  tff(c_232, plain, (![A_96, C_97, B_98]: (r1_tarski(k2_xboole_0(A_96, C_97), B_98) | ~r1_tarski(C_97, B_98) | ~r1_tarski(A_96, B_98))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.86/2.38  tff(c_5800, plain, (![A_377, B_378]: (r1_tarski(k3_relat_1(A_377), B_378) | ~r1_tarski(k2_relat_1(A_377), B_378) | ~r1_tarski(k1_relat_1(A_377), B_378) | ~v1_relat_1(A_377))), inference(superposition, [status(thm), theory('equality')], [c_52, c_232])).
% 6.86/2.38  tff(c_62, plain, (~r1_tarski(k3_relat_1('#skF_8'), k3_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.86/2.38  tff(c_5864, plain, (~r1_tarski(k2_relat_1('#skF_8'), k3_relat_1('#skF_9')) | ~r1_tarski(k1_relat_1('#skF_8'), k3_relat_1('#skF_9')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_5800, c_62])).
% 6.86/2.38  tff(c_5893, plain, (~r1_tarski(k2_relat_1('#skF_8'), k3_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1066, c_5864])).
% 6.86/2.38  tff(c_5899, plain, (~r1_tarski(k2_relat_1('#skF_8'), k2_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_182, c_5893])).
% 6.86/2.38  tff(c_5903, plain, (~r1_tarski(k2_relat_1('#skF_8'), k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5899])).
% 6.86/2.38  tff(c_5906, plain, (~r1_tarski('#skF_8', '#skF_9') | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_54, c_5903])).
% 6.86/2.38  tff(c_5910, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_5906])).
% 6.86/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.86/2.38  
% 6.86/2.38  Inference rules
% 6.86/2.38  ----------------------
% 6.86/2.38  #Ref     : 0
% 6.86/2.38  #Sup     : 1378
% 6.86/2.38  #Fact    : 0
% 6.86/2.38  #Define  : 0
% 6.86/2.38  #Split   : 9
% 6.86/2.38  #Chain   : 0
% 6.86/2.38  #Close   : 0
% 6.86/2.38  
% 6.86/2.38  Ordering : KBO
% 6.86/2.38  
% 6.86/2.38  Simplification rules
% 6.86/2.38  ----------------------
% 6.86/2.38  #Subsume      : 348
% 6.86/2.38  #Demod        : 408
% 6.86/2.38  #Tautology    : 351
% 6.86/2.38  #SimpNegUnit  : 10
% 6.86/2.38  #BackRed      : 10
% 6.86/2.38  
% 6.86/2.38  #Partial instantiations: 0
% 6.86/2.38  #Strategies tried      : 1
% 6.86/2.38  
% 6.86/2.38  Timing (in seconds)
% 6.86/2.38  ----------------------
% 6.86/2.38  Preprocessing        : 0.32
% 6.86/2.38  Parsing              : 0.17
% 6.86/2.38  CNF conversion       : 0.03
% 6.86/2.38  Main loop            : 1.30
% 6.86/2.38  Inferencing          : 0.44
% 6.86/2.38  Reduction            : 0.37
% 6.86/2.38  Demodulation         : 0.25
% 6.86/2.39  BG Simplification    : 0.05
% 6.86/2.39  Subsumption          : 0.35
% 6.86/2.39  Abstraction          : 0.05
% 6.86/2.39  MUC search           : 0.00
% 6.86/2.39  Cooper               : 0.00
% 6.86/2.39  Total                : 1.65
% 6.86/2.39  Index Insertion      : 0.00
% 6.86/2.39  Index Deletion       : 0.00
% 6.86/2.39  Index Matching       : 0.00
% 6.86/2.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
