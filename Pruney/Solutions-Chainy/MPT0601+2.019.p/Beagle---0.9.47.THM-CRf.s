%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:16 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   63 (  93 expanded)
%              Number of leaves         :   28 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   82 ( 144 expanded)
%              Number of equality atoms :   25 (  40 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_32,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,
    ( k11_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_76,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_40,plain,
    ( r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | k11_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_77,plain,(
    k11_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_290,plain,(
    ! [A_84,B_85] :
      ( r2_hidden(k4_tarski('#skF_1'(A_84,B_85),'#skF_2'(A_84,B_85)),A_84)
      | r2_hidden('#skF_3'(A_84,B_85),B_85)
      | k1_relat_1(A_84) = B_85 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [A_40,C_41,B_42] :
      ( ~ r2_hidden(A_40,C_41)
      | ~ r1_xboole_0(k2_tarski(A_40,B_42),C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ! [A_40] : ~ r2_hidden(A_40,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_60])).

tff(c_342,plain,(
    ! [B_86] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_86),B_86)
      | k1_relat_1(k1_xboole_0) = B_86 ) ),
    inference(resolution,[status(thm)],[c_290,c_68])).

tff(c_386,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_342,c_68])).

tff(c_341,plain,(
    ! [B_85] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_85),B_85)
      | k1_relat_1(k1_xboole_0) = B_85 ) ),
    inference(resolution,[status(thm)],[c_290,c_68])).

tff(c_432,plain,(
    ! [B_90] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_90),B_90)
      | k1_xboole_0 = B_90 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_341])).

tff(c_130,plain,(
    ! [A_58,B_59,C_60] :
      ( r2_hidden(k4_tarski(A_58,B_59),C_60)
      | ~ r2_hidden(B_59,k11_relat_1(C_60,A_58))
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [C_26,A_11,D_29] :
      ( r2_hidden(C_26,k1_relat_1(A_11))
      | ~ r2_hidden(k4_tarski(C_26,D_29),A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_138,plain,(
    ! [A_58,C_60,B_59] :
      ( r2_hidden(A_58,k1_relat_1(C_60))
      | ~ r2_hidden(B_59,k11_relat_1(C_60,A_58))
      | ~ v1_relat_1(C_60) ) ),
    inference(resolution,[status(thm)],[c_130,c_14])).

tff(c_485,plain,(
    ! [A_93,C_94] :
      ( r2_hidden(A_93,k1_relat_1(C_94))
      | ~ v1_relat_1(C_94)
      | k11_relat_1(C_94,A_93) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_432,c_138])).

tff(c_507,plain,
    ( ~ v1_relat_1('#skF_6')
    | k11_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_485,c_76])).

tff(c_519,plain,(
    k11_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_507])).

tff(c_521,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_519])).

tff(c_522,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_528,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_522])).

tff(c_529,plain,(
    k11_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_10,plain,(
    ! [A_8,B_10] :
      ( k9_relat_1(A_8,k1_tarski(B_10)) = k11_relat_1(A_8,B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_530,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_547,plain,(
    ! [B_100,A_101] :
      ( r1_xboole_0(k1_relat_1(B_100),A_101)
      | k9_relat_1(B_100,A_101) != k1_xboole_0
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_571,plain,(
    ! [A_108,B_109] :
      ( r1_xboole_0(A_108,k1_relat_1(B_109))
      | k9_relat_1(B_109,A_108) != k1_xboole_0
      | ~ v1_relat_1(B_109) ) ),
    inference(resolution,[status(thm)],[c_547,c_2])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_63,plain,(
    ! [A_4,C_41] :
      ( ~ r2_hidden(A_4,C_41)
      | ~ r1_xboole_0(k1_tarski(A_4),C_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_60])).

tff(c_590,plain,(
    ! [A_110,B_111] :
      ( ~ r2_hidden(A_110,k1_relat_1(B_111))
      | k9_relat_1(B_111,k1_tarski(A_110)) != k1_xboole_0
      | ~ v1_relat_1(B_111) ) ),
    inference(resolution,[status(thm)],[c_571,c_63])).

tff(c_593,plain,
    ( k9_relat_1('#skF_6',k1_tarski('#skF_5')) != k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_530,c_590])).

tff(c_596,plain,(
    k9_relat_1('#skF_6',k1_tarski('#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_593])).

tff(c_599,plain,
    ( k11_relat_1('#skF_6','#skF_5') != k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_596])).

tff(c_602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_529,c_599])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:11:21 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.41  
% 2.69/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.41  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 2.69/1.41  
% 2.69/1.41  %Foreground sorts:
% 2.69/1.41  
% 2.69/1.41  
% 2.69/1.41  %Background operators:
% 2.69/1.41  
% 2.69/1.41  
% 2.69/1.41  %Foreground operators:
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.69/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.69/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.69/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.69/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.69/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.41  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.69/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.69/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.69/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.69/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.69/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.69/1.41  
% 2.69/1.43  tff(f_71, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.69/1.43  tff(f_51, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.69/1.43  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.69/1.43  tff(f_38, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.69/1.43  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 2.69/1.43  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.69/1.43  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 2.69/1.43  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.69/1.43  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.69/1.43  tff(c_32, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.69/1.43  tff(c_34, plain, (k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | ~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.69/1.43  tff(c_76, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_34])).
% 2.69/1.43  tff(c_40, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6')) | k11_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.69/1.43  tff(c_77, plain, (k11_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 2.69/1.43  tff(c_290, plain, (![A_84, B_85]: (r2_hidden(k4_tarski('#skF_1'(A_84, B_85), '#skF_2'(A_84, B_85)), A_84) | r2_hidden('#skF_3'(A_84, B_85), B_85) | k1_relat_1(A_84)=B_85)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.69/1.43  tff(c_4, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.43  tff(c_60, plain, (![A_40, C_41, B_42]: (~r2_hidden(A_40, C_41) | ~r1_xboole_0(k2_tarski(A_40, B_42), C_41))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.69/1.43  tff(c_68, plain, (![A_40]: (~r2_hidden(A_40, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_60])).
% 2.69/1.43  tff(c_342, plain, (![B_86]: (r2_hidden('#skF_3'(k1_xboole_0, B_86), B_86) | k1_relat_1(k1_xboole_0)=B_86)), inference(resolution, [status(thm)], [c_290, c_68])).
% 2.69/1.43  tff(c_386, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_342, c_68])).
% 2.69/1.43  tff(c_341, plain, (![B_85]: (r2_hidden('#skF_3'(k1_xboole_0, B_85), B_85) | k1_relat_1(k1_xboole_0)=B_85)), inference(resolution, [status(thm)], [c_290, c_68])).
% 2.69/1.43  tff(c_432, plain, (![B_90]: (r2_hidden('#skF_3'(k1_xboole_0, B_90), B_90) | k1_xboole_0=B_90)), inference(demodulation, [status(thm), theory('equality')], [c_386, c_341])).
% 2.69/1.43  tff(c_130, plain, (![A_58, B_59, C_60]: (r2_hidden(k4_tarski(A_58, B_59), C_60) | ~r2_hidden(B_59, k11_relat_1(C_60, A_58)) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.69/1.43  tff(c_14, plain, (![C_26, A_11, D_29]: (r2_hidden(C_26, k1_relat_1(A_11)) | ~r2_hidden(k4_tarski(C_26, D_29), A_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.69/1.43  tff(c_138, plain, (![A_58, C_60, B_59]: (r2_hidden(A_58, k1_relat_1(C_60)) | ~r2_hidden(B_59, k11_relat_1(C_60, A_58)) | ~v1_relat_1(C_60))), inference(resolution, [status(thm)], [c_130, c_14])).
% 2.69/1.43  tff(c_485, plain, (![A_93, C_94]: (r2_hidden(A_93, k1_relat_1(C_94)) | ~v1_relat_1(C_94) | k11_relat_1(C_94, A_93)=k1_xboole_0)), inference(resolution, [status(thm)], [c_432, c_138])).
% 2.69/1.43  tff(c_507, plain, (~v1_relat_1('#skF_6') | k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_485, c_76])).
% 2.69/1.43  tff(c_519, plain, (k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_507])).
% 2.69/1.43  tff(c_521, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_519])).
% 2.69/1.43  tff(c_522, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_40])).
% 2.69/1.43  tff(c_528, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_522])).
% 2.69/1.43  tff(c_529, plain, (k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 2.69/1.43  tff(c_10, plain, (![A_8, B_10]: (k9_relat_1(A_8, k1_tarski(B_10))=k11_relat_1(A_8, B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.69/1.43  tff(c_530, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_34])).
% 2.69/1.43  tff(c_547, plain, (![B_100, A_101]: (r1_xboole_0(k1_relat_1(B_100), A_101) | k9_relat_1(B_100, A_101)!=k1_xboole_0 | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.69/1.43  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.43  tff(c_571, plain, (![A_108, B_109]: (r1_xboole_0(A_108, k1_relat_1(B_109)) | k9_relat_1(B_109, A_108)!=k1_xboole_0 | ~v1_relat_1(B_109))), inference(resolution, [status(thm)], [c_547, c_2])).
% 2.69/1.43  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.69/1.43  tff(c_63, plain, (![A_4, C_41]: (~r2_hidden(A_4, C_41) | ~r1_xboole_0(k1_tarski(A_4), C_41))), inference(superposition, [status(thm), theory('equality')], [c_6, c_60])).
% 2.69/1.43  tff(c_590, plain, (![A_110, B_111]: (~r2_hidden(A_110, k1_relat_1(B_111)) | k9_relat_1(B_111, k1_tarski(A_110))!=k1_xboole_0 | ~v1_relat_1(B_111))), inference(resolution, [status(thm)], [c_571, c_63])).
% 2.69/1.43  tff(c_593, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_5'))!=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_530, c_590])).
% 2.69/1.43  tff(c_596, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_593])).
% 2.69/1.43  tff(c_599, plain, (k11_relat_1('#skF_6', '#skF_5')!=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_10, c_596])).
% 2.69/1.43  tff(c_602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_529, c_599])).
% 2.69/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.43  
% 2.69/1.43  Inference rules
% 2.69/1.43  ----------------------
% 2.69/1.43  #Ref     : 0
% 2.69/1.43  #Sup     : 116
% 2.69/1.43  #Fact    : 0
% 2.69/1.43  #Define  : 0
% 2.69/1.43  #Split   : 4
% 2.69/1.43  #Chain   : 0
% 2.69/1.43  #Close   : 0
% 2.69/1.43  
% 2.69/1.43  Ordering : KBO
% 2.69/1.43  
% 2.69/1.43  Simplification rules
% 2.69/1.43  ----------------------
% 2.69/1.43  #Subsume      : 25
% 2.69/1.43  #Demod        : 48
% 2.69/1.43  #Tautology    : 30
% 2.69/1.43  #SimpNegUnit  : 4
% 2.69/1.43  #BackRed      : 7
% 2.69/1.43  
% 2.69/1.43  #Partial instantiations: 0
% 2.69/1.43  #Strategies tried      : 1
% 2.69/1.43  
% 2.69/1.43  Timing (in seconds)
% 2.69/1.43  ----------------------
% 2.69/1.43  Preprocessing        : 0.33
% 2.69/1.43  Parsing              : 0.17
% 2.69/1.43  CNF conversion       : 0.03
% 2.69/1.43  Main loop            : 0.29
% 2.69/1.43  Inferencing          : 0.11
% 2.69/1.43  Reduction            : 0.08
% 2.69/1.43  Demodulation         : 0.05
% 2.69/1.43  BG Simplification    : 0.02
% 2.69/1.43  Subsumption          : 0.06
% 2.69/1.43  Abstraction          : 0.02
% 2.69/1.43  MUC search           : 0.00
% 2.69/1.43  Cooper               : 0.00
% 2.69/1.43  Total                : 0.65
% 2.69/1.43  Index Insertion      : 0.00
% 2.69/1.43  Index Deletion       : 0.00
% 2.69/1.43  Index Matching       : 0.00
% 2.69/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
