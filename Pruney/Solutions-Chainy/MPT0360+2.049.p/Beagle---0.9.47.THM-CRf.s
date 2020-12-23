%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:25 EST 2020

% Result     : Theorem 6.54s
% Output     : CNFRefutation 6.54s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 296 expanded)
%              Number of leaves         :   23 ( 112 expanded)
%              Depth                    :   14
%              Number of atoms          :  119 ( 750 expanded)
%              Number of equality atoms :   33 ( 191 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_306,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden('#skF_2'(A_70,B_71,C_72),A_70)
      | r2_hidden('#skF_3'(A_70,B_71,C_72),C_72)
      | k4_xboole_0(A_70,B_71) = C_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_347,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_3'(A_70,B_71,A_70),A_70)
      | k4_xboole_0(A_70,B_71) = A_70 ) ),
    inference(resolution,[status(thm)],[c_306,c_20])).

tff(c_1205,plain,(
    ! [A_150,B_151,C_152] :
      ( r2_hidden('#skF_2'(A_150,B_151,C_152),A_150)
      | r2_hidden('#skF_3'(A_150,B_151,C_152),B_151)
      | ~ r2_hidden('#skF_3'(A_150,B_151,C_152),A_150)
      | k4_xboole_0(A_150,B_151) = C_152 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),B_7)
      | ~ r2_hidden('#skF_3'(A_6,B_7,C_8),A_6)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1893,plain,(
    ! [A_168,B_169] :
      ( r2_hidden('#skF_3'(A_168,B_169,A_168),B_169)
      | ~ r2_hidden('#skF_3'(A_168,B_169,A_168),A_168)
      | k4_xboole_0(A_168,B_169) = A_168 ) ),
    inference(resolution,[status(thm)],[c_1205,c_14])).

tff(c_1920,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_3'(A_70,B_71,A_70),B_71)
      | k4_xboole_0(A_70,B_71) = A_70 ) ),
    inference(resolution,[status(thm)],[c_347,c_1893])).

tff(c_358,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_3'(A_73,B_74,A_73),A_73)
      | k4_xboole_0(A_73,B_74) = A_73 ) ),
    inference(resolution,[status(thm)],[c_306,c_20])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_512,plain,(
    ! [A_94,B_95,B_96] :
      ( r2_hidden('#skF_3'(A_94,B_95,A_94),B_96)
      | ~ r1_tarski(A_94,B_96)
      | k4_xboole_0(A_94,B_95) = A_94 ) ),
    inference(resolution,[status(thm)],[c_358,c_2])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_73,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k3_subset_1(A_34,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_77,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k3_subset_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_73])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_84,plain,(
    ! [D_11] :
      ( ~ r2_hidden(D_11,'#skF_6')
      | ~ r2_hidden(D_11,k3_subset_1('#skF_4','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_10])).

tff(c_5478,plain,(
    ! [A_259,B_260] :
      ( ~ r2_hidden('#skF_3'(A_259,B_260,A_259),'#skF_6')
      | ~ r1_tarski(A_259,k3_subset_1('#skF_4','#skF_6'))
      | k4_xboole_0(A_259,B_260) = A_259 ) ),
    inference(resolution,[status(thm)],[c_512,c_84])).

tff(c_5514,plain,(
    ! [A_261] :
      ( ~ r1_tarski(A_261,k3_subset_1('#skF_4','#skF_6'))
      | k4_xboole_0(A_261,'#skF_6') = A_261 ) ),
    inference(resolution,[status(thm)],[c_1920,c_5478])).

tff(c_5560,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_5514])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_475,plain,(
    ! [A_89,B_90,C_91] :
      ( ~ r2_hidden('#skF_2'(A_89,B_90,C_91),B_90)
      | r2_hidden('#skF_3'(A_89,B_90,C_91),C_91)
      | k4_xboole_0(A_89,B_90) = C_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_488,plain,(
    ! [A_92,C_93] :
      ( r2_hidden('#skF_3'(A_92,A_92,C_93),C_93)
      | k4_xboole_0(A_92,A_92) = C_93 ) ),
    inference(resolution,[status(thm)],[c_24,c_475])).

tff(c_509,plain,(
    ! [A_92,C_93,B_2] :
      ( r2_hidden('#skF_3'(A_92,A_92,C_93),B_2)
      | ~ r1_tarski(C_93,B_2)
      | k4_xboole_0(A_92,A_92) = C_93 ) ),
    inference(resolution,[status(thm)],[c_488,c_2])).

tff(c_785,plain,(
    ! [A_124,A_125,B_126] :
      ( ~ r2_hidden('#skF_3'(A_124,A_124,k4_xboole_0(A_125,B_126)),B_126)
      | k4_xboole_0(A_125,B_126) = k4_xboole_0(A_124,A_124) ) ),
    inference(resolution,[status(thm)],[c_488,c_10])).

tff(c_805,plain,(
    ! [A_125,B_2,A_92] :
      ( ~ r1_tarski(k4_xboole_0(A_125,B_2),B_2)
      | k4_xboole_0(A_92,A_92) = k4_xboole_0(A_125,B_2) ) ),
    inference(resolution,[status(thm)],[c_509,c_785])).

tff(c_5593,plain,(
    ! [A_92] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_6')
      | k4_xboole_0(k1_xboole_0,'#skF_6') = k4_xboole_0(A_92,A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5560,c_805])).

tff(c_5643,plain,(
    ! [A_92] : k4_xboole_0(A_92,A_92) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5560,c_28,c_5593])).

tff(c_36,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_69,plain,(
    ! [C_31,B_32,A_33] :
      ( r2_hidden(C_31,B_32)
      | ~ r2_hidden(C_31,A_33)
      | ~ r1_tarski(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [A_1,B_2,B_32] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_32)
      | ~ r1_tarski(A_1,B_32)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_120,plain,(
    ! [A_41,B_42,B_43] :
      ( r2_hidden('#skF_1'(A_41,B_42),B_43)
      | ~ r1_tarski(A_41,B_43)
      | r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_271,plain,(
    ! [A_63,B_64,B_65,A_66] :
      ( ~ r2_hidden('#skF_1'(A_63,B_64),B_65)
      | ~ r1_tarski(A_63,k4_xboole_0(A_66,B_65))
      | r1_tarski(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_120,c_10])).

tff(c_382,plain,(
    ! [A_75,A_76,B_77,B_78] :
      ( ~ r1_tarski(A_75,k4_xboole_0(A_76,B_77))
      | ~ r1_tarski(A_75,B_77)
      | r1_tarski(A_75,B_78) ) ),
    inference(resolution,[status(thm)],[c_72,c_271])).

tff(c_405,plain,(
    ! [A_79,B_80] :
      ( ~ r1_tarski(A_79,k3_subset_1('#skF_4','#skF_6'))
      | ~ r1_tarski(A_79,'#skF_6')
      | r1_tarski(A_79,B_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_382])).

tff(c_416,plain,(
    ! [B_80] :
      ( ~ r1_tarski('#skF_5','#skF_6')
      | r1_tarski('#skF_5',B_80) ) ),
    inference(resolution,[status(thm)],[c_34,c_405])).

tff(c_427,plain,(
    ! [B_80] : r1_tarski('#skF_5',B_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_416])).

tff(c_379,plain,(
    ! [A_73,B_74,B_2] :
      ( r2_hidden('#skF_3'(A_73,B_74,A_73),B_2)
      | ~ r1_tarski(A_73,B_2)
      | k4_xboole_0(A_73,B_74) = A_73 ) ),
    inference(resolution,[status(thm)],[c_358,c_2])).

tff(c_485,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,A_6,C_8),C_8)
      | k4_xboole_0(A_6,A_6) = C_8 ) ),
    inference(resolution,[status(thm)],[c_24,c_475])).

tff(c_7529,plain,(
    ! [A_318,C_319] :
      ( r2_hidden('#skF_3'(A_318,A_318,C_319),C_319)
      | k1_xboole_0 = C_319 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5643,c_485])).

tff(c_5556,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_427,c_5514])).

tff(c_6127,plain,(
    ! [D_11] :
      ( ~ r2_hidden(D_11,'#skF_6')
      | ~ r2_hidden(D_11,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5556,c_10])).

tff(c_7543,plain,(
    ! [A_318] :
      ( ~ r2_hidden('#skF_3'(A_318,A_318,'#skF_5'),'#skF_6')
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_7529,c_6127])).

tff(c_7590,plain,(
    ! [A_320] : ~ r2_hidden('#skF_3'(A_320,A_320,'#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_7543])).

tff(c_7602,plain,
    ( ~ r1_tarski('#skF_5','#skF_6')
    | k4_xboole_0('#skF_5','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_379,c_7590])).

tff(c_7605,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5643,c_427,c_7602])).

tff(c_7607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_7605])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:17:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.54/2.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.54/2.33  
% 6.54/2.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.54/2.33  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 6.54/2.33  
% 6.54/2.33  %Foreground sorts:
% 6.54/2.33  
% 6.54/2.33  
% 6.54/2.33  %Background operators:
% 6.54/2.33  
% 6.54/2.33  
% 6.54/2.33  %Foreground operators:
% 6.54/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.54/2.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.54/2.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.54/2.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.54/2.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.54/2.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.54/2.33  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.54/2.33  tff('#skF_5', type, '#skF_5': $i).
% 6.54/2.33  tff('#skF_6', type, '#skF_6': $i).
% 6.54/2.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.54/2.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.54/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.54/2.33  tff('#skF_4', type, '#skF_4': $i).
% 6.54/2.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.54/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.54/2.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.54/2.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.54/2.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.54/2.33  
% 6.54/2.34  tff(f_59, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 6.54/2.34  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.54/2.34  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.54/2.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.54/2.34  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 6.54/2.34  tff(c_32, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.54/2.34  tff(c_28, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.54/2.34  tff(c_306, plain, (![A_70, B_71, C_72]: (r2_hidden('#skF_2'(A_70, B_71, C_72), A_70) | r2_hidden('#skF_3'(A_70, B_71, C_72), C_72) | k4_xboole_0(A_70, B_71)=C_72)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.54/2.34  tff(c_20, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.54/2.34  tff(c_347, plain, (![A_70, B_71]: (r2_hidden('#skF_3'(A_70, B_71, A_70), A_70) | k4_xboole_0(A_70, B_71)=A_70)), inference(resolution, [status(thm)], [c_306, c_20])).
% 6.54/2.34  tff(c_1205, plain, (![A_150, B_151, C_152]: (r2_hidden('#skF_2'(A_150, B_151, C_152), A_150) | r2_hidden('#skF_3'(A_150, B_151, C_152), B_151) | ~r2_hidden('#skF_3'(A_150, B_151, C_152), A_150) | k4_xboole_0(A_150, B_151)=C_152)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.54/2.34  tff(c_14, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), B_7) | ~r2_hidden('#skF_3'(A_6, B_7, C_8), A_6) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.54/2.34  tff(c_1893, plain, (![A_168, B_169]: (r2_hidden('#skF_3'(A_168, B_169, A_168), B_169) | ~r2_hidden('#skF_3'(A_168, B_169, A_168), A_168) | k4_xboole_0(A_168, B_169)=A_168)), inference(resolution, [status(thm)], [c_1205, c_14])).
% 6.54/2.34  tff(c_1920, plain, (![A_70, B_71]: (r2_hidden('#skF_3'(A_70, B_71, A_70), B_71) | k4_xboole_0(A_70, B_71)=A_70)), inference(resolution, [status(thm)], [c_347, c_1893])).
% 6.54/2.34  tff(c_358, plain, (![A_73, B_74]: (r2_hidden('#skF_3'(A_73, B_74, A_73), A_73) | k4_xboole_0(A_73, B_74)=A_73)), inference(resolution, [status(thm)], [c_306, c_20])).
% 6.54/2.34  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.54/2.34  tff(c_512, plain, (![A_94, B_95, B_96]: (r2_hidden('#skF_3'(A_94, B_95, A_94), B_96) | ~r1_tarski(A_94, B_96) | k4_xboole_0(A_94, B_95)=A_94)), inference(resolution, [status(thm)], [c_358, c_2])).
% 6.54/2.34  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.54/2.34  tff(c_73, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k3_subset_1(A_34, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.54/2.34  tff(c_77, plain, (k4_xboole_0('#skF_4', '#skF_6')=k3_subset_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_38, c_73])).
% 6.54/2.34  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.54/2.34  tff(c_84, plain, (![D_11]: (~r2_hidden(D_11, '#skF_6') | ~r2_hidden(D_11, k3_subset_1('#skF_4', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_77, c_10])).
% 6.54/2.34  tff(c_5478, plain, (![A_259, B_260]: (~r2_hidden('#skF_3'(A_259, B_260, A_259), '#skF_6') | ~r1_tarski(A_259, k3_subset_1('#skF_4', '#skF_6')) | k4_xboole_0(A_259, B_260)=A_259)), inference(resolution, [status(thm)], [c_512, c_84])).
% 6.54/2.34  tff(c_5514, plain, (![A_261]: (~r1_tarski(A_261, k3_subset_1('#skF_4', '#skF_6')) | k4_xboole_0(A_261, '#skF_6')=A_261)), inference(resolution, [status(thm)], [c_1920, c_5478])).
% 6.54/2.34  tff(c_5560, plain, (k4_xboole_0(k1_xboole_0, '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_5514])).
% 6.54/2.34  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.54/2.34  tff(c_475, plain, (![A_89, B_90, C_91]: (~r2_hidden('#skF_2'(A_89, B_90, C_91), B_90) | r2_hidden('#skF_3'(A_89, B_90, C_91), C_91) | k4_xboole_0(A_89, B_90)=C_91)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.54/2.34  tff(c_488, plain, (![A_92, C_93]: (r2_hidden('#skF_3'(A_92, A_92, C_93), C_93) | k4_xboole_0(A_92, A_92)=C_93)), inference(resolution, [status(thm)], [c_24, c_475])).
% 6.54/2.34  tff(c_509, plain, (![A_92, C_93, B_2]: (r2_hidden('#skF_3'(A_92, A_92, C_93), B_2) | ~r1_tarski(C_93, B_2) | k4_xboole_0(A_92, A_92)=C_93)), inference(resolution, [status(thm)], [c_488, c_2])).
% 6.54/2.34  tff(c_785, plain, (![A_124, A_125, B_126]: (~r2_hidden('#skF_3'(A_124, A_124, k4_xboole_0(A_125, B_126)), B_126) | k4_xboole_0(A_125, B_126)=k4_xboole_0(A_124, A_124))), inference(resolution, [status(thm)], [c_488, c_10])).
% 6.54/2.34  tff(c_805, plain, (![A_125, B_2, A_92]: (~r1_tarski(k4_xboole_0(A_125, B_2), B_2) | k4_xboole_0(A_92, A_92)=k4_xboole_0(A_125, B_2))), inference(resolution, [status(thm)], [c_509, c_785])).
% 6.54/2.34  tff(c_5593, plain, (![A_92]: (~r1_tarski(k1_xboole_0, '#skF_6') | k4_xboole_0(k1_xboole_0, '#skF_6')=k4_xboole_0(A_92, A_92))), inference(superposition, [status(thm), theory('equality')], [c_5560, c_805])).
% 6.54/2.34  tff(c_5643, plain, (![A_92]: (k4_xboole_0(A_92, A_92)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5560, c_28, c_5593])).
% 6.54/2.34  tff(c_36, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.54/2.34  tff(c_34, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.54/2.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.54/2.34  tff(c_69, plain, (![C_31, B_32, A_33]: (r2_hidden(C_31, B_32) | ~r2_hidden(C_31, A_33) | ~r1_tarski(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.54/2.34  tff(c_72, plain, (![A_1, B_2, B_32]: (r2_hidden('#skF_1'(A_1, B_2), B_32) | ~r1_tarski(A_1, B_32) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_69])).
% 6.54/2.34  tff(c_120, plain, (![A_41, B_42, B_43]: (r2_hidden('#skF_1'(A_41, B_42), B_43) | ~r1_tarski(A_41, B_43) | r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_6, c_69])).
% 6.54/2.34  tff(c_271, plain, (![A_63, B_64, B_65, A_66]: (~r2_hidden('#skF_1'(A_63, B_64), B_65) | ~r1_tarski(A_63, k4_xboole_0(A_66, B_65)) | r1_tarski(A_63, B_64))), inference(resolution, [status(thm)], [c_120, c_10])).
% 6.54/2.34  tff(c_382, plain, (![A_75, A_76, B_77, B_78]: (~r1_tarski(A_75, k4_xboole_0(A_76, B_77)) | ~r1_tarski(A_75, B_77) | r1_tarski(A_75, B_78))), inference(resolution, [status(thm)], [c_72, c_271])).
% 6.54/2.34  tff(c_405, plain, (![A_79, B_80]: (~r1_tarski(A_79, k3_subset_1('#skF_4', '#skF_6')) | ~r1_tarski(A_79, '#skF_6') | r1_tarski(A_79, B_80))), inference(superposition, [status(thm), theory('equality')], [c_77, c_382])).
% 6.54/2.34  tff(c_416, plain, (![B_80]: (~r1_tarski('#skF_5', '#skF_6') | r1_tarski('#skF_5', B_80))), inference(resolution, [status(thm)], [c_34, c_405])).
% 6.54/2.34  tff(c_427, plain, (![B_80]: (r1_tarski('#skF_5', B_80))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_416])).
% 6.54/2.34  tff(c_379, plain, (![A_73, B_74, B_2]: (r2_hidden('#skF_3'(A_73, B_74, A_73), B_2) | ~r1_tarski(A_73, B_2) | k4_xboole_0(A_73, B_74)=A_73)), inference(resolution, [status(thm)], [c_358, c_2])).
% 6.54/2.34  tff(c_485, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, A_6, C_8), C_8) | k4_xboole_0(A_6, A_6)=C_8)), inference(resolution, [status(thm)], [c_24, c_475])).
% 6.54/2.34  tff(c_7529, plain, (![A_318, C_319]: (r2_hidden('#skF_3'(A_318, A_318, C_319), C_319) | k1_xboole_0=C_319)), inference(demodulation, [status(thm), theory('equality')], [c_5643, c_485])).
% 6.54/2.34  tff(c_5556, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_427, c_5514])).
% 6.54/2.34  tff(c_6127, plain, (![D_11]: (~r2_hidden(D_11, '#skF_6') | ~r2_hidden(D_11, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5556, c_10])).
% 6.54/2.34  tff(c_7543, plain, (![A_318]: (~r2_hidden('#skF_3'(A_318, A_318, '#skF_5'), '#skF_6') | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_7529, c_6127])).
% 6.54/2.34  tff(c_7590, plain, (![A_320]: (~r2_hidden('#skF_3'(A_320, A_320, '#skF_5'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_32, c_7543])).
% 6.54/2.34  tff(c_7602, plain, (~r1_tarski('#skF_5', '#skF_6') | k4_xboole_0('#skF_5', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_379, c_7590])).
% 6.54/2.34  tff(c_7605, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5643, c_427, c_7602])).
% 6.54/2.34  tff(c_7607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_7605])).
% 6.54/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.54/2.34  
% 6.54/2.34  Inference rules
% 6.54/2.34  ----------------------
% 6.54/2.34  #Ref     : 0
% 6.54/2.34  #Sup     : 1901
% 6.54/2.34  #Fact    : 0
% 6.54/2.34  #Define  : 0
% 6.54/2.34  #Split   : 6
% 6.54/2.34  #Chain   : 0
% 6.54/2.34  #Close   : 0
% 6.54/2.34  
% 6.54/2.34  Ordering : KBO
% 6.54/2.34  
% 6.54/2.34  Simplification rules
% 6.54/2.34  ----------------------
% 6.54/2.34  #Subsume      : 589
% 6.54/2.34  #Demod        : 1269
% 6.54/2.34  #Tautology    : 555
% 6.54/2.34  #SimpNegUnit  : 23
% 6.54/2.34  #BackRed      : 71
% 6.54/2.34  
% 6.54/2.34  #Partial instantiations: 0
% 6.54/2.34  #Strategies tried      : 1
% 6.54/2.34  
% 6.54/2.34  Timing (in seconds)
% 6.54/2.34  ----------------------
% 6.54/2.35  Preprocessing        : 0.28
% 6.54/2.35  Parsing              : 0.14
% 6.54/2.35  CNF conversion       : 0.02
% 6.54/2.35  Main loop            : 1.29
% 6.54/2.35  Inferencing          : 0.38
% 6.54/2.35  Reduction            : 0.45
% 6.54/2.35  Demodulation         : 0.33
% 6.54/2.35  BG Simplification    : 0.04
% 6.54/2.35  Subsumption          : 0.32
% 6.54/2.35  Abstraction          : 0.06
% 6.54/2.35  MUC search           : 0.00
% 6.54/2.35  Cooper               : 0.00
% 6.54/2.35  Total                : 1.60
% 6.54/2.35  Index Insertion      : 0.00
% 6.54/2.35  Index Deletion       : 0.00
% 6.54/2.35  Index Matching       : 0.00
% 6.54/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
