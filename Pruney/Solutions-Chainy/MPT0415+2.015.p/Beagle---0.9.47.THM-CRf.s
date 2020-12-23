%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:47 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 117 expanded)
%              Number of leaves         :   24 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  102 ( 237 expanded)
%              Number of equality atoms :   27 (  82 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_44,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_600,plain,(
    ! [A_103,B_104,C_105] :
      ( r2_hidden('#skF_1'(A_103,B_104,C_105),A_103)
      | r2_hidden('#skF_2'(A_103,B_104,C_105),C_105)
      | k4_xboole_0(A_103,B_104) = C_105 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ! [D_33,B_34,A_35] :
      ( ~ r2_hidden(D_33,B_34)
      | ~ r2_hidden(D_33,k4_xboole_0(A_35,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [D_33,A_10] :
      ( ~ r2_hidden(D_33,A_10)
      | ~ r2_hidden(D_33,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_71])).

tff(c_1477,plain,(
    ! [A_175,B_176,C_177] :
      ( ~ r2_hidden('#skF_1'(A_175,B_176,C_177),k1_xboole_0)
      | r2_hidden('#skF_2'(A_175,B_176,C_177),C_177)
      | k4_xboole_0(A_175,B_176) = C_177 ) ),
    inference(resolution,[status(thm)],[c_600,c_74])).

tff(c_1486,plain,(
    ! [B_2,C_3] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_2,C_3),C_3)
      | k4_xboole_0(k1_xboole_0,B_2) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_1477])).

tff(c_1492,plain,(
    ! [B_2,C_3] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_2,C_3),C_3)
      | k1_xboole_0 = C_3 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1486])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_76,plain,(
    ! [A_38,C_39,B_40] :
      ( m1_subset_1(A_38,C_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(C_39))
      | ~ r2_hidden(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_81,plain,(
    ! [A_38] :
      ( m1_subset_1(A_38,k1_zfmisc_1('#skF_6'))
      | ~ r2_hidden(A_38,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_54,c_76])).

tff(c_30,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    k7_setfam_1('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_108,plain,(
    ! [A_52,B_53] :
      ( k7_setfam_1(A_52,k7_setfam_1(A_52,B_53)) = B_53
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k1_zfmisc_1(A_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_110,plain,(
    k7_setfam_1('#skF_6',k7_setfam_1('#skF_6','#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_54,c_108])).

tff(c_115,plain,(
    k7_setfam_1('#skF_6',k1_xboole_0) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_110])).

tff(c_2038,plain,(
    ! [A_208,D_209,B_210] :
      ( r2_hidden(k3_subset_1(A_208,D_209),B_210)
      | ~ r2_hidden(D_209,k7_setfam_1(A_208,B_210))
      | ~ m1_subset_1(D_209,k1_zfmisc_1(A_208))
      | ~ m1_subset_1(k7_setfam_1(A_208,B_210),k1_zfmisc_1(k1_zfmisc_1(A_208)))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(k1_zfmisc_1(A_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2042,plain,(
    ! [D_209] :
      ( r2_hidden(k3_subset_1('#skF_6',D_209),k1_xboole_0)
      | ~ r2_hidden(D_209,k7_setfam_1('#skF_6',k1_xboole_0))
      | ~ m1_subset_1(D_209,k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_6')))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_2038])).

tff(c_2048,plain,(
    ! [D_209] :
      ( r2_hidden(k3_subset_1('#skF_6',D_209),k1_xboole_0)
      | ~ r2_hidden(D_209,'#skF_7')
      | ~ m1_subset_1(D_209,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_54,c_115,c_2042])).

tff(c_2552,plain,(
    ! [D_227] :
      ( r2_hidden(k3_subset_1('#skF_6',D_227),k1_xboole_0)
      | ~ r2_hidden(D_227,'#skF_7')
      | ~ m1_subset_1(D_227,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_54,c_115,c_2042])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_644,plain,(
    ! [A_103,B_104] :
      ( r2_hidden('#skF_2'(A_103,B_104,A_103),A_103)
      | k4_xboole_0(A_103,B_104) = A_103 ) ),
    inference(resolution,[status(thm)],[c_600,c_14])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1634,plain,(
    ! [A_190,B_191,C_192] :
      ( ~ r2_hidden('#skF_1'(A_190,B_191,C_192),C_192)
      | r2_hidden('#skF_2'(A_190,B_191,C_192),B_191)
      | ~ r2_hidden('#skF_2'(A_190,B_191,C_192),A_190)
      | k4_xboole_0(A_190,B_191) = C_192 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1651,plain,(
    ! [A_193,B_194] :
      ( r2_hidden('#skF_2'(A_193,B_194,A_193),B_194)
      | ~ r2_hidden('#skF_2'(A_193,B_194,A_193),A_193)
      | k4_xboole_0(A_193,B_194) = A_193 ) ),
    inference(resolution,[status(thm)],[c_12,c_1634])).

tff(c_1672,plain,(
    ! [A_195,B_196] :
      ( r2_hidden('#skF_2'(A_195,B_196,A_195),B_196)
      | k4_xboole_0(A_195,B_196) = A_195 ) ),
    inference(resolution,[status(thm)],[c_644,c_1651])).

tff(c_691,plain,(
    ! [A_110,B_111] :
      ( r2_hidden('#skF_2'(A_110,B_111,A_110),A_110)
      | k4_xboole_0(A_110,B_111) = A_110 ) ),
    inference(resolution,[status(thm)],[c_600,c_14])).

tff(c_722,plain,(
    ! [A_110,B_111] :
      ( ~ r2_hidden('#skF_2'(A_110,B_111,A_110),k1_xboole_0)
      | k4_xboole_0(A_110,B_111) = A_110 ) ),
    inference(resolution,[status(thm)],[c_691,c_74])).

tff(c_1716,plain,(
    ! [A_197] : k4_xboole_0(A_197,k1_xboole_0) = A_197 ),
    inference(resolution,[status(thm)],[c_1672,c_722])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1786,plain,(
    ! [D_6,A_197] :
      ( ~ r2_hidden(D_6,k1_xboole_0)
      | ~ r2_hidden(D_6,A_197) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1716,c_4])).

tff(c_2622,plain,(
    ! [D_236,A_237] :
      ( ~ r2_hidden(k3_subset_1('#skF_6',D_236),A_237)
      | ~ r2_hidden(D_236,'#skF_7')
      | ~ m1_subset_1(D_236,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_2552,c_1786])).

tff(c_2636,plain,(
    ! [D_238] :
      ( ~ r2_hidden(D_238,'#skF_7')
      | ~ m1_subset_1(D_238,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_2048,c_2622])).

tff(c_2652,plain,(
    ! [A_239] : ~ r2_hidden(A_239,'#skF_7') ),
    inference(resolution,[status(thm)],[c_81,c_2636])).

tff(c_2668,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1492,c_2652])).

tff(c_2729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2668])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:06:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.67  
% 3.91/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.67  %$ r2_hidden > m1_subset_1 > k7_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4
% 3.91/1.67  
% 3.91/1.67  %Foreground sorts:
% 3.91/1.67  
% 3.91/1.67  
% 3.91/1.67  %Background operators:
% 3.91/1.67  
% 3.91/1.67  
% 3.91/1.67  %Foreground operators:
% 3.91/1.67  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.91/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.91/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.91/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.91/1.67  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 3.91/1.67  tff('#skF_7', type, '#skF_7': $i).
% 3.91/1.67  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.91/1.67  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.91/1.67  tff('#skF_6', type, '#skF_6': $i).
% 3.91/1.67  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.91/1.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.91/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.91/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.67  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.91/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.91/1.67  
% 3.91/1.68  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 3.91/1.68  tff(f_44, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.91/1.68  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.91/1.68  tff(f_70, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.91/1.68  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.91/1.68  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 3.91/1.68  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 3.91/1.68  tff(c_52, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.91/1.68  tff(c_28, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.91/1.68  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.91/1.68  tff(c_600, plain, (![A_103, B_104, C_105]: (r2_hidden('#skF_1'(A_103, B_104, C_105), A_103) | r2_hidden('#skF_2'(A_103, B_104, C_105), C_105) | k4_xboole_0(A_103, B_104)=C_105)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.91/1.68  tff(c_71, plain, (![D_33, B_34, A_35]: (~r2_hidden(D_33, B_34) | ~r2_hidden(D_33, k4_xboole_0(A_35, B_34)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.91/1.68  tff(c_74, plain, (![D_33, A_10]: (~r2_hidden(D_33, A_10) | ~r2_hidden(D_33, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_71])).
% 3.91/1.68  tff(c_1477, plain, (![A_175, B_176, C_177]: (~r2_hidden('#skF_1'(A_175, B_176, C_177), k1_xboole_0) | r2_hidden('#skF_2'(A_175, B_176, C_177), C_177) | k4_xboole_0(A_175, B_176)=C_177)), inference(resolution, [status(thm)], [c_600, c_74])).
% 3.91/1.68  tff(c_1486, plain, (![B_2, C_3]: (r2_hidden('#skF_2'(k1_xboole_0, B_2, C_3), C_3) | k4_xboole_0(k1_xboole_0, B_2)=C_3)), inference(resolution, [status(thm)], [c_18, c_1477])).
% 3.91/1.68  tff(c_1492, plain, (![B_2, C_3]: (r2_hidden('#skF_2'(k1_xboole_0, B_2, C_3), C_3) | k1_xboole_0=C_3)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1486])).
% 3.91/1.68  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.91/1.68  tff(c_76, plain, (![A_38, C_39, B_40]: (m1_subset_1(A_38, C_39) | ~m1_subset_1(B_40, k1_zfmisc_1(C_39)) | ~r2_hidden(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.91/1.68  tff(c_81, plain, (![A_38]: (m1_subset_1(A_38, k1_zfmisc_1('#skF_6')) | ~r2_hidden(A_38, '#skF_7'))), inference(resolution, [status(thm)], [c_54, c_76])).
% 3.91/1.68  tff(c_30, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.91/1.68  tff(c_50, plain, (k7_setfam_1('#skF_6', '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.91/1.68  tff(c_108, plain, (![A_52, B_53]: (k7_setfam_1(A_52, k7_setfam_1(A_52, B_53))=B_53 | ~m1_subset_1(B_53, k1_zfmisc_1(k1_zfmisc_1(A_52))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.91/1.68  tff(c_110, plain, (k7_setfam_1('#skF_6', k7_setfam_1('#skF_6', '#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_54, c_108])).
% 3.91/1.68  tff(c_115, plain, (k7_setfam_1('#skF_6', k1_xboole_0)='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_110])).
% 3.91/1.68  tff(c_2038, plain, (![A_208, D_209, B_210]: (r2_hidden(k3_subset_1(A_208, D_209), B_210) | ~r2_hidden(D_209, k7_setfam_1(A_208, B_210)) | ~m1_subset_1(D_209, k1_zfmisc_1(A_208)) | ~m1_subset_1(k7_setfam_1(A_208, B_210), k1_zfmisc_1(k1_zfmisc_1(A_208))) | ~m1_subset_1(B_210, k1_zfmisc_1(k1_zfmisc_1(A_208))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.91/1.68  tff(c_2042, plain, (![D_209]: (r2_hidden(k3_subset_1('#skF_6', D_209), k1_xboole_0) | ~r2_hidden(D_209, k7_setfam_1('#skF_6', k1_xboole_0)) | ~m1_subset_1(D_209, k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_115, c_2038])).
% 3.91/1.68  tff(c_2048, plain, (![D_209]: (r2_hidden(k3_subset_1('#skF_6', D_209), k1_xboole_0) | ~r2_hidden(D_209, '#skF_7') | ~m1_subset_1(D_209, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_54, c_115, c_2042])).
% 3.91/1.68  tff(c_2552, plain, (![D_227]: (r2_hidden(k3_subset_1('#skF_6', D_227), k1_xboole_0) | ~r2_hidden(D_227, '#skF_7') | ~m1_subset_1(D_227, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_54, c_115, c_2042])).
% 3.91/1.68  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.91/1.68  tff(c_644, plain, (![A_103, B_104]: (r2_hidden('#skF_2'(A_103, B_104, A_103), A_103) | k4_xboole_0(A_103, B_104)=A_103)), inference(resolution, [status(thm)], [c_600, c_14])).
% 3.91/1.68  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.91/1.68  tff(c_1634, plain, (![A_190, B_191, C_192]: (~r2_hidden('#skF_1'(A_190, B_191, C_192), C_192) | r2_hidden('#skF_2'(A_190, B_191, C_192), B_191) | ~r2_hidden('#skF_2'(A_190, B_191, C_192), A_190) | k4_xboole_0(A_190, B_191)=C_192)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.91/1.68  tff(c_1651, plain, (![A_193, B_194]: (r2_hidden('#skF_2'(A_193, B_194, A_193), B_194) | ~r2_hidden('#skF_2'(A_193, B_194, A_193), A_193) | k4_xboole_0(A_193, B_194)=A_193)), inference(resolution, [status(thm)], [c_12, c_1634])).
% 3.91/1.68  tff(c_1672, plain, (![A_195, B_196]: (r2_hidden('#skF_2'(A_195, B_196, A_195), B_196) | k4_xboole_0(A_195, B_196)=A_195)), inference(resolution, [status(thm)], [c_644, c_1651])).
% 3.91/1.68  tff(c_691, plain, (![A_110, B_111]: (r2_hidden('#skF_2'(A_110, B_111, A_110), A_110) | k4_xboole_0(A_110, B_111)=A_110)), inference(resolution, [status(thm)], [c_600, c_14])).
% 3.91/1.68  tff(c_722, plain, (![A_110, B_111]: (~r2_hidden('#skF_2'(A_110, B_111, A_110), k1_xboole_0) | k4_xboole_0(A_110, B_111)=A_110)), inference(resolution, [status(thm)], [c_691, c_74])).
% 3.91/1.68  tff(c_1716, plain, (![A_197]: (k4_xboole_0(A_197, k1_xboole_0)=A_197)), inference(resolution, [status(thm)], [c_1672, c_722])).
% 3.91/1.68  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.91/1.68  tff(c_1786, plain, (![D_6, A_197]: (~r2_hidden(D_6, k1_xboole_0) | ~r2_hidden(D_6, A_197))), inference(superposition, [status(thm), theory('equality')], [c_1716, c_4])).
% 3.91/1.68  tff(c_2622, plain, (![D_236, A_237]: (~r2_hidden(k3_subset_1('#skF_6', D_236), A_237) | ~r2_hidden(D_236, '#skF_7') | ~m1_subset_1(D_236, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_2552, c_1786])).
% 3.91/1.68  tff(c_2636, plain, (![D_238]: (~r2_hidden(D_238, '#skF_7') | ~m1_subset_1(D_238, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_2048, c_2622])).
% 3.91/1.68  tff(c_2652, plain, (![A_239]: (~r2_hidden(A_239, '#skF_7'))), inference(resolution, [status(thm)], [c_81, c_2636])).
% 3.91/1.68  tff(c_2668, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_1492, c_2652])).
% 3.91/1.68  tff(c_2729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_2668])).
% 3.91/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.68  
% 3.91/1.68  Inference rules
% 3.91/1.68  ----------------------
% 3.91/1.68  #Ref     : 0
% 3.91/1.68  #Sup     : 581
% 3.91/1.68  #Fact    : 0
% 3.91/1.68  #Define  : 0
% 3.91/1.68  #Split   : 0
% 3.91/1.68  #Chain   : 0
% 3.91/1.68  #Close   : 0
% 3.91/1.68  
% 3.91/1.68  Ordering : KBO
% 3.91/1.68  
% 3.91/1.68  Simplification rules
% 3.91/1.68  ----------------------
% 3.91/1.68  #Subsume      : 207
% 3.91/1.68  #Demod        : 321
% 3.91/1.68  #Tautology    : 221
% 3.91/1.68  #SimpNegUnit  : 2
% 3.91/1.68  #BackRed      : 1
% 3.91/1.68  
% 3.91/1.68  #Partial instantiations: 0
% 3.91/1.68  #Strategies tried      : 1
% 3.91/1.68  
% 3.91/1.68  Timing (in seconds)
% 3.91/1.68  ----------------------
% 3.91/1.69  Preprocessing        : 0.30
% 3.91/1.69  Parsing              : 0.15
% 3.91/1.69  CNF conversion       : 0.02
% 3.91/1.69  Main loop            : 0.62
% 3.91/1.69  Inferencing          : 0.24
% 3.91/1.69  Reduction            : 0.17
% 3.91/1.69  Demodulation         : 0.12
% 3.91/1.69  BG Simplification    : 0.03
% 3.91/1.69  Subsumption          : 0.14
% 3.91/1.69  Abstraction          : 0.03
% 3.91/1.69  MUC search           : 0.00
% 3.91/1.69  Cooper               : 0.00
% 3.91/1.69  Total                : 0.95
% 3.91/1.69  Index Insertion      : 0.00
% 3.91/1.69  Index Deletion       : 0.00
% 3.91/1.69  Index Matching       : 0.00
% 3.91/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
