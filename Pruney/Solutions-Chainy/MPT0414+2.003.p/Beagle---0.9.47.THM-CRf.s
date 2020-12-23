%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:43 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 207 expanded)
%              Number of leaves         :   18 (  76 expanded)
%              Depth                    :   11
%              Number of atoms          :  140 ( 511 expanded)
%              Number of equality atoms :    8 (  32 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(A))
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_28,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_49,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_57,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_49])).

tff(c_22,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_137,plain,(
    ! [C_40,B_41,A_42] :
      ( r2_hidden(C_40,B_41)
      | ~ r2_hidden(C_40,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_229,plain,(
    ! [A_53,B_54,B_55] :
      ( r2_hidden('#skF_1'(A_53,B_54),B_55)
      | ~ r1_tarski(A_53,B_55)
      | r1_tarski(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_6,c_137])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( m1_subset_1(B_9,A_8)
      | ~ r2_hidden(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_325,plain,(
    ! [A_64,B_65,B_66] :
      ( m1_subset_1('#skF_1'(A_64,B_65),B_66)
      | v1_xboole_0(B_66)
      | ~ r1_tarski(A_64,B_66)
      | r1_tarski(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_229,c_14])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_341,plain,(
    ! [A_64,B_65,B_12] :
      ( r1_tarski('#skF_1'(A_64,B_65),B_12)
      | v1_xboole_0(k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_64,k1_zfmisc_1(B_12))
      | r1_tarski(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_325,c_24])).

tff(c_369,plain,(
    ! [A_71,B_72,B_73] :
      ( r1_tarski('#skF_1'(A_71,B_72),B_73)
      | ~ r1_tarski(A_71,k1_zfmisc_1(B_73))
      | r1_tarski(A_71,B_72) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_341])).

tff(c_59,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(A_25,k1_zfmisc_1(B_26))
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    ! [D_17] :
      ( r2_hidden(D_17,'#skF_4')
      | ~ r2_hidden(D_17,'#skF_3')
      | ~ m1_subset_1(D_17,k1_zfmisc_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_157,plain,(
    ! [A_44] :
      ( r2_hidden(A_44,'#skF_4')
      | ~ r2_hidden(A_44,'#skF_3')
      | ~ r1_tarski(A_44,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_59,c_36])).

tff(c_294,plain,(
    ! [B_62] :
      ( r2_hidden('#skF_1'('#skF_3',B_62),'#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3',B_62),'#skF_2')
      | r1_tarski('#skF_3',B_62) ) ),
    inference(resolution,[status(thm)],[c_6,c_157])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_316,plain,
    ( ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_294,c_4])).

tff(c_317,plain,(
    ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_316])).

tff(c_378,plain,
    ( ~ r1_tarski('#skF_3',k1_zfmisc_1('#skF_2'))
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_369,c_317])).

tff(c_394,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_378])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_56,plain,(
    r1_tarski('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_49])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_117,plain,(
    ! [D_37] :
      ( r2_hidden(D_37,'#skF_3')
      | ~ r2_hidden(D_37,'#skF_4')
      | ~ m1_subset_1(D_37,k1_zfmisc_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_144,plain,(
    ! [A_43] :
      ( r2_hidden(A_43,'#skF_3')
      | ~ r2_hidden(A_43,'#skF_4')
      | ~ r1_tarski(A_43,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_117])).

tff(c_277,plain,(
    ! [A_61] :
      ( r1_tarski(A_61,'#skF_3')
      | ~ r2_hidden('#skF_1'(A_61,'#skF_3'),'#skF_4')
      | ~ r1_tarski('#skF_1'(A_61,'#skF_3'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_144,c_4])).

tff(c_292,plain,
    ( ~ r1_tarski('#skF_1'('#skF_4','#skF_3'),'#skF_2')
    | r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_277])).

tff(c_293,plain,(
    ~ r1_tarski('#skF_1'('#skF_4','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_292])).

tff(c_381,plain,
    ( ~ r1_tarski('#skF_4',k1_zfmisc_1('#skF_2'))
    | r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_369,c_293])).

tff(c_397,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_381])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_418,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_397,c_8])).

tff(c_424,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_418])).

tff(c_426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_424])).

tff(c_427,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_452,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_427,c_8])).

tff(c_457,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_452])).

tff(c_475,plain,(
    ! [A_75,B_76,B_77] :
      ( m1_subset_1('#skF_1'(A_75,B_76),B_77)
      | v1_xboole_0(B_77)
      | ~ r1_tarski(A_75,B_77)
      | r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_229,c_14])).

tff(c_491,plain,(
    ! [A_75,B_76,B_12] :
      ( r1_tarski('#skF_1'(A_75,B_76),B_12)
      | v1_xboole_0(k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_75,k1_zfmisc_1(B_12))
      | r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_475,c_24])).

tff(c_513,plain,(
    ! [A_79,B_80,B_81] :
      ( r1_tarski('#skF_1'(A_79,B_80),B_81)
      | ~ r1_tarski(A_79,k1_zfmisc_1(B_81))
      | r1_tarski(A_79,B_80) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_491])).

tff(c_520,plain,
    ( ~ r1_tarski('#skF_4',k1_zfmisc_1('#skF_2'))
    | r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_513,c_293])).

tff(c_532,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_520])).

tff(c_534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_457,c_532])).

tff(c_535,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_292])).

tff(c_563,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_535,c_8])).

tff(c_568,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_563])).

tff(c_577,plain,(
    ! [A_83,B_84,B_85] :
      ( m1_subset_1('#skF_1'(A_83,B_84),B_85)
      | v1_xboole_0(B_85)
      | ~ r1_tarski(A_83,B_85)
      | r1_tarski(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_229,c_14])).

tff(c_593,plain,(
    ! [A_83,B_84,B_12] :
      ( r1_tarski('#skF_1'(A_83,B_84),B_12)
      | v1_xboole_0(k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_83,k1_zfmisc_1(B_12))
      | r1_tarski(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_577,c_24])).

tff(c_621,plain,(
    ! [A_87,B_88,B_89] :
      ( r1_tarski('#skF_1'(A_87,B_88),B_89)
      | ~ r1_tarski(A_87,k1_zfmisc_1(B_89))
      | r1_tarski(A_87,B_88) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_593])).

tff(c_537,plain,(
    ! [B_82] :
      ( r2_hidden('#skF_1'('#skF_3',B_82),'#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3',B_82),'#skF_2')
      | r1_tarski('#skF_3',B_82) ) ),
    inference(resolution,[status(thm)],[c_6,c_157])).

tff(c_559,plain,
    ( ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_537,c_4])).

tff(c_575,plain,(
    ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_568,c_559])).

tff(c_628,plain,
    ( ~ r1_tarski('#skF_3',k1_zfmisc_1('#skF_2'))
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_621,c_575])).

tff(c_640,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_628])).

tff(c_642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_568,c_640])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.43  
% 2.40/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.43  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.40/1.43  
% 2.40/1.43  %Foreground sorts:
% 2.40/1.43  
% 2.40/1.43  
% 2.40/1.43  %Background operators:
% 2.40/1.43  
% 2.40/1.43  
% 2.40/1.43  %Foreground operators:
% 2.40/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.40/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.40/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.40/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.40/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.43  
% 2.40/1.45  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_setfam_1)).
% 2.40/1.45  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.40/1.45  tff(f_54, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.40/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.40/1.45  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.40/1.45  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.40/1.45  tff(c_28, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.40/1.45  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.40/1.45  tff(c_49, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.40/1.45  tff(c_57, plain, (r1_tarski('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_49])).
% 2.40/1.45  tff(c_22, plain, (![A_10]: (~v1_xboole_0(k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.40/1.45  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.40/1.45  tff(c_137, plain, (![C_40, B_41, A_42]: (r2_hidden(C_40, B_41) | ~r2_hidden(C_40, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.40/1.45  tff(c_229, plain, (![A_53, B_54, B_55]: (r2_hidden('#skF_1'(A_53, B_54), B_55) | ~r1_tarski(A_53, B_55) | r1_tarski(A_53, B_54))), inference(resolution, [status(thm)], [c_6, c_137])).
% 2.40/1.45  tff(c_14, plain, (![B_9, A_8]: (m1_subset_1(B_9, A_8) | ~r2_hidden(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.40/1.45  tff(c_325, plain, (![A_64, B_65, B_66]: (m1_subset_1('#skF_1'(A_64, B_65), B_66) | v1_xboole_0(B_66) | ~r1_tarski(A_64, B_66) | r1_tarski(A_64, B_65))), inference(resolution, [status(thm)], [c_229, c_14])).
% 2.40/1.45  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.40/1.45  tff(c_341, plain, (![A_64, B_65, B_12]: (r1_tarski('#skF_1'(A_64, B_65), B_12) | v1_xboole_0(k1_zfmisc_1(B_12)) | ~r1_tarski(A_64, k1_zfmisc_1(B_12)) | r1_tarski(A_64, B_65))), inference(resolution, [status(thm)], [c_325, c_24])).
% 2.40/1.45  tff(c_369, plain, (![A_71, B_72, B_73]: (r1_tarski('#skF_1'(A_71, B_72), B_73) | ~r1_tarski(A_71, k1_zfmisc_1(B_73)) | r1_tarski(A_71, B_72))), inference(negUnitSimplification, [status(thm)], [c_22, c_341])).
% 2.40/1.45  tff(c_59, plain, (![A_25, B_26]: (m1_subset_1(A_25, k1_zfmisc_1(B_26)) | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.40/1.45  tff(c_36, plain, (![D_17]: (r2_hidden(D_17, '#skF_4') | ~r2_hidden(D_17, '#skF_3') | ~m1_subset_1(D_17, k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.40/1.45  tff(c_157, plain, (![A_44]: (r2_hidden(A_44, '#skF_4') | ~r2_hidden(A_44, '#skF_3') | ~r1_tarski(A_44, '#skF_2'))), inference(resolution, [status(thm)], [c_59, c_36])).
% 2.40/1.45  tff(c_294, plain, (![B_62]: (r2_hidden('#skF_1'('#skF_3', B_62), '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', B_62), '#skF_2') | r1_tarski('#skF_3', B_62))), inference(resolution, [status(thm)], [c_6, c_157])).
% 2.40/1.45  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.40/1.45  tff(c_316, plain, (~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_294, c_4])).
% 2.40/1.45  tff(c_317, plain, (~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_316])).
% 2.40/1.45  tff(c_378, plain, (~r1_tarski('#skF_3', k1_zfmisc_1('#skF_2')) | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_369, c_317])).
% 2.40/1.45  tff(c_394, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_378])).
% 2.40/1.45  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.40/1.45  tff(c_56, plain, (r1_tarski('#skF_4', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_49])).
% 2.40/1.45  tff(c_26, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.40/1.45  tff(c_117, plain, (![D_37]: (r2_hidden(D_37, '#skF_3') | ~r2_hidden(D_37, '#skF_4') | ~m1_subset_1(D_37, k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.40/1.45  tff(c_144, plain, (![A_43]: (r2_hidden(A_43, '#skF_3') | ~r2_hidden(A_43, '#skF_4') | ~r1_tarski(A_43, '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_117])).
% 2.40/1.45  tff(c_277, plain, (![A_61]: (r1_tarski(A_61, '#skF_3') | ~r2_hidden('#skF_1'(A_61, '#skF_3'), '#skF_4') | ~r1_tarski('#skF_1'(A_61, '#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_144, c_4])).
% 2.40/1.45  tff(c_292, plain, (~r1_tarski('#skF_1'('#skF_4', '#skF_3'), '#skF_2') | r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_277])).
% 2.40/1.45  tff(c_293, plain, (~r1_tarski('#skF_1'('#skF_4', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_292])).
% 2.40/1.45  tff(c_381, plain, (~r1_tarski('#skF_4', k1_zfmisc_1('#skF_2')) | r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_369, c_293])).
% 2.40/1.45  tff(c_397, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_381])).
% 2.40/1.45  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.40/1.45  tff(c_418, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_397, c_8])).
% 2.40/1.45  tff(c_424, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_394, c_418])).
% 2.40/1.45  tff(c_426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_424])).
% 2.40/1.45  tff(c_427, plain, (r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_316])).
% 2.40/1.45  tff(c_452, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_427, c_8])).
% 2.40/1.45  tff(c_457, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_452])).
% 2.40/1.45  tff(c_475, plain, (![A_75, B_76, B_77]: (m1_subset_1('#skF_1'(A_75, B_76), B_77) | v1_xboole_0(B_77) | ~r1_tarski(A_75, B_77) | r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_229, c_14])).
% 2.40/1.45  tff(c_491, plain, (![A_75, B_76, B_12]: (r1_tarski('#skF_1'(A_75, B_76), B_12) | v1_xboole_0(k1_zfmisc_1(B_12)) | ~r1_tarski(A_75, k1_zfmisc_1(B_12)) | r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_475, c_24])).
% 2.40/1.45  tff(c_513, plain, (![A_79, B_80, B_81]: (r1_tarski('#skF_1'(A_79, B_80), B_81) | ~r1_tarski(A_79, k1_zfmisc_1(B_81)) | r1_tarski(A_79, B_80))), inference(negUnitSimplification, [status(thm)], [c_22, c_491])).
% 2.40/1.45  tff(c_520, plain, (~r1_tarski('#skF_4', k1_zfmisc_1('#skF_2')) | r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_513, c_293])).
% 2.40/1.45  tff(c_532, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_520])).
% 2.40/1.45  tff(c_534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_457, c_532])).
% 2.40/1.45  tff(c_535, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_292])).
% 2.40/1.45  tff(c_563, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_535, c_8])).
% 2.40/1.45  tff(c_568, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_28, c_563])).
% 2.40/1.45  tff(c_577, plain, (![A_83, B_84, B_85]: (m1_subset_1('#skF_1'(A_83, B_84), B_85) | v1_xboole_0(B_85) | ~r1_tarski(A_83, B_85) | r1_tarski(A_83, B_84))), inference(resolution, [status(thm)], [c_229, c_14])).
% 2.40/1.45  tff(c_593, plain, (![A_83, B_84, B_12]: (r1_tarski('#skF_1'(A_83, B_84), B_12) | v1_xboole_0(k1_zfmisc_1(B_12)) | ~r1_tarski(A_83, k1_zfmisc_1(B_12)) | r1_tarski(A_83, B_84))), inference(resolution, [status(thm)], [c_577, c_24])).
% 2.40/1.45  tff(c_621, plain, (![A_87, B_88, B_89]: (r1_tarski('#skF_1'(A_87, B_88), B_89) | ~r1_tarski(A_87, k1_zfmisc_1(B_89)) | r1_tarski(A_87, B_88))), inference(negUnitSimplification, [status(thm)], [c_22, c_593])).
% 2.40/1.45  tff(c_537, plain, (![B_82]: (r2_hidden('#skF_1'('#skF_3', B_82), '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', B_82), '#skF_2') | r1_tarski('#skF_3', B_82))), inference(resolution, [status(thm)], [c_6, c_157])).
% 2.40/1.45  tff(c_559, plain, (~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_537, c_4])).
% 2.40/1.45  tff(c_575, plain, (~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_568, c_559])).
% 2.40/1.45  tff(c_628, plain, (~r1_tarski('#skF_3', k1_zfmisc_1('#skF_2')) | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_621, c_575])).
% 2.40/1.45  tff(c_640, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_628])).
% 2.40/1.45  tff(c_642, plain, $false, inference(negUnitSimplification, [status(thm)], [c_568, c_640])).
% 2.40/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.45  
% 2.40/1.45  Inference rules
% 2.40/1.45  ----------------------
% 2.40/1.45  #Ref     : 0
% 2.40/1.45  #Sup     : 120
% 2.40/1.45  #Fact    : 0
% 2.40/1.45  #Define  : 0
% 2.40/1.45  #Split   : 8
% 2.40/1.45  #Chain   : 0
% 2.40/1.45  #Close   : 0
% 2.40/1.45  
% 2.40/1.45  Ordering : KBO
% 2.40/1.45  
% 2.40/1.45  Simplification rules
% 2.40/1.45  ----------------------
% 2.40/1.45  #Subsume      : 14
% 2.40/1.45  #Demod        : 26
% 2.40/1.45  #Tautology    : 35
% 2.40/1.45  #SimpNegUnit  : 25
% 2.40/1.45  #BackRed      : 0
% 2.40/1.45  
% 2.40/1.45  #Partial instantiations: 0
% 2.40/1.45  #Strategies tried      : 1
% 2.40/1.45  
% 2.40/1.45  Timing (in seconds)
% 2.40/1.45  ----------------------
% 2.40/1.45  Preprocessing        : 0.29
% 2.40/1.45  Parsing              : 0.16
% 2.40/1.45  CNF conversion       : 0.02
% 2.40/1.45  Main loop            : 0.31
% 2.40/1.45  Inferencing          : 0.12
% 2.40/1.45  Reduction            : 0.09
% 2.40/1.45  Demodulation         : 0.06
% 2.40/1.45  BG Simplification    : 0.01
% 2.40/1.45  Subsumption          : 0.08
% 2.40/1.45  Abstraction          : 0.01
% 2.40/1.45  MUC search           : 0.00
% 2.40/1.45  Cooper               : 0.00
% 2.40/1.45  Total                : 0.65
% 2.40/1.45  Index Insertion      : 0.00
% 2.40/1.45  Index Deletion       : 0.00
% 2.40/1.45  Index Matching       : 0.00
% 2.40/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
