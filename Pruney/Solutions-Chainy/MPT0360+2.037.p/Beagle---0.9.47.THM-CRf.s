%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:23 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 113 expanded)
%              Number of leaves         :   25 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 246 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_54,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_93,plain,(
    ! [A_37,B_38] :
      ( ~ r2_hidden('#skF_1'(A_37,B_38),B_38)
      | r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_102,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_93])).

tff(c_30,plain,(
    ! [A_14] : ~ v1_xboole_0(k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [C_10,A_6] :
      ( r2_hidden(C_10,k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_71,plain,(
    ! [B_31,A_32] :
      ( m1_subset_1(B_31,A_32)
      | ~ r2_hidden(B_31,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_74,plain,(
    ! [C_10,A_6] :
      ( m1_subset_1(C_10,k1_zfmisc_1(A_6))
      | v1_xboole_0(k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_71])).

tff(c_77,plain,(
    ! [C_10,A_6] :
      ( m1_subset_1(C_10,k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_74])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_289,plain,(
    ! [C_78,A_79,B_80] :
      ( r1_tarski(C_78,k3_subset_1(A_79,B_80))
      | ~ r1_tarski(B_80,k3_subset_1(A_79,C_78))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(A_79))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_305,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_289])).

tff(c_313,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_305])).

tff(c_314,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_321,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_77,c_314])).

tff(c_42,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_105,plain,(
    ! [B_40,A_41] :
      ( r2_hidden(B_40,A_41)
      | ~ m1_subset_1(B_40,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( r1_tarski(C_10,A_6)
      | ~ r2_hidden(C_10,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_116,plain,(
    ! [B_40,A_6] :
      ( r1_tarski(B_40,A_6)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_6))
      | v1_xboole_0(k1_zfmisc_1(A_6)) ) ),
    inference(resolution,[status(thm)],[c_105,c_8])).

tff(c_122,plain,(
    ! [B_42,A_43] :
      ( r1_tarski(B_42,A_43)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_116])).

tff(c_135,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_122])).

tff(c_136,plain,(
    ! [C_44,B_45,A_46] :
      ( r2_hidden(C_44,B_45)
      | ~ r2_hidden(C_44,A_46)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_209,plain,(
    ! [A_63,B_64,B_65] :
      ( r2_hidden('#skF_1'(A_63,B_64),B_65)
      | ~ r1_tarski(A_63,B_65)
      | r1_tarski(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_6,c_136])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_355,plain,(
    ! [A_86,B_87,B_88,B_89] :
      ( r2_hidden('#skF_1'(A_86,B_87),B_88)
      | ~ r1_tarski(B_89,B_88)
      | ~ r1_tarski(A_86,B_89)
      | r1_tarski(A_86,B_87) ) ),
    inference(resolution,[status(thm)],[c_209,c_2])).

tff(c_380,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_1'(A_90,B_91),'#skF_4')
      | ~ r1_tarski(A_90,'#skF_6')
      | r1_tarski(A_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_135,c_355])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_407,plain,(
    ! [A_94] :
      ( ~ r1_tarski(A_94,'#skF_6')
      | r1_tarski(A_94,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_380,c_4])).

tff(c_424,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_407])).

tff(c_432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_321,c_424])).

tff(c_434,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_433,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_487,plain,(
    ! [A_100,B_101,B_102,B_103] :
      ( r2_hidden('#skF_1'(A_100,B_101),B_102)
      | ~ r1_tarski(B_103,B_102)
      | ~ r1_tarski(A_100,B_103)
      | r1_tarski(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_209,c_2])).

tff(c_518,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_1'(A_104,B_105),'#skF_6')
      | ~ r1_tarski(A_104,'#skF_5')
      | r1_tarski(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_42,c_487])).

tff(c_853,plain,(
    ! [A_126,B_127,B_128] :
      ( r2_hidden('#skF_1'(A_126,B_127),B_128)
      | ~ r1_tarski('#skF_6',B_128)
      | ~ r1_tarski(A_126,'#skF_5')
      | r1_tarski(A_126,B_127) ) ),
    inference(resolution,[status(thm)],[c_518,c_2])).

tff(c_904,plain,(
    ! [B_130,A_131] :
      ( ~ r1_tarski('#skF_6',B_130)
      | ~ r1_tarski(A_131,'#skF_5')
      | r1_tarski(A_131,B_130) ) ),
    inference(resolution,[status(thm)],[c_853,c_4])).

tff(c_943,plain,(
    ! [A_133] :
      ( ~ r1_tarski(A_133,'#skF_5')
      | r1_tarski(A_133,k3_subset_1('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_433,c_904])).

tff(c_28,plain,(
    ! [A_13] : k1_subset_1(A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    ! [A_19,B_20] :
      ( k1_subset_1(A_19) = B_20
      | ~ r1_tarski(B_20,k3_subset_1(A_19,B_20))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_45,plain,(
    ! [B_20,A_19] :
      ( k1_xboole_0 = B_20
      | ~ r1_tarski(B_20,k3_subset_1(A_19,B_20))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_36])).

tff(c_966,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_943,c_45])).

tff(c_985,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_434,c_966])).

tff(c_987,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_985])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:27:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.48  
% 3.09/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.49  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 3.09/1.49  
% 3.09/1.49  %Foreground sorts:
% 3.09/1.49  
% 3.09/1.49  
% 3.09/1.49  %Background operators:
% 3.09/1.49  
% 3.09/1.49  
% 3.09/1.49  %Foreground operators:
% 3.09/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.09/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.09/1.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.09/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.49  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.09/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.09/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.09/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.09/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.09/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.09/1.49  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.09/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.09/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.09/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.09/1.49  
% 3.24/1.50  tff(f_81, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 3.24/1.50  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.24/1.50  tff(f_57, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.24/1.50  tff(f_39, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.24/1.50  tff(f_52, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.24/1.50  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 3.24/1.50  tff(f_54, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.24/1.50  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 3.24/1.50  tff(c_38, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.24/1.50  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.24/1.50  tff(c_93, plain, (![A_37, B_38]: (~r2_hidden('#skF_1'(A_37, B_38), B_38) | r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.24/1.50  tff(c_102, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_93])).
% 3.24/1.50  tff(c_30, plain, (![A_14]: (~v1_xboole_0(k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.24/1.50  tff(c_10, plain, (![C_10, A_6]: (r2_hidden(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.24/1.50  tff(c_71, plain, (![B_31, A_32]: (m1_subset_1(B_31, A_32) | ~r2_hidden(B_31, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.24/1.50  tff(c_74, plain, (![C_10, A_6]: (m1_subset_1(C_10, k1_zfmisc_1(A_6)) | v1_xboole_0(k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(resolution, [status(thm)], [c_10, c_71])).
% 3.24/1.50  tff(c_77, plain, (![C_10, A_6]: (m1_subset_1(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(negUnitSimplification, [status(thm)], [c_30, c_74])).
% 3.24/1.50  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.24/1.50  tff(c_40, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.24/1.50  tff(c_289, plain, (![C_78, A_79, B_80]: (r1_tarski(C_78, k3_subset_1(A_79, B_80)) | ~r1_tarski(B_80, k3_subset_1(A_79, C_78)) | ~m1_subset_1(C_78, k1_zfmisc_1(A_79)) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.24/1.50  tff(c_305, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_289])).
% 3.24/1.50  tff(c_313, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_305])).
% 3.24/1.50  tff(c_314, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_313])).
% 3.24/1.50  tff(c_321, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_77, c_314])).
% 3.24/1.50  tff(c_42, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.24/1.50  tff(c_105, plain, (![B_40, A_41]: (r2_hidden(B_40, A_41) | ~m1_subset_1(B_40, A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.24/1.50  tff(c_8, plain, (![C_10, A_6]: (r1_tarski(C_10, A_6) | ~r2_hidden(C_10, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.24/1.50  tff(c_116, plain, (![B_40, A_6]: (r1_tarski(B_40, A_6) | ~m1_subset_1(B_40, k1_zfmisc_1(A_6)) | v1_xboole_0(k1_zfmisc_1(A_6)))), inference(resolution, [status(thm)], [c_105, c_8])).
% 3.24/1.50  tff(c_122, plain, (![B_42, A_43]: (r1_tarski(B_42, A_43) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)))), inference(negUnitSimplification, [status(thm)], [c_30, c_116])).
% 3.24/1.50  tff(c_135, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_122])).
% 3.24/1.50  tff(c_136, plain, (![C_44, B_45, A_46]: (r2_hidden(C_44, B_45) | ~r2_hidden(C_44, A_46) | ~r1_tarski(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.24/1.50  tff(c_209, plain, (![A_63, B_64, B_65]: (r2_hidden('#skF_1'(A_63, B_64), B_65) | ~r1_tarski(A_63, B_65) | r1_tarski(A_63, B_64))), inference(resolution, [status(thm)], [c_6, c_136])).
% 3.24/1.50  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.24/1.50  tff(c_355, plain, (![A_86, B_87, B_88, B_89]: (r2_hidden('#skF_1'(A_86, B_87), B_88) | ~r1_tarski(B_89, B_88) | ~r1_tarski(A_86, B_89) | r1_tarski(A_86, B_87))), inference(resolution, [status(thm)], [c_209, c_2])).
% 3.24/1.50  tff(c_380, plain, (![A_90, B_91]: (r2_hidden('#skF_1'(A_90, B_91), '#skF_4') | ~r1_tarski(A_90, '#skF_6') | r1_tarski(A_90, B_91))), inference(resolution, [status(thm)], [c_135, c_355])).
% 3.24/1.50  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.24/1.50  tff(c_407, plain, (![A_94]: (~r1_tarski(A_94, '#skF_6') | r1_tarski(A_94, '#skF_4'))), inference(resolution, [status(thm)], [c_380, c_4])).
% 3.24/1.50  tff(c_424, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_407])).
% 3.24/1.50  tff(c_432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_321, c_424])).
% 3.24/1.50  tff(c_434, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_313])).
% 3.24/1.50  tff(c_433, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_313])).
% 3.24/1.50  tff(c_487, plain, (![A_100, B_101, B_102, B_103]: (r2_hidden('#skF_1'(A_100, B_101), B_102) | ~r1_tarski(B_103, B_102) | ~r1_tarski(A_100, B_103) | r1_tarski(A_100, B_101))), inference(resolution, [status(thm)], [c_209, c_2])).
% 3.24/1.50  tff(c_518, plain, (![A_104, B_105]: (r2_hidden('#skF_1'(A_104, B_105), '#skF_6') | ~r1_tarski(A_104, '#skF_5') | r1_tarski(A_104, B_105))), inference(resolution, [status(thm)], [c_42, c_487])).
% 3.24/1.50  tff(c_853, plain, (![A_126, B_127, B_128]: (r2_hidden('#skF_1'(A_126, B_127), B_128) | ~r1_tarski('#skF_6', B_128) | ~r1_tarski(A_126, '#skF_5') | r1_tarski(A_126, B_127))), inference(resolution, [status(thm)], [c_518, c_2])).
% 3.24/1.50  tff(c_904, plain, (![B_130, A_131]: (~r1_tarski('#skF_6', B_130) | ~r1_tarski(A_131, '#skF_5') | r1_tarski(A_131, B_130))), inference(resolution, [status(thm)], [c_853, c_4])).
% 3.24/1.50  tff(c_943, plain, (![A_133]: (~r1_tarski(A_133, '#skF_5') | r1_tarski(A_133, k3_subset_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_433, c_904])).
% 3.24/1.50  tff(c_28, plain, (![A_13]: (k1_subset_1(A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.24/1.50  tff(c_36, plain, (![A_19, B_20]: (k1_subset_1(A_19)=B_20 | ~r1_tarski(B_20, k3_subset_1(A_19, B_20)) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.24/1.50  tff(c_45, plain, (![B_20, A_19]: (k1_xboole_0=B_20 | ~r1_tarski(B_20, k3_subset_1(A_19, B_20)) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_36])).
% 3.24/1.50  tff(c_966, plain, (k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4')) | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_943, c_45])).
% 3.24/1.50  tff(c_985, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_434, c_966])).
% 3.24/1.50  tff(c_987, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_985])).
% 3.24/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.50  
% 3.24/1.50  Inference rules
% 3.24/1.50  ----------------------
% 3.24/1.50  #Ref     : 0
% 3.24/1.50  #Sup     : 195
% 3.24/1.50  #Fact    : 0
% 3.24/1.50  #Define  : 0
% 3.24/1.50  #Split   : 6
% 3.24/1.50  #Chain   : 0
% 3.24/1.50  #Close   : 0
% 3.24/1.50  
% 3.24/1.50  Ordering : KBO
% 3.24/1.50  
% 3.24/1.50  Simplification rules
% 3.24/1.50  ----------------------
% 3.24/1.50  #Subsume      : 27
% 3.24/1.50  #Demod        : 29
% 3.24/1.50  #Tautology    : 31
% 3.24/1.50  #SimpNegUnit  : 23
% 3.24/1.50  #BackRed      : 0
% 3.24/1.50  
% 3.24/1.50  #Partial instantiations: 0
% 3.24/1.50  #Strategies tried      : 1
% 3.24/1.50  
% 3.24/1.50  Timing (in seconds)
% 3.24/1.50  ----------------------
% 3.24/1.50  Preprocessing        : 0.31
% 3.24/1.50  Parsing              : 0.16
% 3.24/1.50  CNF conversion       : 0.02
% 3.24/1.50  Main loop            : 0.44
% 3.24/1.50  Inferencing          : 0.16
% 3.24/1.50  Reduction            : 0.12
% 3.24/1.50  Demodulation         : 0.08
% 3.24/1.50  BG Simplification    : 0.03
% 3.24/1.50  Subsumption          : 0.10
% 3.24/1.50  Abstraction          : 0.02
% 3.24/1.50  MUC search           : 0.00
% 3.24/1.50  Cooper               : 0.00
% 3.24/1.50  Total                : 0.78
% 3.24/1.50  Index Insertion      : 0.00
% 3.24/1.51  Index Deletion       : 0.00
% 3.24/1.51  Index Matching       : 0.00
% 3.24/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
