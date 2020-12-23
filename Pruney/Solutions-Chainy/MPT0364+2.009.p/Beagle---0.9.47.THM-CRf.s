%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:40 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 177 expanded)
%              Number of leaves         :   18 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  142 ( 432 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_36,plain,(
    ~ r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_32,plain,
    ( r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3'))
    | r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_37,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_32])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k3_subset_1(A_8,B_9),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_55,plain,(
    ! [B_32,C_33,A_34] :
      ( r1_xboole_0(B_32,C_33)
      | ~ r1_tarski(B_32,k3_subset_1(A_34,C_33))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(A_34))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_65,plain,(
    ! [A_35,C_36] :
      ( r1_xboole_0(k3_subset_1(A_35,C_36),C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(A_35))
      | ~ m1_subset_1(k3_subset_1(A_35,C_36),k1_zfmisc_1(A_35)) ) ),
    inference(resolution,[status(thm)],[c_8,c_55])).

tff(c_81,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(k3_subset_1(A_40,B_41),B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(resolution,[status(thm)],[c_12,c_65])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_88,plain,(
    ! [B_42,A_43] :
      ( r1_xboole_0(B_42,k3_subset_1(A_43,B_42))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43)) ) ),
    inference(resolution,[status(thm)],[c_81,c_2])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_xboole_0(A_5,C_7)
      | ~ r1_xboole_0(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_117,plain,(
    ! [A_50,A_51,B_52] :
      ( r1_xboole_0(A_50,k3_subset_1(A_51,B_52))
      | ~ r1_tarski(A_50,B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(resolution,[status(thm)],[c_88,c_10])).

tff(c_122,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_117,c_36])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_37,c_122])).

tff(c_130,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_131,plain,(
    r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_20,plain,(
    ! [B_15,A_14,C_17] :
      ( r1_tarski(B_15,k3_subset_1(A_14,C_17))
      | ~ r1_xboole_0(B_15,C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_220,plain,(
    ! [B_71,C_72,A_73] :
      ( r1_xboole_0(B_71,C_72)
      | ~ r1_tarski(B_71,k3_subset_1(A_73,C_72))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(A_73))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_258,plain,(
    ! [A_78,C_79] :
      ( r1_xboole_0(k3_subset_1(A_78,C_79),C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(A_78))
      | ~ m1_subset_1(k3_subset_1(A_78,C_79),k1_zfmisc_1(A_78)) ) ),
    inference(resolution,[status(thm)],[c_8,c_220])).

tff(c_262,plain,(
    ! [A_80,B_81] :
      ( r1_xboole_0(k3_subset_1(A_80,B_81),B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(resolution,[status(thm)],[c_12,c_258])).

tff(c_288,plain,(
    ! [B_85,A_86] :
      ( r1_xboole_0(B_85,k3_subset_1(A_86,B_85))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_86)) ) ),
    inference(resolution,[status(thm)],[c_262,c_2])).

tff(c_305,plain,(
    ! [A_90,A_91,B_92] :
      ( r1_xboole_0(A_90,k3_subset_1(A_91,B_92))
      | ~ r1_tarski(A_90,B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(resolution,[status(thm)],[c_288,c_10])).

tff(c_313,plain,(
    ! [A_96,B_97,A_98] :
      ( r1_xboole_0(k3_subset_1(A_96,B_97),A_98)
      | ~ r1_tarski(A_98,B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(resolution,[status(thm)],[c_305,c_2])).

tff(c_186,plain,(
    ! [B_67,A_68,C_69] :
      ( r1_tarski(B_67,k3_subset_1(A_68,C_69))
      | ~ r1_xboole_0(B_67,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(A_68))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_134,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_131,c_2])).

tff(c_148,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_xboole_0(A_55,C_56)
      | ~ r1_xboole_0(B_57,C_56)
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_153,plain,(
    ! [A_55] :
      ( r1_xboole_0(A_55,'#skF_2')
      | ~ r1_tarski(A_55,k3_subset_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_134,c_148])).

tff(c_195,plain,(
    ! [B_67] :
      ( r1_xboole_0(B_67,'#skF_2')
      | ~ r1_xboole_0(B_67,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_67,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_186,c_153])).

tff(c_206,plain,(
    ! [B_70] :
      ( r1_xboole_0(B_70,'#skF_2')
      | ~ r1_xboole_0(B_70,'#skF_3')
      | ~ m1_subset_1(B_70,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_195])).

tff(c_243,plain,(
    ! [B_76] :
      ( r1_xboole_0(k3_subset_1('#skF_1',B_76),'#skF_2')
      | ~ r1_xboole_0(k3_subset_1('#skF_1',B_76),'#skF_3')
      | ~ m1_subset_1(B_76,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_12,c_206])).

tff(c_249,plain,(
    ! [B_76] :
      ( r1_xboole_0('#skF_2',k3_subset_1('#skF_1',B_76))
      | ~ r1_xboole_0(k3_subset_1('#skF_1',B_76),'#skF_3')
      | ~ m1_subset_1(B_76,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_243,c_2])).

tff(c_325,plain,(
    ! [B_99] :
      ( r1_xboole_0('#skF_2',k3_subset_1('#skF_1',B_99))
      | ~ r1_tarski('#skF_3',B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_313,c_249])).

tff(c_332,plain,(
    ! [B_100] :
      ( r1_xboole_0(k3_subset_1('#skF_1',B_100),'#skF_2')
      | ~ r1_tarski('#skF_3',B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_325,c_2])).

tff(c_408,plain,(
    ! [A_119,B_120] :
      ( r1_xboole_0(A_119,'#skF_2')
      | ~ r1_tarski(A_119,k3_subset_1('#skF_1',B_120))
      | ~ r1_tarski('#skF_3',B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_332,c_10])).

tff(c_468,plain,(
    ! [B_129,C_130] :
      ( r1_xboole_0(B_129,'#skF_2')
      | ~ r1_tarski('#skF_3',C_130)
      | ~ r1_xboole_0(B_129,C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_129,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_20,c_408])).

tff(c_494,plain,
    ( r1_xboole_0('#skF_2','#skF_2')
    | ~ r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_3'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_131,c_468])).

tff(c_518,plain,
    ( r1_xboole_0('#skF_2','#skF_2')
    | ~ r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_3'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_494])).

tff(c_535,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_518])).

tff(c_538,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_535])).

tff(c_542,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_538])).

tff(c_544,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_518])).

tff(c_276,plain,(
    ! [B_82,C_83,A_84] :
      ( r1_tarski(B_82,C_83)
      | ~ r1_tarski(k3_subset_1(A_84,C_83),k3_subset_1(A_84,B_82))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(A_84))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_606,plain,(
    ! [C_142,C_143,A_144] :
      ( r1_tarski(C_142,C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(A_144))
      | ~ r1_xboole_0(k3_subset_1(A_144,C_143),C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(A_144))
      | ~ m1_subset_1(k3_subset_1(A_144,C_143),k1_zfmisc_1(A_144)) ) ),
    inference(resolution,[status(thm)],[c_20,c_276])).

tff(c_632,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_134,c_606])).

tff(c_652,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_24,c_22,c_632])).

tff(c_654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_652])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:12:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.40  
% 2.94/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.40  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.94/1.40  
% 2.94/1.40  %Foreground sorts:
% 2.94/1.40  
% 2.94/1.40  
% 2.94/1.40  %Background operators:
% 2.94/1.40  
% 2.94/1.40  
% 2.94/1.40  %Foreground operators:
% 2.94/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.40  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.94/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.94/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.94/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.40  
% 2.94/1.42  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 2.94/1.42  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.94/1.42  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.94/1.42  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 2.94/1.42  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.94/1.42  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.94/1.42  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 2.94/1.42  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.94/1.42  tff(c_26, plain, (~r1_tarski('#skF_2', '#skF_3') | ~r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.94/1.42  tff(c_36, plain, (~r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_26])).
% 2.94/1.42  tff(c_32, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3')) | r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.94/1.42  tff(c_37, plain, (r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_36, c_32])).
% 2.94/1.42  tff(c_12, plain, (![A_8, B_9]: (m1_subset_1(k3_subset_1(A_8, B_9), k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.94/1.42  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.94/1.42  tff(c_55, plain, (![B_32, C_33, A_34]: (r1_xboole_0(B_32, C_33) | ~r1_tarski(B_32, k3_subset_1(A_34, C_33)) | ~m1_subset_1(C_33, k1_zfmisc_1(A_34)) | ~m1_subset_1(B_32, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.94/1.42  tff(c_65, plain, (![A_35, C_36]: (r1_xboole_0(k3_subset_1(A_35, C_36), C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(A_35)) | ~m1_subset_1(k3_subset_1(A_35, C_36), k1_zfmisc_1(A_35)))), inference(resolution, [status(thm)], [c_8, c_55])).
% 2.94/1.42  tff(c_81, plain, (![A_40, B_41]: (r1_xboole_0(k3_subset_1(A_40, B_41), B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(resolution, [status(thm)], [c_12, c_65])).
% 2.94/1.42  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.94/1.42  tff(c_88, plain, (![B_42, A_43]: (r1_xboole_0(B_42, k3_subset_1(A_43, B_42)) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)))), inference(resolution, [status(thm)], [c_81, c_2])).
% 2.94/1.42  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, C_7) | ~r1_xboole_0(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.94/1.42  tff(c_117, plain, (![A_50, A_51, B_52]: (r1_xboole_0(A_50, k3_subset_1(A_51, B_52)) | ~r1_tarski(A_50, B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(resolution, [status(thm)], [c_88, c_10])).
% 2.94/1.42  tff(c_122, plain, (~r1_tarski('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_117, c_36])).
% 2.94/1.42  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_37, c_122])).
% 2.94/1.42  tff(c_130, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 2.94/1.42  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.94/1.42  tff(c_131, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_26])).
% 2.94/1.42  tff(c_20, plain, (![B_15, A_14, C_17]: (r1_tarski(B_15, k3_subset_1(A_14, C_17)) | ~r1_xboole_0(B_15, C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.94/1.42  tff(c_220, plain, (![B_71, C_72, A_73]: (r1_xboole_0(B_71, C_72) | ~r1_tarski(B_71, k3_subset_1(A_73, C_72)) | ~m1_subset_1(C_72, k1_zfmisc_1(A_73)) | ~m1_subset_1(B_71, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.94/1.42  tff(c_258, plain, (![A_78, C_79]: (r1_xboole_0(k3_subset_1(A_78, C_79), C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(A_78)) | ~m1_subset_1(k3_subset_1(A_78, C_79), k1_zfmisc_1(A_78)))), inference(resolution, [status(thm)], [c_8, c_220])).
% 2.94/1.42  tff(c_262, plain, (![A_80, B_81]: (r1_xboole_0(k3_subset_1(A_80, B_81), B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(resolution, [status(thm)], [c_12, c_258])).
% 2.94/1.42  tff(c_288, plain, (![B_85, A_86]: (r1_xboole_0(B_85, k3_subset_1(A_86, B_85)) | ~m1_subset_1(B_85, k1_zfmisc_1(A_86)))), inference(resolution, [status(thm)], [c_262, c_2])).
% 2.94/1.42  tff(c_305, plain, (![A_90, A_91, B_92]: (r1_xboole_0(A_90, k3_subset_1(A_91, B_92)) | ~r1_tarski(A_90, B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(resolution, [status(thm)], [c_288, c_10])).
% 2.94/1.42  tff(c_313, plain, (![A_96, B_97, A_98]: (r1_xboole_0(k3_subset_1(A_96, B_97), A_98) | ~r1_tarski(A_98, B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(resolution, [status(thm)], [c_305, c_2])).
% 2.94/1.42  tff(c_186, plain, (![B_67, A_68, C_69]: (r1_tarski(B_67, k3_subset_1(A_68, C_69)) | ~r1_xboole_0(B_67, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(A_68)) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.94/1.42  tff(c_134, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_131, c_2])).
% 2.94/1.42  tff(c_148, plain, (![A_55, C_56, B_57]: (r1_xboole_0(A_55, C_56) | ~r1_xboole_0(B_57, C_56) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.94/1.42  tff(c_153, plain, (![A_55]: (r1_xboole_0(A_55, '#skF_2') | ~r1_tarski(A_55, k3_subset_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_134, c_148])).
% 2.94/1.42  tff(c_195, plain, (![B_67]: (r1_xboole_0(B_67, '#skF_2') | ~r1_xboole_0(B_67, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_67, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_186, c_153])).
% 2.94/1.42  tff(c_206, plain, (![B_70]: (r1_xboole_0(B_70, '#skF_2') | ~r1_xboole_0(B_70, '#skF_3') | ~m1_subset_1(B_70, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_195])).
% 2.94/1.42  tff(c_243, plain, (![B_76]: (r1_xboole_0(k3_subset_1('#skF_1', B_76), '#skF_2') | ~r1_xboole_0(k3_subset_1('#skF_1', B_76), '#skF_3') | ~m1_subset_1(B_76, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_206])).
% 2.94/1.42  tff(c_249, plain, (![B_76]: (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', B_76)) | ~r1_xboole_0(k3_subset_1('#skF_1', B_76), '#skF_3') | ~m1_subset_1(B_76, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_243, c_2])).
% 2.94/1.42  tff(c_325, plain, (![B_99]: (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', B_99)) | ~r1_tarski('#skF_3', B_99) | ~m1_subset_1(B_99, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_313, c_249])).
% 2.94/1.42  tff(c_332, plain, (![B_100]: (r1_xboole_0(k3_subset_1('#skF_1', B_100), '#skF_2') | ~r1_tarski('#skF_3', B_100) | ~m1_subset_1(B_100, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_325, c_2])).
% 2.94/1.42  tff(c_408, plain, (![A_119, B_120]: (r1_xboole_0(A_119, '#skF_2') | ~r1_tarski(A_119, k3_subset_1('#skF_1', B_120)) | ~r1_tarski('#skF_3', B_120) | ~m1_subset_1(B_120, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_332, c_10])).
% 2.94/1.42  tff(c_468, plain, (![B_129, C_130]: (r1_xboole_0(B_129, '#skF_2') | ~r1_tarski('#skF_3', C_130) | ~r1_xboole_0(B_129, C_130) | ~m1_subset_1(C_130, k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_129, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_408])).
% 2.94/1.42  tff(c_494, plain, (r1_xboole_0('#skF_2', '#skF_2') | ~r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_3')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_131, c_468])).
% 2.94/1.42  tff(c_518, plain, (r1_xboole_0('#skF_2', '#skF_2') | ~r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_3')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_494])).
% 2.94/1.42  tff(c_535, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_518])).
% 2.94/1.42  tff(c_538, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_535])).
% 2.94/1.42  tff(c_542, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_538])).
% 2.94/1.42  tff(c_544, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_518])).
% 2.94/1.42  tff(c_276, plain, (![B_82, C_83, A_84]: (r1_tarski(B_82, C_83) | ~r1_tarski(k3_subset_1(A_84, C_83), k3_subset_1(A_84, B_82)) | ~m1_subset_1(C_83, k1_zfmisc_1(A_84)) | ~m1_subset_1(B_82, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.94/1.42  tff(c_606, plain, (![C_142, C_143, A_144]: (r1_tarski(C_142, C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(A_144)) | ~r1_xboole_0(k3_subset_1(A_144, C_143), C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(A_144)) | ~m1_subset_1(k3_subset_1(A_144, C_143), k1_zfmisc_1(A_144)))), inference(resolution, [status(thm)], [c_20, c_276])).
% 2.94/1.42  tff(c_632, plain, (r1_tarski('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_134, c_606])).
% 2.94/1.42  tff(c_652, plain, (r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_544, c_24, c_22, c_632])).
% 2.94/1.42  tff(c_654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_652])).
% 2.94/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.42  
% 2.94/1.42  Inference rules
% 2.94/1.42  ----------------------
% 2.94/1.42  #Ref     : 0
% 2.94/1.42  #Sup     : 137
% 2.94/1.42  #Fact    : 0
% 2.94/1.42  #Define  : 0
% 2.94/1.42  #Split   : 6
% 2.94/1.42  #Chain   : 0
% 2.94/1.42  #Close   : 0
% 2.94/1.42  
% 2.94/1.42  Ordering : KBO
% 2.94/1.42  
% 2.94/1.42  Simplification rules
% 2.94/1.42  ----------------------
% 2.94/1.42  #Subsume      : 40
% 2.94/1.42  #Demod        : 41
% 2.94/1.42  #Tautology    : 25
% 2.94/1.42  #SimpNegUnit  : 3
% 2.94/1.42  #BackRed      : 0
% 2.94/1.42  
% 2.94/1.42  #Partial instantiations: 0
% 2.94/1.42  #Strategies tried      : 1
% 2.94/1.42  
% 2.94/1.42  Timing (in seconds)
% 2.94/1.42  ----------------------
% 2.94/1.42  Preprocessing        : 0.28
% 2.94/1.42  Parsing              : 0.16
% 2.94/1.42  CNF conversion       : 0.02
% 2.94/1.42  Main loop            : 0.38
% 2.94/1.42  Inferencing          : 0.14
% 2.94/1.42  Reduction            : 0.09
% 2.94/1.42  Demodulation         : 0.06
% 2.94/1.42  BG Simplification    : 0.02
% 2.94/1.42  Subsumption          : 0.11
% 2.94/1.42  Abstraction          : 0.02
% 2.94/1.42  MUC search           : 0.00
% 2.94/1.42  Cooper               : 0.00
% 2.94/1.42  Total                : 0.69
% 2.94/1.42  Index Insertion      : 0.00
% 2.94/1.42  Index Deletion       : 0.00
% 2.94/1.42  Index Matching       : 0.00
% 2.94/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
