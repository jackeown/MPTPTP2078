%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:50 EST 2020

% Result     : Theorem 7.48s
% Output     : CNFRefutation 7.48s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 127 expanded)
%              Number of leaves         :   22 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  122 ( 279 expanded)
%              Number of equality atoms :    9 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
            <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_56,plain,(
    ~ r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_40,plain,
    ( r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3'))
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_57,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_40])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k7_setfam_1(A_18,B_19),k1_zfmisc_1(k1_zfmisc_1(A_18)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k1_zfmisc_1(A_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_58,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k3_subset_1(A_32,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_58])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_74,plain,(
    r1_tarski(k3_subset_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_2])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_152,plain,(
    ! [A_48,B_49] :
      ( k3_subset_1(A_48,k3_subset_1(A_48,B_49)) = B_49
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_164,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_152])).

tff(c_761,plain,(
    ! [A_85,D_86,B_87] :
      ( r2_hidden(k3_subset_1(A_85,D_86),B_87)
      | ~ r2_hidden(D_86,k7_setfam_1(A_85,B_87))
      | ~ m1_subset_1(D_86,k1_zfmisc_1(A_85))
      | ~ m1_subset_1(k7_setfam_1(A_85,B_87),k1_zfmisc_1(k1_zfmisc_1(A_85)))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k1_zfmisc_1(A_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1320,plain,(
    ! [A_105,D_106,B_107] :
      ( r2_hidden(k3_subset_1(A_105,D_106),B_107)
      | ~ r2_hidden(D_106,k7_setfam_1(A_105,B_107))
      | ~ m1_subset_1(D_106,k1_zfmisc_1(A_105))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k1_zfmisc_1(A_105))) ) ),
    inference(resolution,[status(thm)],[c_22,c_761])).

tff(c_1446,plain,(
    ! [A_116,D_117,A_118] :
      ( r2_hidden(k3_subset_1(A_116,D_117),A_118)
      | ~ r2_hidden(D_117,k7_setfam_1(A_116,A_118))
      | ~ m1_subset_1(D_117,k1_zfmisc_1(A_116))
      | ~ r1_tarski(A_118,k1_zfmisc_1(A_116)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1320])).

tff(c_1502,plain,(
    ! [A_118] :
      ( r2_hidden('#skF_4',A_118)
      | ~ r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2',A_118))
      | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2'))
      | ~ r1_tarski(A_118,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_1446])).

tff(c_1836,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1502])).

tff(c_1842,plain,(
    ~ r1_tarski(k3_subset_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_1836])).

tff(c_1847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1842])).

tff(c_1849,plain,(
    m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1502])).

tff(c_668,plain,(
    ! [D_78,A_79,B_80] :
      ( r2_hidden(D_78,k7_setfam_1(A_79,B_80))
      | ~ r2_hidden(k3_subset_1(A_79,D_78),B_80)
      | ~ m1_subset_1(D_78,k1_zfmisc_1(A_79))
      | ~ m1_subset_1(k7_setfam_1(A_79,B_80),k1_zfmisc_1(k1_zfmisc_1(A_79)))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k1_zfmisc_1(A_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_676,plain,(
    ! [B_80] :
      ( r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2',B_80))
      | ~ r2_hidden('#skF_4',B_80)
      | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(k7_setfam_1('#skF_2',B_80),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_668])).

tff(c_5447,plain,(
    ! [B_227] :
      ( r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2',B_227))
      | ~ r2_hidden('#skF_4',B_227)
      | ~ m1_subset_1(k7_setfam_1('#skF_2',B_227),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(B_227,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1849,c_676])).

tff(c_5463,plain,(
    ! [B_228] :
      ( r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2',B_228))
      | ~ r2_hidden('#skF_4',B_228)
      | ~ m1_subset_1(B_228,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_22,c_5447])).

tff(c_5510,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_5463,c_56])).

tff(c_5550,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_57,c_5510])).

tff(c_5551,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_5833,plain,(
    ! [A_254,B_255] :
      ( m1_subset_1(k7_setfam_1(A_254,B_255),k1_zfmisc_1(k1_zfmisc_1(A_254)))
      | ~ m1_subset_1(B_255,k1_zfmisc_1(k1_zfmisc_1(A_254))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5886,plain,(
    ! [A_259,B_260] :
      ( r1_tarski(k7_setfam_1(A_259,B_260),k1_zfmisc_1(A_259))
      | ~ m1_subset_1(B_260,k1_zfmisc_1(k1_zfmisc_1(A_259))) ) ),
    inference(resolution,[status(thm)],[c_5833,c_24])).

tff(c_5553,plain,(
    r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_5551,c_40])).

tff(c_5555,plain,(
    ! [A_229,C_230,B_231] :
      ( m1_subset_1(A_229,C_230)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(C_230))
      | ~ r2_hidden(A_229,B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5629,plain,(
    ! [A_239,B_240,A_241] :
      ( m1_subset_1(A_239,B_240)
      | ~ r2_hidden(A_239,A_241)
      | ~ r1_tarski(A_241,B_240) ) ),
    inference(resolution,[status(thm)],[c_26,c_5555])).

tff(c_5632,plain,(
    ! [B_240] :
      ( m1_subset_1(k3_subset_1('#skF_2','#skF_4'),B_240)
      | ~ r1_tarski(k7_setfam_1('#skF_2','#skF_3'),B_240) ) ),
    inference(resolution,[status(thm)],[c_5553,c_5629])).

tff(c_5890,plain,
    ( m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_5886,c_5632])).

tff(c_5896,plain,(
    m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_5890])).

tff(c_5637,plain,(
    ! [A_244,B_245] :
      ( k3_subset_1(A_244,k3_subset_1(A_244,B_245)) = B_245
      | ~ m1_subset_1(B_245,k1_zfmisc_1(A_244)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5649,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_5637])).

tff(c_6195,plain,(
    ! [A_278,D_279,B_280] :
      ( r2_hidden(k3_subset_1(A_278,D_279),B_280)
      | ~ r2_hidden(D_279,k7_setfam_1(A_278,B_280))
      | ~ m1_subset_1(D_279,k1_zfmisc_1(A_278))
      | ~ m1_subset_1(k7_setfam_1(A_278,B_280),k1_zfmisc_1(k1_zfmisc_1(A_278)))
      | ~ m1_subset_1(B_280,k1_zfmisc_1(k1_zfmisc_1(A_278))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6809,plain,(
    ! [A_303,D_304,B_305] :
      ( r2_hidden(k3_subset_1(A_303,D_304),B_305)
      | ~ r2_hidden(D_304,k7_setfam_1(A_303,B_305))
      | ~ m1_subset_1(D_304,k1_zfmisc_1(A_303))
      | ~ m1_subset_1(B_305,k1_zfmisc_1(k1_zfmisc_1(A_303))) ) ),
    inference(resolution,[status(thm)],[c_22,c_6195])).

tff(c_6824,plain,(
    ! [D_306] :
      ( r2_hidden(k3_subset_1('#skF_2',D_306),'#skF_3')
      | ~ r2_hidden(D_306,k7_setfam_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_306,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_32,c_6809])).

tff(c_6853,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | ~ r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5649,c_6824])).

tff(c_6865,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5896,c_5553,c_6853])).

tff(c_6867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5551,c_6865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.48/2.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.48/2.52  
% 7.48/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.48/2.52  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 7.48/2.52  
% 7.48/2.52  %Foreground sorts:
% 7.48/2.52  
% 7.48/2.52  
% 7.48/2.52  %Background operators:
% 7.48/2.52  
% 7.48/2.52  
% 7.48/2.52  %Foreground operators:
% 7.48/2.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.48/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.48/2.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.48/2.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.48/2.52  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 7.48/2.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.48/2.52  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.48/2.52  tff('#skF_2', type, '#skF_2': $i).
% 7.48/2.52  tff('#skF_3', type, '#skF_3': $i).
% 7.48/2.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.48/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.48/2.52  tff('#skF_4', type, '#skF_4': $i).
% 7.48/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.48/2.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.48/2.52  
% 7.48/2.53  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_setfam_1)).
% 7.48/2.53  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 7.48/2.53  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 7.48/2.53  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.48/2.53  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.48/2.53  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 7.48/2.53  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 7.48/2.53  tff(f_63, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 7.48/2.53  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.48/2.53  tff(c_34, plain, (~r2_hidden('#skF_4', '#skF_3') | ~r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.48/2.53  tff(c_56, plain, (~r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_34])).
% 7.48/2.53  tff(c_40, plain, (r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3')) | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.48/2.53  tff(c_57, plain, (r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_40])).
% 7.48/2.53  tff(c_22, plain, (![A_18, B_19]: (m1_subset_1(k7_setfam_1(A_18, B_19), k1_zfmisc_1(k1_zfmisc_1(A_18))) | ~m1_subset_1(B_19, k1_zfmisc_1(k1_zfmisc_1(A_18))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.48/2.53  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.48/2.53  tff(c_58, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k3_subset_1(A_32, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.48/2.53  tff(c_70, plain, (k4_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_58])).
% 7.48/2.53  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.48/2.53  tff(c_74, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_4'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_70, c_2])).
% 7.48/2.53  tff(c_26, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.48/2.53  tff(c_152, plain, (![A_48, B_49]: (k3_subset_1(A_48, k3_subset_1(A_48, B_49))=B_49 | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.48/2.53  tff(c_164, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_30, c_152])).
% 7.48/2.53  tff(c_761, plain, (![A_85, D_86, B_87]: (r2_hidden(k3_subset_1(A_85, D_86), B_87) | ~r2_hidden(D_86, k7_setfam_1(A_85, B_87)) | ~m1_subset_1(D_86, k1_zfmisc_1(A_85)) | ~m1_subset_1(k7_setfam_1(A_85, B_87), k1_zfmisc_1(k1_zfmisc_1(A_85))) | ~m1_subset_1(B_87, k1_zfmisc_1(k1_zfmisc_1(A_85))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.48/2.53  tff(c_1320, plain, (![A_105, D_106, B_107]: (r2_hidden(k3_subset_1(A_105, D_106), B_107) | ~r2_hidden(D_106, k7_setfam_1(A_105, B_107)) | ~m1_subset_1(D_106, k1_zfmisc_1(A_105)) | ~m1_subset_1(B_107, k1_zfmisc_1(k1_zfmisc_1(A_105))))), inference(resolution, [status(thm)], [c_22, c_761])).
% 7.48/2.53  tff(c_1446, plain, (![A_116, D_117, A_118]: (r2_hidden(k3_subset_1(A_116, D_117), A_118) | ~r2_hidden(D_117, k7_setfam_1(A_116, A_118)) | ~m1_subset_1(D_117, k1_zfmisc_1(A_116)) | ~r1_tarski(A_118, k1_zfmisc_1(A_116)))), inference(resolution, [status(thm)], [c_26, c_1320])).
% 7.48/2.53  tff(c_1502, plain, (![A_118]: (r2_hidden('#skF_4', A_118) | ~r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', A_118)) | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2')) | ~r1_tarski(A_118, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_164, c_1446])).
% 7.48/2.53  tff(c_1836, plain, (~m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1502])).
% 7.48/2.53  tff(c_1842, plain, (~r1_tarski(k3_subset_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_26, c_1836])).
% 7.48/2.53  tff(c_1847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1842])).
% 7.48/2.53  tff(c_1849, plain, (m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1502])).
% 7.48/2.53  tff(c_668, plain, (![D_78, A_79, B_80]: (r2_hidden(D_78, k7_setfam_1(A_79, B_80)) | ~r2_hidden(k3_subset_1(A_79, D_78), B_80) | ~m1_subset_1(D_78, k1_zfmisc_1(A_79)) | ~m1_subset_1(k7_setfam_1(A_79, B_80), k1_zfmisc_1(k1_zfmisc_1(A_79))) | ~m1_subset_1(B_80, k1_zfmisc_1(k1_zfmisc_1(A_79))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.48/2.53  tff(c_676, plain, (![B_80]: (r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', B_80)) | ~r2_hidden('#skF_4', B_80) | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', B_80), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(B_80, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_164, c_668])).
% 7.48/2.53  tff(c_5447, plain, (![B_227]: (r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', B_227)) | ~r2_hidden('#skF_4', B_227) | ~m1_subset_1(k7_setfam_1('#skF_2', B_227), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(B_227, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1849, c_676])).
% 7.48/2.53  tff(c_5463, plain, (![B_228]: (r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', B_228)) | ~r2_hidden('#skF_4', B_228) | ~m1_subset_1(B_228, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_22, c_5447])).
% 7.48/2.53  tff(c_5510, plain, (~r2_hidden('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_5463, c_56])).
% 7.48/2.53  tff(c_5550, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_57, c_5510])).
% 7.48/2.53  tff(c_5551, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 7.48/2.53  tff(c_5833, plain, (![A_254, B_255]: (m1_subset_1(k7_setfam_1(A_254, B_255), k1_zfmisc_1(k1_zfmisc_1(A_254))) | ~m1_subset_1(B_255, k1_zfmisc_1(k1_zfmisc_1(A_254))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.48/2.53  tff(c_24, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.48/2.53  tff(c_5886, plain, (![A_259, B_260]: (r1_tarski(k7_setfam_1(A_259, B_260), k1_zfmisc_1(A_259)) | ~m1_subset_1(B_260, k1_zfmisc_1(k1_zfmisc_1(A_259))))), inference(resolution, [status(thm)], [c_5833, c_24])).
% 7.48/2.53  tff(c_5553, plain, (r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_5551, c_40])).
% 7.48/2.53  tff(c_5555, plain, (![A_229, C_230, B_231]: (m1_subset_1(A_229, C_230) | ~m1_subset_1(B_231, k1_zfmisc_1(C_230)) | ~r2_hidden(A_229, B_231))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.48/2.53  tff(c_5629, plain, (![A_239, B_240, A_241]: (m1_subset_1(A_239, B_240) | ~r2_hidden(A_239, A_241) | ~r1_tarski(A_241, B_240))), inference(resolution, [status(thm)], [c_26, c_5555])).
% 7.48/2.53  tff(c_5632, plain, (![B_240]: (m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), B_240) | ~r1_tarski(k7_setfam_1('#skF_2', '#skF_3'), B_240))), inference(resolution, [status(thm)], [c_5553, c_5629])).
% 7.48/2.53  tff(c_5890, plain, (m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_5886, c_5632])).
% 7.48/2.53  tff(c_5896, plain, (m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_5890])).
% 7.48/2.53  tff(c_5637, plain, (![A_244, B_245]: (k3_subset_1(A_244, k3_subset_1(A_244, B_245))=B_245 | ~m1_subset_1(B_245, k1_zfmisc_1(A_244)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.48/2.53  tff(c_5649, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_30, c_5637])).
% 7.48/2.53  tff(c_6195, plain, (![A_278, D_279, B_280]: (r2_hidden(k3_subset_1(A_278, D_279), B_280) | ~r2_hidden(D_279, k7_setfam_1(A_278, B_280)) | ~m1_subset_1(D_279, k1_zfmisc_1(A_278)) | ~m1_subset_1(k7_setfam_1(A_278, B_280), k1_zfmisc_1(k1_zfmisc_1(A_278))) | ~m1_subset_1(B_280, k1_zfmisc_1(k1_zfmisc_1(A_278))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.48/2.53  tff(c_6809, plain, (![A_303, D_304, B_305]: (r2_hidden(k3_subset_1(A_303, D_304), B_305) | ~r2_hidden(D_304, k7_setfam_1(A_303, B_305)) | ~m1_subset_1(D_304, k1_zfmisc_1(A_303)) | ~m1_subset_1(B_305, k1_zfmisc_1(k1_zfmisc_1(A_303))))), inference(resolution, [status(thm)], [c_22, c_6195])).
% 7.48/2.53  tff(c_6824, plain, (![D_306]: (r2_hidden(k3_subset_1('#skF_2', D_306), '#skF_3') | ~r2_hidden(D_306, k7_setfam_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_306, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_32, c_6809])).
% 7.48/2.53  tff(c_6853, plain, (r2_hidden('#skF_4', '#skF_3') | ~r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3')) | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5649, c_6824])).
% 7.48/2.53  tff(c_6865, plain, (r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5896, c_5553, c_6853])).
% 7.48/2.53  tff(c_6867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5551, c_6865])).
% 7.48/2.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.48/2.53  
% 7.48/2.53  Inference rules
% 7.48/2.53  ----------------------
% 7.48/2.53  #Ref     : 0
% 7.48/2.53  #Sup     : 1656
% 7.48/2.53  #Fact    : 0
% 7.48/2.53  #Define  : 0
% 7.48/2.53  #Split   : 11
% 7.48/2.53  #Chain   : 0
% 7.48/2.53  #Close   : 0
% 7.48/2.54  
% 7.48/2.54  Ordering : KBO
% 7.48/2.54  
% 7.48/2.54  Simplification rules
% 7.48/2.54  ----------------------
% 7.48/2.54  #Subsume      : 188
% 7.48/2.54  #Demod        : 1261
% 7.48/2.54  #Tautology    : 732
% 7.48/2.54  #SimpNegUnit  : 15
% 7.48/2.54  #BackRed      : 30
% 7.48/2.54  
% 7.48/2.54  #Partial instantiations: 0
% 7.48/2.54  #Strategies tried      : 1
% 7.48/2.54  
% 7.48/2.54  Timing (in seconds)
% 7.48/2.54  ----------------------
% 7.48/2.54  Preprocessing        : 0.31
% 7.48/2.54  Parsing              : 0.16
% 7.48/2.54  CNF conversion       : 0.02
% 7.48/2.54  Main loop            : 1.46
% 7.48/2.54  Inferencing          : 0.47
% 7.48/2.54  Reduction            : 0.51
% 7.48/2.54  Demodulation         : 0.37
% 7.48/2.54  BG Simplification    : 0.06
% 7.48/2.54  Subsumption          : 0.31
% 7.48/2.54  Abstraction          : 0.08
% 7.48/2.54  MUC search           : 0.00
% 7.48/2.54  Cooper               : 0.00
% 7.48/2.54  Total                : 1.81
% 7.48/2.54  Index Insertion      : 0.00
% 7.48/2.54  Index Deletion       : 0.00
% 7.48/2.54  Index Matching       : 0.00
% 7.48/2.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
