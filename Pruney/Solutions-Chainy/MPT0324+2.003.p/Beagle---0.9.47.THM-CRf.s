%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:20 EST 2020

% Result     : Theorem 26.80s
% Output     : CNFRefutation 27.34s
% Verified   : 
% Statistics : Number of formulae       :  763 (36801 expanded)
%              Number of leaves         :   21 (11963 expanded)
%              Depth                    :   22
%              Number of atoms          : 1065 (90334 expanded)
%              Number of equality atoms :    3 (9552 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( ( r2_hidden(A,k2_zfmisc_1(B,C))
          & r2_hidden(A,k2_zfmisc_1(D,E)) )
       => r2_hidden(A,k2_zfmisc_1(k3_xboole_0(B,D),k3_xboole_0(C,E))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_30,plain,(
    ~ r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_7','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_143,plain,(
    ! [A_47,B_48,C_49] :
      ( k4_tarski('#skF_3'(A_47,B_48,C_49),'#skF_4'(A_47,B_48,C_49)) = A_47
      | ~ r2_hidden(A_47,k2_zfmisc_1(B_48,C_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    ! [A_14,C_16,B_15,D_17] :
      ( r2_hidden(A_14,C_16)
      | ~ r2_hidden(k4_tarski(A_14,B_15),k2_zfmisc_1(C_16,D_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_277,plain,(
    ! [D_73,C_75,B_74,A_72,C_76] :
      ( r2_hidden('#skF_3'(A_72,B_74,C_76),C_75)
      | ~ r2_hidden(A_72,k2_zfmisc_1(C_75,D_73))
      | ~ r2_hidden(A_72,k2_zfmisc_1(B_74,C_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_28])).

tff(c_310,plain,(
    ! [B_74,C_76] :
      ( r2_hidden('#skF_3'('#skF_5',B_74,C_76),'#skF_6')
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_74,C_76)) ) ),
    inference(resolution,[status(thm)],[c_34,c_277])).

tff(c_32,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_309,plain,(
    ! [B_74,C_76] :
      ( r2_hidden('#skF_3'('#skF_5',B_74,C_76),'#skF_8')
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_74,C_76)) ) ),
    inference(resolution,[status(thm)],[c_32,c_277])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,(
    ! [B_15,D_17,A_14,C_16] :
      ( r2_hidden(B_15,D_17)
      | ~ r2_hidden(k4_tarski(A_14,B_15),k2_zfmisc_1(C_16,D_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_241,plain,(
    ! [C_67,D_64,A_63,C_66,B_65] :
      ( r2_hidden('#skF_4'(A_63,B_65,C_67),D_64)
      | ~ r2_hidden(A_63,k2_zfmisc_1(C_66,D_64))
      | ~ r2_hidden(A_63,k2_zfmisc_1(B_65,C_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_26])).

tff(c_273,plain,(
    ! [B_65,C_67] :
      ( r2_hidden('#skF_4'('#skF_5',B_65,C_67),'#skF_9')
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_65,C_67)) ) ),
    inference(resolution,[status(thm)],[c_32,c_241])).

tff(c_24,plain,(
    ! [A_14,B_15,C_16,D_17] :
      ( r2_hidden(k4_tarski(A_14,B_15),k2_zfmisc_1(C_16,D_17))
      | ~ r2_hidden(B_15,D_17)
      | ~ r2_hidden(A_14,C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2774,plain,(
    ! [B_211,A_209,D_210,C_213,C_212] :
      ( r2_hidden(A_209,k2_zfmisc_1(C_212,D_210))
      | ~ r2_hidden('#skF_4'(A_209,B_211,C_213),D_210)
      | ~ r2_hidden('#skF_3'(A_209,B_211,C_213),C_212)
      | ~ r2_hidden(A_209,k2_zfmisc_1(B_211,C_213)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_24])).

tff(c_2821,plain,(
    ! [C_217,B_218,C_219] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(C_217,'#skF_9'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_218,C_219),C_217)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_218,C_219)) ) ),
    inference(resolution,[status(thm)],[c_273,c_2774])).

tff(c_6223,plain,(
    ! [A_364,B_365,B_366,C_367] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(A_364,B_365),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_366,C_367))
      | ~ r2_hidden('#skF_3'('#skF_5',B_366,C_367),B_365)
      | ~ r2_hidden('#skF_3'('#skF_5',B_366,C_367),A_364) ) ),
    inference(resolution,[status(thm)],[c_2,c_2821])).

tff(c_6547,plain,(
    ! [A_381,B_382,C_383] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(A_381,'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_382,C_383),A_381)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_382,C_383)) ) ),
    inference(resolution,[status(thm)],[c_309,c_6223])).

tff(c_6558,plain,(
    ! [B_74,C_76] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6','#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_74,C_76)) ) ),
    inference(resolution,[status(thm)],[c_310,c_6547])).

tff(c_6574,plain,(
    ! [B_74,C_76] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_74,C_76)) ),
    inference(splitLeft,[status(thm)],[c_6558])).

tff(c_6234,plain,(
    ! [A_368,B_369,C_370] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(A_368,'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_369,C_370),A_368)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_369,C_370)) ) ),
    inference(resolution,[status(thm)],[c_310,c_6223])).

tff(c_6244,plain,(
    ! [B_74,C_76] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8','#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_74,C_76)) ) ),
    inference(resolution,[status(thm)],[c_309,c_6234])).

tff(c_6246,plain,(
    ! [B_74,C_76] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_74,C_76)) ),
    inference(splitLeft,[status(thm)],[c_6244])).

tff(c_2832,plain,(
    ! [B_74,C_76] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6','#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_74,C_76)) ) ),
    inference(resolution,[status(thm)],[c_310,c_2821])).

tff(c_2836,plain,(
    ! [B_74,C_76] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_74,C_76)) ),
    inference(splitLeft,[status(thm)],[c_2832])).

tff(c_274,plain,(
    ! [B_65,C_67] :
      ( r2_hidden('#skF_4'('#skF_5',B_65,C_67),'#skF_7')
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_65,C_67)) ) ),
    inference(resolution,[status(thm)],[c_34,c_241])).

tff(c_2788,plain,(
    ! [C_214,B_215,C_216] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(C_214,'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_215,C_216),C_214)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_215,C_216)) ) ),
    inference(resolution,[status(thm)],[c_274,c_2774])).

tff(c_2801,plain,(
    ! [B_74,C_76] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8','#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_74,C_76)) ) ),
    inference(resolution,[status(thm)],[c_309,c_2788])).

tff(c_2803,plain,(
    ! [B_74,C_76] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_74,C_76)) ),
    inference(splitLeft,[status(thm)],[c_2801])).

tff(c_2807,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2803,c_32])).

tff(c_2808,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_2801])).

tff(c_2842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2836,c_2808])).

tff(c_2843,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_2832])).

tff(c_6268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6246,c_2843])).

tff(c_6269,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8','#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_6244])).

tff(c_152,plain,(
    ! [A_47,C_16,D_17,C_49,B_48] :
      ( r2_hidden('#skF_3'(A_47,B_48,C_49),C_16)
      | ~ r2_hidden(A_47,k2_zfmisc_1(C_16,D_17))
      | ~ r2_hidden(A_47,k2_zfmisc_1(B_48,C_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_28])).

tff(c_6282,plain,(
    ! [B_374,C_375] :
      ( r2_hidden('#skF_3'('#skF_5',B_374,C_375),k3_xboole_0('#skF_8','#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_374,C_375)) ) ),
    inference(resolution,[status(thm)],[c_6269,c_152])).

tff(c_6231,plain,(
    ! [A_364,B_74,C_76] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(A_364,'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_74,C_76),A_364)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_74,C_76)) ) ),
    inference(resolution,[status(thm)],[c_310,c_6223])).

tff(c_6311,plain,(
    ! [B_374,C_375] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_374,C_375)) ) ),
    inference(resolution,[status(thm)],[c_6282,c_6231])).

tff(c_6534,plain,(
    ! [B_374,C_375] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_374,C_375)) ),
    inference(splitLeft,[status(thm)],[c_6311])).

tff(c_2785,plain,(
    ! [C_212,B_65,C_67] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(C_212,'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_65,C_67),C_212)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_65,C_67)) ) ),
    inference(resolution,[status(thm)],[c_274,c_2774])).

tff(c_6315,plain,(
    ! [B_374,C_375] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8','#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_374,C_375)) ) ),
    inference(resolution,[status(thm)],[c_6282,c_2785])).

tff(c_6324,plain,(
    ! [B_374,C_375] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_374,C_375)) ),
    inference(splitLeft,[status(thm)],[c_6315])).

tff(c_6334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6324,c_6269])).

tff(c_6335,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8','#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_6315])).

tff(c_6545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6534,c_6335])).

tff(c_6546,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_6311])).

tff(c_6587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6574,c_6546])).

tff(c_6588,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6','#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_6558])).

tff(c_6599,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_3'('#skF_5',B_48,C_49),k3_xboole_0('#skF_6','#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_6588,c_152])).

tff(c_52602,plain,(
    ! [A_1020,A_1019,B_1017,C_1016,C_1021,B_1018] :
      ( r2_hidden(A_1020,k2_zfmisc_1(C_1016,k3_xboole_0(A_1019,B_1018)))
      | ~ r2_hidden('#skF_3'(A_1020,B_1017,C_1021),C_1016)
      | ~ r2_hidden(A_1020,k2_zfmisc_1(B_1017,C_1021))
      | ~ r2_hidden('#skF_4'(A_1020,B_1017,C_1021),B_1018)
      | ~ r2_hidden('#skF_4'(A_1020,B_1017,C_1021),A_1019) ) ),
    inference(resolution,[status(thm)],[c_2,c_2774])).

tff(c_52991,plain,(
    ! [A_1022,B_1023,B_1024,C_1025] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(A_1022,B_1023)))
      | ~ r2_hidden('#skF_4'('#skF_5',B_1024,C_1025),B_1023)
      | ~ r2_hidden('#skF_4'('#skF_5',B_1024,C_1025),A_1022)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1024,C_1025)) ) ),
    inference(resolution,[status(thm)],[c_310,c_52602])).

tff(c_53584,plain,(
    ! [A_1035,B_1036,C_1037] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(A_1035,'#skF_9')))
      | ~ r2_hidden('#skF_4'('#skF_5',B_1036,C_1037),A_1035)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1036,C_1037)) ) ),
    inference(resolution,[status(thm)],[c_273,c_52991])).

tff(c_53595,plain,(
    ! [B_65,C_67] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0('#skF_7','#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_65,C_67)) ) ),
    inference(resolution,[status(thm)],[c_274,c_53584])).

tff(c_53599,plain,(
    ! [B_65,C_67] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_65,C_67)) ),
    inference(splitLeft,[status(thm)],[c_53595])).

tff(c_53002,plain,(
    ! [A_1026,B_1027,C_1028] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(A_1026,'#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_5',B_1027,C_1028),A_1026)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1027,C_1028)) ) ),
    inference(resolution,[status(thm)],[c_274,c_52991])).

tff(c_53012,plain,(
    ! [B_65,C_67] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0('#skF_9','#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_65,C_67)) ) ),
    inference(resolution,[status(thm)],[c_273,c_53002])).

tff(c_53014,plain,(
    ! [B_65,C_67] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_65,C_67)) ),
    inference(splitLeft,[status(thm)],[c_53012])).

tff(c_2835,plain,(
    ! [A_1,B_2,B_218,C_219] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(A_1,B_2),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_218,C_219))
      | ~ r2_hidden('#skF_3'('#skF_5',B_218,C_219),B_2)
      | ~ r2_hidden('#skF_3'('#skF_5',B_218,C_219),A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_2821])).

tff(c_44253,plain,(
    ! [A_943,B_944,C_945] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(A_943,k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_944,C_945),A_943)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_944,C_945)) ) ),
    inference(resolution,[status(thm)],[c_6282,c_2835])).

tff(c_44421,plain,(
    ! [B_74,C_76] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_74,C_76)) ) ),
    inference(resolution,[status(thm)],[c_310,c_44253])).

tff(c_44582,plain,(
    ! [B_74,C_76] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_74,C_76)) ),
    inference(splitLeft,[status(thm)],[c_44421])).

tff(c_6601,plain,(
    ! [B_384,C_385] :
      ( r2_hidden('#skF_3'('#skF_5',B_384,C_385),k3_xboole_0('#skF_6','#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_384,C_385)) ) ),
    inference(resolution,[status(thm)],[c_6588,c_152])).

tff(c_23815,plain,(
    ! [A_720,B_721,C_722] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(A_720,k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_721,C_722),A_720)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_721,C_722)) ) ),
    inference(resolution,[status(thm)],[c_6601,c_2835])).

tff(c_23915,plain,(
    ! [B_74,C_76] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_74,C_76)) ) ),
    inference(resolution,[status(thm)],[c_309,c_23815])).

tff(c_24014,plain,(
    ! [B_74,C_76] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_74,C_76)) ),
    inference(splitLeft,[status(thm)],[c_23915])).

tff(c_23914,plain,(
    ! [B_74,C_76] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_74,C_76)) ) ),
    inference(resolution,[status(thm)],[c_310,c_23815])).

tff(c_23917,plain,(
    ! [B_74,C_76] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_74,C_76)) ),
    inference(splitLeft,[status(thm)],[c_23914])).

tff(c_7393,plain,(
    ! [B_403,C_404] :
      ( r2_hidden('#skF_3'('#skF_5',B_403,C_404),k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_403,C_404)) ) ),
    inference(resolution,[status(thm)],[c_6546,c_152])).

tff(c_7425,plain,(
    ! [B_403,C_404] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_403,C_404)) ) ),
    inference(resolution,[status(thm)],[c_7393,c_6231])).

tff(c_8267,plain,(
    ! [B_403,C_404] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_403,C_404)) ),
    inference(splitLeft,[status(thm)],[c_7425])).

tff(c_6232,plain,(
    ! [A_364,B_74,C_76] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(A_364,'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_74,C_76),A_364)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_74,C_76)) ) ),
    inference(resolution,[status(thm)],[c_309,c_6223])).

tff(c_7424,plain,(
    ! [B_403,C_404] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_403,C_404)) ) ),
    inference(resolution,[status(thm)],[c_7393,c_6232])).

tff(c_8227,plain,(
    ! [B_403,C_404] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_403,C_404)) ),
    inference(splitLeft,[status(thm)],[c_7424])).

tff(c_6633,plain,(
    ! [B_384,C_385] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_384,C_385)) ) ),
    inference(resolution,[status(thm)],[c_6601,c_6231])).

tff(c_6845,plain,(
    ! [B_384,C_385] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_384,C_385)) ),
    inference(splitLeft,[status(thm)],[c_6633])).

tff(c_6637,plain,(
    ! [B_384,C_385] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6','#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_384,C_385)) ) ),
    inference(resolution,[status(thm)],[c_6601,c_2785])).

tff(c_6817,plain,(
    ! [B_384,C_385] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_384,C_385)) ),
    inference(splitLeft,[status(thm)],[c_6637])).

tff(c_6831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6817,c_6588])).

tff(c_6832,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6','#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_6637])).

tff(c_6860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6845,c_6832])).

tff(c_6861,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_6633])).

tff(c_7471,plain,(
    ! [B_405,C_406] :
      ( r2_hidden('#skF_3'('#skF_5',B_405,C_406),k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_405,C_406)) ) ),
    inference(resolution,[status(thm)],[c_6861,c_152])).

tff(c_7503,plain,(
    ! [B_405,C_406] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_405,C_406)) ) ),
    inference(resolution,[status(thm)],[c_7471,c_6231])).

tff(c_8188,plain,(
    ! [B_405,C_406] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_405,C_406)) ),
    inference(splitLeft,[status(thm)],[c_7503])).

tff(c_6632,plain,(
    ! [B_384,C_385] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_384,C_385)) ) ),
    inference(resolution,[status(thm)],[c_6601,c_6232])).

tff(c_7100,plain,(
    ! [B_384,C_385] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_384,C_385)) ),
    inference(splitLeft,[status(thm)],[c_6632])).

tff(c_6280,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_3'('#skF_5',B_48,C_49),k3_xboole_0('#skF_8','#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_6269,c_152])).

tff(c_6557,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_6280,c_6547])).

tff(c_6874,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_6557])).

tff(c_6890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6874,c_6861])).

tff(c_6891,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_6557])).

tff(c_7117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7100,c_6891])).

tff(c_7118,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_6632])).

tff(c_7736,plain,(
    ! [B_412,C_413] :
      ( r2_hidden('#skF_3'('#skF_5',B_412,C_413),k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_412,C_413)) ) ),
    inference(resolution,[status(thm)],[c_7118,c_152])).

tff(c_7772,plain,(
    ! [B_412,C_413] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_412,C_413)) ) ),
    inference(resolution,[status(thm)],[c_7736,c_2785])).

tff(c_7781,plain,(
    ! [B_412,C_413] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_412,C_413)) ),
    inference(splitLeft,[status(thm)],[c_7772])).

tff(c_7507,plain,(
    ! [B_405,C_406] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_405,C_406)) ) ),
    inference(resolution,[status(thm)],[c_7471,c_2785])).

tff(c_7516,plain,(
    ! [B_405,C_406] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_405,C_406)) ),
    inference(splitLeft,[status(thm)],[c_7507])).

tff(c_7429,plain,(
    ! [B_403,C_404] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_403,C_404)) ) ),
    inference(resolution,[status(thm)],[c_7393,c_2785])).

tff(c_7438,plain,(
    ! [B_403,C_404] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_403,C_404)) ),
    inference(splitLeft,[status(thm)],[c_7429])).

tff(c_7131,plain,(
    ! [B_396,C_397] :
      ( r2_hidden('#skF_3'('#skF_5',B_396,C_397),k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_396,C_397)) ) ),
    inference(resolution,[status(thm)],[c_6891,c_152])).

tff(c_7167,plain,(
    ! [B_396,C_397] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_396,C_397)) ) ),
    inference(resolution,[status(thm)],[c_7131,c_2785])).

tff(c_7176,plain,(
    ! [B_396,C_397] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_396,C_397)) ),
    inference(splitLeft,[status(thm)],[c_7167])).

tff(c_7194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7176,c_7118])).

tff(c_7195,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_7167])).

tff(c_7457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7438,c_7195])).

tff(c_7458,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_7429])).

tff(c_7536,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7516,c_7458])).

tff(c_7537,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_7507])).

tff(c_7802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7781,c_7537])).

tff(c_7803,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_7772])).

tff(c_8210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8188,c_7803])).

tff(c_8211,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_7503])).

tff(c_8250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8227,c_8211])).

tff(c_8251,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_7424])).

tff(c_8298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8267,c_8251])).

tff(c_8299,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_7425])).

tff(c_10341,plain,(
    ! [B_480,C_481] :
      ( r2_hidden('#skF_3'('#skF_5',B_480,C_481),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_480,C_481)) ) ),
    inference(resolution,[status(thm)],[c_8299,c_152])).

tff(c_10372,plain,(
    ! [B_480,C_481] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_480,C_481)) ) ),
    inference(resolution,[status(thm)],[c_10341,c_6232])).

tff(c_12066,plain,(
    ! [B_480,C_481] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_480,C_481)) ),
    inference(splitLeft,[status(thm)],[c_10372])).

tff(c_7768,plain,(
    ! [B_412,C_413] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_412,C_413)) ) ),
    inference(resolution,[status(thm)],[c_7736,c_6231])).

tff(c_8407,plain,(
    ! [B_412,C_413] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_412,C_413)) ),
    inference(splitLeft,[status(thm)],[c_7768])).

tff(c_7502,plain,(
    ! [B_405,C_406] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_405,C_406)) ) ),
    inference(resolution,[status(thm)],[c_7471,c_6232])).

tff(c_8357,plain,(
    ! [B_405,C_406] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_405,C_406)) ),
    inference(splitLeft,[status(thm)],[c_7502])).

tff(c_7163,plain,(
    ! [B_396,C_397] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_396,C_397)) ) ),
    inference(resolution,[status(thm)],[c_7131,c_6231])).

tff(c_8315,plain,(
    ! [B_396,C_397] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_396,C_397)) ),
    inference(splitLeft,[status(thm)],[c_7163])).

tff(c_8340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8315,c_8299])).

tff(c_8341,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_7163])).

tff(c_8383,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8357,c_8341])).

tff(c_8384,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_7502])).

tff(c_8434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8407,c_8384])).

tff(c_8435,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_7768])).

tff(c_10640,plain,(
    ! [B_487,C_488] :
      ( r2_hidden('#skF_3'('#skF_5',B_487,C_488),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_487,C_488)) ) ),
    inference(resolution,[status(thm)],[c_8435,c_152])).

tff(c_10676,plain,(
    ! [B_487,C_488] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_487,C_488)) ) ),
    inference(resolution,[status(thm)],[c_10640,c_2785])).

tff(c_10685,plain,(
    ! [B_487,C_488] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_487,C_488)) ),
    inference(splitLeft,[status(thm)],[c_10676])).

tff(c_10377,plain,(
    ! [B_480,C_481] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_480,C_481)) ) ),
    inference(resolution,[status(thm)],[c_10341,c_2785])).

tff(c_10386,plain,(
    ! [B_480,C_481] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_480,C_481)) ),
    inference(splitLeft,[status(thm)],[c_10377])).

tff(c_7162,plain,(
    ! [B_396,C_397] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_396,C_397)) ) ),
    inference(resolution,[status(thm)],[c_7131,c_6232])).

tff(c_8700,plain,(
    ! [B_396,C_397] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_396,C_397)) ),
    inference(splitLeft,[status(thm)],[c_7162])).

tff(c_7767,plain,(
    ! [B_412,C_413] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_412,C_413)) ) ),
    inference(resolution,[status(thm)],[c_7736,c_6232])).

tff(c_8451,plain,(
    ! [B_412,C_413] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_412,C_413)) ),
    inference(splitLeft,[status(thm)],[c_7767])).

tff(c_8479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8451,c_8435])).

tff(c_8480,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_7767])).

tff(c_8729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8700,c_8480])).

tff(c_8730,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_7162])).

tff(c_10231,plain,(
    ! [B_474,C_475] :
      ( r2_hidden('#skF_3'('#skF_5',B_474,C_475),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_474,C_475)) ) ),
    inference(resolution,[status(thm)],[c_8730,c_152])).

tff(c_10267,plain,(
    ! [B_474,C_475] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_474,C_475)) ) ),
    inference(resolution,[status(thm)],[c_10231,c_2785])).

tff(c_10276,plain,(
    ! [B_474,C_475] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_474,C_475)) ),
    inference(splitLeft,[status(thm)],[c_10267])).

tff(c_9955,plain,(
    ! [B_467,C_468] :
      ( r2_hidden('#skF_3'('#skF_5',B_467,C_468),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_467,C_468)) ) ),
    inference(resolution,[status(thm)],[c_8341,c_152])).

tff(c_9991,plain,(
    ! [B_467,C_468] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_467,C_468)) ) ),
    inference(resolution,[status(thm)],[c_9955,c_2785])).

tff(c_10000,plain,(
    ! [B_467,C_468] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_467,C_468)) ),
    inference(splitLeft,[status(thm)],[c_9991])).

tff(c_9847,plain,(
    ! [B_461,C_462] :
      ( r2_hidden('#skF_3'('#skF_5',B_461,C_462),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_461,C_462)) ) ),
    inference(resolution,[status(thm)],[c_8384,c_152])).

tff(c_9883,plain,(
    ! [B_461,C_462] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_461,C_462)) ) ),
    inference(resolution,[status(thm)],[c_9847,c_2785])).

tff(c_9892,plain,(
    ! [B_461,C_462] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_461,C_462)) ),
    inference(splitLeft,[status(thm)],[c_9883])).

tff(c_9546,plain,(
    ! [B_454,C_455] :
      ( r2_hidden('#skF_3'('#skF_5',B_454,C_455),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_454,C_455)) ) ),
    inference(resolution,[status(thm)],[c_8211,c_152])).

tff(c_9582,plain,(
    ! [B_454,C_455] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_454,C_455)) ) ),
    inference(resolution,[status(thm)],[c_9546,c_2785])).

tff(c_9591,plain,(
    ! [B_454,C_455] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_454,C_455)) ),
    inference(splitLeft,[status(thm)],[c_9582])).

tff(c_9035,plain,(
    ! [B_445,C_446] :
      ( r2_hidden('#skF_3'('#skF_5',B_445,C_446),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_445,C_446)) ) ),
    inference(resolution,[status(thm)],[c_8251,c_152])).

tff(c_9071,plain,(
    ! [B_445,C_446] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_445,C_446)) ) ),
    inference(resolution,[status(thm)],[c_9035,c_2785])).

tff(c_9080,plain,(
    ! [B_445,C_446] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_445,C_446)) ),
    inference(splitLeft,[status(thm)],[c_9071])).

tff(c_8753,plain,(
    ! [B_438,C_439] :
      ( r2_hidden('#skF_3'('#skF_5',B_438,C_439),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_438,C_439)) ) ),
    inference(resolution,[status(thm)],[c_8480,c_152])).

tff(c_8789,plain,(
    ! [B_438,C_439] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_438,C_439)) ) ),
    inference(resolution,[status(thm)],[c_8753,c_2785])).

tff(c_8798,plain,(
    ! [B_438,C_439] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_438,C_439)) ),
    inference(splitLeft,[status(thm)],[c_8789])).

tff(c_8828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8798,c_8730])).

tff(c_8829,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_8789])).

tff(c_9111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9080,c_8829])).

tff(c_9112,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_9071])).

tff(c_9623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9591,c_9112])).

tff(c_9624,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_9582])).

tff(c_9925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9892,c_9624])).

tff(c_9926,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_9883])).

tff(c_10034,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10000,c_9926])).

tff(c_10035,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_9991])).

tff(c_10311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10276,c_10035])).

tff(c_10312,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_10267])).

tff(c_10422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10386,c_10312])).

tff(c_10423,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_10377])).

tff(c_10722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10685,c_10423])).

tff(c_10723,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_10676])).

tff(c_12104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12066,c_10723])).

tff(c_12105,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_10372])).

tff(c_23105,plain,(
    ! [B_711,C_712] :
      ( r2_hidden('#skF_3'('#skF_5',B_711,C_712),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_711,C_712)) ) ),
    inference(resolution,[status(thm)],[c_12105,c_152])).

tff(c_23162,plain,(
    ! [B_711,C_712] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_711,C_712)) ) ),
    inference(resolution,[status(thm)],[c_23105,c_2785])).

tff(c_23720,plain,(
    ! [B_711,C_712] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_711,C_712)) ),
    inference(splitLeft,[status(thm)],[c_23162])).

tff(c_9066,plain,(
    ! [B_445,C_446] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_445,C_446)) ) ),
    inference(resolution,[status(thm)],[c_9035,c_6232])).

tff(c_13188,plain,(
    ! [B_445,C_446] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_445,C_446)) ),
    inference(splitLeft,[status(thm)],[c_9066])).

tff(c_9878,plain,(
    ! [B_461,C_462] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_461,C_462)) ) ),
    inference(resolution,[status(thm)],[c_9847,c_6232])).

tff(c_12611,plain,(
    ! [B_461,C_462] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_461,C_462)) ),
    inference(splitLeft,[status(thm)],[c_9878])).

tff(c_10672,plain,(
    ! [B_487,C_488] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_487,C_488)) ) ),
    inference(resolution,[status(thm)],[c_10640,c_6231])).

tff(c_12326,plain,(
    ! [B_487,C_488] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_487,C_488)) ),
    inference(splitLeft,[status(thm)],[c_10672])).

tff(c_9578,plain,(
    ! [B_454,C_455] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_454,C_455)) ) ),
    inference(resolution,[status(thm)],[c_9546,c_6231])).

tff(c_12262,plain,(
    ! [B_454,C_455] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_454,C_455)) ),
    inference(splitLeft,[status(thm)],[c_9578])).

tff(c_10263,plain,(
    ! [B_474,C_475] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_474,C_475)) ) ),
    inference(resolution,[status(thm)],[c_10231,c_6231])).

tff(c_12189,plain,(
    ! [B_474,C_475] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_474,C_475)) ),
    inference(splitLeft,[status(thm)],[c_10263])).

tff(c_10671,plain,(
    ! [B_487,C_488] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_487,C_488)) ) ),
    inference(resolution,[status(thm)],[c_10640,c_6232])).

tff(c_12127,plain,(
    ! [B_487,C_488] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_487,C_488)) ),
    inference(splitLeft,[status(thm)],[c_10671])).

tff(c_12166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12127,c_12105])).

tff(c_12167,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_10671])).

tff(c_12229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12189,c_12167])).

tff(c_12230,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_10263])).

tff(c_12303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12262,c_12230])).

tff(c_12304,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_9578])).

tff(c_12588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12326,c_12304])).

tff(c_12589,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_10672])).

tff(c_13165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12611,c_12589])).

tff(c_13166,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_9878])).

tff(c_13232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13188,c_13166])).

tff(c_13233,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_9066])).

tff(c_22678,plain,(
    ! [B_704,C_705] :
      ( r2_hidden('#skF_3'('#skF_5',B_704,C_705),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_704,C_705)) ) ),
    inference(resolution,[status(thm)],[c_13233,c_152])).

tff(c_22735,plain,(
    ! [B_704,C_705] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_704,C_705)) ) ),
    inference(resolution,[status(thm)],[c_22678,c_2785])).

tff(c_22744,plain,(
    ! [B_704,C_705] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_704,C_705)) ),
    inference(splitLeft,[status(thm)],[c_22735])).

tff(c_21979,plain,(
    ! [B_695,C_696] :
      ( r2_hidden('#skF_3'('#skF_5',B_695,C_696),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_695,C_696)) ) ),
    inference(resolution,[status(thm)],[c_12304,c_152])).

tff(c_22033,plain,(
    ! [B_695,C_696] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_695,C_696)) ) ),
    inference(resolution,[status(thm)],[c_21979,c_2785])).

tff(c_22585,plain,(
    ! [B_695,C_696] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_695,C_696)) ),
    inference(splitLeft,[status(thm)],[c_22033])).

tff(c_21824,plain,(
    ! [B_693,C_694] :
      ( r2_hidden('#skF_3'('#skF_5',B_693,C_694),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_693,C_694)) ) ),
    inference(resolution,[status(thm)],[c_12167,c_152])).

tff(c_21878,plain,(
    ! [B_693,C_694] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_693,C_694)) ) ),
    inference(resolution,[status(thm)],[c_21824,c_2785])).

tff(c_21887,plain,(
    ! [B_693,C_694] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_693,C_694)) ),
    inference(splitLeft,[status(thm)],[c_21878])).

tff(c_21136,plain,(
    ! [B_684,C_685] :
      ( r2_hidden('#skF_3'('#skF_5',B_684,C_685),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_684,C_685)) ) ),
    inference(resolution,[status(thm)],[c_12230,c_152])).

tff(c_21187,plain,(
    ! [B_684,C_685] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_684,C_685)) ) ),
    inference(resolution,[status(thm)],[c_21136,c_2785])).

tff(c_21733,plain,(
    ! [B_684,C_685] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_684,C_685)) ),
    inference(splitLeft,[status(thm)],[c_21187])).

tff(c_20735,plain,(
    ! [B_677,C_678] :
      ( r2_hidden('#skF_3'('#skF_5',B_677,C_678),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_677,C_678)) ) ),
    inference(resolution,[status(thm)],[c_13166,c_152])).

tff(c_20786,plain,(
    ! [B_677,C_678] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_677,C_678)) ) ),
    inference(resolution,[status(thm)],[c_20735,c_2785])).

tff(c_20795,plain,(
    ! [B_677,C_678] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_677,C_678)) ),
    inference(splitLeft,[status(thm)],[c_20786])).

tff(c_8784,plain,(
    ! [B_438,C_439] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_438,C_439)) ) ),
    inference(resolution,[status(thm)],[c_8753,c_6232])).

tff(c_14916,plain,(
    ! [B_438,C_439] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_438,C_439)) ),
    inference(splitLeft,[status(thm)],[c_8784])).

tff(c_9067,plain,(
    ! [B_445,C_446] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_445,C_446)) ) ),
    inference(resolution,[status(thm)],[c_9035,c_6231])).

tff(c_14621,plain,(
    ! [B_445,C_446] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_445,C_446)) ),
    inference(splitLeft,[status(thm)],[c_9067])).

tff(c_9987,plain,(
    ! [B_467,C_468] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_467,C_468)) ) ),
    inference(resolution,[status(thm)],[c_9955,c_6231])).

tff(c_14540,plain,(
    ! [B_467,C_468] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_467,C_468)) ),
    inference(splitLeft,[status(thm)],[c_9987])).

tff(c_9577,plain,(
    ! [B_454,C_455] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_454,C_455)) ) ),
    inference(resolution,[status(thm)],[c_9546,c_6232])).

tff(c_14247,plain,(
    ! [B_454,C_455] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_454,C_455)) ),
    inference(splitLeft,[status(thm)],[c_9577])).

tff(c_10373,plain,(
    ! [B_480,C_481] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_480,C_481)) ) ),
    inference(resolution,[status(thm)],[c_10341,c_6231])).

tff(c_14175,plain,(
    ! [B_480,C_481] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_480,C_481)) ),
    inference(splitLeft,[status(thm)],[c_10373])).

tff(c_9986,plain,(
    ! [B_467,C_468] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_467,C_468)) ) ),
    inference(resolution,[status(thm)],[c_9955,c_6232])).

tff(c_13575,plain,(
    ! [B_467,C_468] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_467,C_468)) ),
    inference(splitLeft,[status(thm)],[c_9986])).

tff(c_13620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13575,c_13233])).

tff(c_13621,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_9986])).

tff(c_14221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14175,c_13621])).

tff(c_14222,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_10373])).

tff(c_14514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14247,c_14222])).

tff(c_14515,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_9577])).

tff(c_14595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14540,c_14515])).

tff(c_14596,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_9987])).

tff(c_14670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14621,c_14596])).

tff(c_14671,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_9067])).

tff(c_14966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14916,c_14671])).

tff(c_14967,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_8784])).

tff(c_20058,plain,(
    ! [B_668,C_669] :
      ( r2_hidden('#skF_3'('#skF_5',B_668,C_669),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_668,C_669)) ) ),
    inference(resolution,[status(thm)],[c_14967,c_152])).

tff(c_20106,plain,(
    ! [B_668,C_669] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_668,C_669)) ) ),
    inference(resolution,[status(thm)],[c_20058,c_2785])).

tff(c_20646,plain,(
    ! [B_668,C_669] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_668,C_669)) ),
    inference(splitLeft,[status(thm)],[c_20106])).

tff(c_19663,plain,(
    ! [B_661,C_662] :
      ( r2_hidden('#skF_3'('#skF_5',B_661,C_662),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_661,C_662)) ) ),
    inference(resolution,[status(thm)],[c_14596,c_152])).

tff(c_19711,plain,(
    ! [B_661,C_662] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_661,C_662)) ) ),
    inference(resolution,[status(thm)],[c_19663,c_2785])).

tff(c_19720,plain,(
    ! [B_661,C_662] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_661,C_662)) ),
    inference(splitLeft,[status(thm)],[c_19711])).

tff(c_10262,plain,(
    ! [B_474,C_475] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_474,C_475)) ) ),
    inference(resolution,[status(thm)],[c_10231,c_6232])).

tff(c_14999,plain,(
    ! [B_474,C_475] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_474,C_475)) ),
    inference(splitLeft,[status(thm)],[c_10262])).

tff(c_15050,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14999,c_14967])).

tff(c_15051,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_10262])).

tff(c_18997,plain,(
    ! [B_652,C_653] :
      ( r2_hidden('#skF_3'('#skF_5',B_652,C_653),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_652,C_653)) ) ),
    inference(resolution,[status(thm)],[c_15051,c_152])).

tff(c_19042,plain,(
    ! [B_652,C_653] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_652,C_653)) ) ),
    inference(resolution,[status(thm)],[c_18997,c_2785])).

tff(c_19576,plain,(
    ! [B_652,C_653] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_652,C_653)) ),
    inference(splitLeft,[status(thm)],[c_19042])).

tff(c_18622,plain,(
    ! [B_645,C_646] :
      ( r2_hidden('#skF_3'('#skF_5',B_645,C_646),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_645,C_646)) ) ),
    inference(resolution,[status(thm)],[c_14222,c_152])).

tff(c_18667,plain,(
    ! [B_645,C_646] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_645,C_646)) ) ),
    inference(resolution,[status(thm)],[c_18622,c_2785])).

tff(c_18676,plain,(
    ! [B_645,C_646] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_645,C_646)) ),
    inference(splitLeft,[status(thm)],[c_18667])).

tff(c_17967,plain,(
    ! [B_636,C_637] :
      ( r2_hidden('#skF_3'('#skF_5',B_636,C_637),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_636,C_637)) ) ),
    inference(resolution,[status(thm)],[c_14515,c_152])).

tff(c_18009,plain,(
    ! [B_636,C_637] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_636,C_637)) ) ),
    inference(resolution,[status(thm)],[c_17967,c_2785])).

tff(c_18537,plain,(
    ! [B_636,C_637] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_636,C_637)) ),
    inference(splitLeft,[status(thm)],[c_18009])).

tff(c_8785,plain,(
    ! [B_438,C_439] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_438,C_439)) ) ),
    inference(resolution,[status(thm)],[c_8753,c_6231])).

tff(c_15350,plain,(
    ! [B_438,C_439] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_438,C_439)) ),
    inference(splitLeft,[status(thm)],[c_8785])).

tff(c_9879,plain,(
    ! [B_461,C_462] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_461,C_462)) ) ),
    inference(resolution,[status(thm)],[c_9847,c_6231])).

tff(c_15076,plain,(
    ! [B_461,C_462] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_461,C_462)) ),
    inference(splitLeft,[status(thm)],[c_9879])).

tff(c_15128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15076,c_15051])).

tff(c_15129,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_9879])).

tff(c_15403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15350,c_15129])).

tff(c_15404,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_8785])).

tff(c_17605,plain,(
    ! [B_629,C_630] :
      ( r2_hidden('#skF_3'('#skF_5',B_629,C_630),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_629,C_630)) ) ),
    inference(resolution,[status(thm)],[c_15404,c_152])).

tff(c_17647,plain,(
    ! [B_629,C_630] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_629,C_630)) ) ),
    inference(resolution,[status(thm)],[c_17605,c_2785])).

tff(c_17656,plain,(
    ! [B_629,C_630] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_629,C_630)) ),
    inference(splitLeft,[status(thm)],[c_17647])).

tff(c_16961,plain,(
    ! [B_620,C_621] :
      ( r2_hidden('#skF_3'('#skF_5',B_620,C_621),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_620,C_621)) ) ),
    inference(resolution,[status(thm)],[c_13621,c_152])).

tff(c_17000,plain,(
    ! [B_620,C_621] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_620,C_621)) ) ),
    inference(resolution,[status(thm)],[c_16961,c_2785])).

tff(c_17522,plain,(
    ! [B_620,C_621] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_620,C_621)) ),
    inference(splitLeft,[status(thm)],[c_17000])).

tff(c_16395,plain,(
    ! [B_606,C_607] :
      ( r2_hidden('#skF_3'('#skF_5',B_606,C_607),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_606,C_607)) ) ),
    inference(resolution,[status(thm)],[c_12589,c_152])).

tff(c_16434,plain,(
    ! [B_606,C_607] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_606,C_607)) ) ),
    inference(resolution,[status(thm)],[c_16395,c_2785])).

tff(c_16443,plain,(
    ! [B_606,C_607] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_606,C_607)) ),
    inference(splitLeft,[status(thm)],[c_16434])).

tff(c_15778,plain,(
    ! [B_597,C_598] :
      ( r2_hidden('#skF_3'('#skF_5',B_597,C_598),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_597,C_598)) ) ),
    inference(resolution,[status(thm)],[c_14671,c_152])).

tff(c_15814,plain,(
    ! [B_597,C_598] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_597,C_598)) ) ),
    inference(resolution,[status(thm)],[c_15778,c_2785])).

tff(c_15823,plain,(
    ! [B_597,C_598] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_597,C_598)) ),
    inference(splitLeft,[status(thm)],[c_15814])).

tff(c_15436,plain,(
    ! [B_590,C_591] :
      ( r2_hidden('#skF_3'('#skF_5',B_590,C_591),k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_590,C_591)) ) ),
    inference(resolution,[status(thm)],[c_15129,c_152])).

tff(c_15472,plain,(
    ! [B_590,C_591] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_590,C_591)) ) ),
    inference(resolution,[status(thm)],[c_15436,c_2785])).

tff(c_15481,plain,(
    ! [B_590,C_591] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_590,C_591)) ),
    inference(splitLeft,[status(thm)],[c_15472])).

tff(c_15535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15481,c_15404])).

tff(c_15536,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_15472])).

tff(c_15878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15823,c_15536])).

tff(c_15879,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_15814])).

tff(c_16499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16443,c_15879])).

tff(c_16500,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_16434])).

tff(c_17579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17522,c_16500])).

tff(c_17580,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_17000])).

tff(c_17941,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17656,c_17580])).

tff(c_17942,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_17647])).

tff(c_18596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18537,c_17942])).

tff(c_18597,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_18009])).

tff(c_18971,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18676,c_18597])).

tff(c_18972,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_18667])).

tff(c_19637,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19576,c_18972])).

tff(c_19638,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_19042])).

tff(c_20032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19720,c_19638])).

tff(c_20033,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_6'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_19711])).

tff(c_20709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20646,c_20033])).

tff(c_20710,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_8'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_20106])).

tff(c_21110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20795,c_20710])).

tff(c_21111,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_8'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_20786])).

tff(c_21798,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21733,c_21111])).

tff(c_21799,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),'#skF_8'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_21187])).

tff(c_21953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21887,c_21799])).

tff(c_21954,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),'#skF_6'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_21878])).

tff(c_22652,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22585,c_21954])).

tff(c_22653,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),'#skF_6'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_22033])).

tff(c_23079,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22744,c_22653])).

tff(c_23080,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_8'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_22735])).

tff(c_23789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23720,c_23080])).

tff(c_23790,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),'#skF_6'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_23162])).

tff(c_23988,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23917,c_23790])).

tff(c_23989,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_23914])).

tff(c_24535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24014,c_23989])).

tff(c_24536,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_23915])).

tff(c_24732,plain,(
    ! [B_731,C_732] :
      ( r2_hidden('#skF_3'('#skF_5',B_731,C_732),k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_731,C_732)) ) ),
    inference(resolution,[status(thm)],[c_24536,c_152])).

tff(c_24791,plain,(
    ! [B_731,C_732] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_731,C_732)) ) ),
    inference(resolution,[status(thm)],[c_24732,c_6231])).

tff(c_26288,plain,(
    ! [B_731,C_732] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_731,C_732)) ),
    inference(splitLeft,[status(thm)],[c_24791])).

tff(c_24561,plain,(
    ! [B_729,C_730] :
      ( r2_hidden('#skF_3'('#skF_5',B_729,C_730),k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_729,C_730)) ) ),
    inference(resolution,[status(thm)],[c_23989,c_152])).

tff(c_24620,plain,(
    ! [B_729,C_730] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_729,C_730)) ) ),
    inference(resolution,[status(thm)],[c_24561,c_6231])).

tff(c_25729,plain,(
    ! [B_729,C_730] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_729,C_730)) ),
    inference(splitLeft,[status(thm)],[c_24620])).

tff(c_23913,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_6280,c_23815])).

tff(c_25353,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_23913])).

tff(c_24795,plain,(
    ! [B_731,C_732] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_731,C_732)) ) ),
    inference(resolution,[status(thm)],[c_24732,c_2785])).

tff(c_24804,plain,(
    ! [B_731,C_732] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_731,C_732)) ),
    inference(splitLeft,[status(thm)],[c_24795])).

tff(c_24624,plain,(
    ! [B_729,C_730] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_729,C_730)) ) ),
    inference(resolution,[status(thm)],[c_24561,c_2785])).

tff(c_24633,plain,(
    ! [B_729,C_730] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_729,C_730)) ),
    inference(splitLeft,[status(thm)],[c_24624])).

tff(c_24706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24633,c_24536])).

tff(c_24707,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_24624])).

tff(c_25327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24804,c_24707])).

tff(c_25328,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_24795])).

tff(c_25428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25353,c_25328])).

tff(c_25429,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_23913])).

tff(c_25805,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25729,c_25429])).

tff(c_25806,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_24620])).

tff(c_26365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26288,c_25806])).

tff(c_26366,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_24791])).

tff(c_28350,plain,(
    ! [B_773,C_774] :
      ( r2_hidden('#skF_3'('#skF_5',B_773,C_774),k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_773,C_774)) ) ),
    inference(resolution,[status(thm)],[c_26366,c_152])).

tff(c_28409,plain,(
    ! [B_773,C_774] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_773,C_774)) ) ),
    inference(resolution,[status(thm)],[c_28350,c_6231])).

tff(c_32012,plain,(
    ! [B_773,C_774] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_773,C_774)) ),
    inference(splitLeft,[status(thm)],[c_28409])).

tff(c_24790,plain,(
    ! [B_731,C_732] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_731,C_732)) ) ),
    inference(resolution,[status(thm)],[c_24732,c_6232])).

tff(c_26778,plain,(
    ! [B_731,C_732] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_731,C_732)) ),
    inference(splitLeft,[status(thm)],[c_24790])).

tff(c_24619,plain,(
    ! [B_729,C_730] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_729,C_730)) ) ),
    inference(resolution,[status(thm)],[c_24561,c_6232])).

tff(c_26391,plain,(
    ! [B_729,C_730] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_729,C_730)) ),
    inference(splitLeft,[status(thm)],[c_24619])).

tff(c_26469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26391,c_26366])).

tff(c_26470,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_24619])).

tff(c_26857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26778,c_26470])).

tff(c_26858,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_24790])).

tff(c_28996,plain,(
    ! [B_781,C_782] :
      ( r2_hidden('#skF_3'('#skF_5',B_781,C_782),k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_781,C_782)) ) ),
    inference(resolution,[status(thm)],[c_26858,c_152])).

tff(c_29055,plain,(
    ! [B_781,C_782] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_781,C_782)) ) ),
    inference(resolution,[status(thm)],[c_28996,c_6231])).

tff(c_31890,plain,(
    ! [B_781,C_782] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_781,C_782)) ),
    inference(splitLeft,[status(thm)],[c_29055])).

tff(c_6634,plain,(
    ! [A_1,B_384,C_385] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(A_1,k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_384,C_385),A_1)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_384,C_385)) ) ),
    inference(resolution,[status(thm)],[c_6601,c_2835])).

tff(c_24610,plain,(
    ! [B_729,C_730] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_729,C_730)) ) ),
    inference(resolution,[status(thm)],[c_24561,c_6634])).

tff(c_31471,plain,(
    ! [B_729,C_730] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_729,C_730)) ),
    inference(splitLeft,[status(thm)],[c_24610])).

tff(c_24781,plain,(
    ! [B_731,C_732] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_731,C_732)) ) ),
    inference(resolution,[status(thm)],[c_24732,c_6634])).

tff(c_31351,plain,(
    ! [B_731,C_732] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_731,C_732)) ),
    inference(splitLeft,[status(thm)],[c_24781])).

tff(c_27348,plain,(
    ! [B_761,C_762] :
      ( r2_hidden('#skF_3'('#skF_5',B_761,C_762),k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_761,C_762)) ) ),
    inference(resolution,[status(thm)],[c_25429,c_152])).

tff(c_27406,plain,(
    ! [B_761,C_762] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_761,C_762)) ) ),
    inference(resolution,[status(thm)],[c_27348,c_6232])).

tff(c_30934,plain,(
    ! [B_761,C_762] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_761,C_762)) ),
    inference(splitLeft,[status(thm)],[c_27406])).

tff(c_27407,plain,(
    ! [B_761,C_762] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_761,C_762)) ) ),
    inference(resolution,[status(thm)],[c_27348,c_6231])).

tff(c_30816,plain,(
    ! [B_761,C_762] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_761,C_762)) ),
    inference(splitLeft,[status(thm)],[c_27407])).

tff(c_6872,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_3'('#skF_5',B_48,C_49),k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_6861,c_152])).

tff(c_23908,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_6872,c_23815])).

tff(c_30570,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_23908])).

tff(c_7098,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_3'('#skF_5',B_48,C_49),k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_6891,c_152])).

tff(c_23910,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_7098,c_23815])).

tff(c_30454,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_23910])).

tff(c_7129,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_3'('#skF_5',B_48,C_49),k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_7118,c_152])).

tff(c_23907,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_7129,c_23815])).

tff(c_30339,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_23907])).

tff(c_6572,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_3'('#skF_5',B_48,C_49),k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_6546,c_152])).

tff(c_23909,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_6572,c_23815])).

tff(c_29480,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_23909])).

tff(c_29059,plain,(
    ! [B_781,C_782] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_781,C_782)) ) ),
    inference(resolution,[status(thm)],[c_28996,c_2785])).

tff(c_29068,plain,(
    ! [B_781,C_782] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_781,C_782)) ),
    inference(splitLeft,[status(thm)],[c_29059])).

tff(c_28413,plain,(
    ! [B_773,C_774] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_773,C_774)) ) ),
    inference(resolution,[status(thm)],[c_28350,c_2785])).

tff(c_28422,plain,(
    ! [B_773,C_774] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_773,C_774)) ),
    inference(splitLeft,[status(thm)],[c_28413])).

tff(c_28170,plain,(
    ! [B_771,C_772] :
      ( r2_hidden('#skF_3'('#skF_5',B_771,C_772),k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_771,C_772)) ) ),
    inference(resolution,[status(thm)],[c_25806,c_152])).

tff(c_28233,plain,(
    ! [B_771,C_772] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_771,C_772)) ) ),
    inference(resolution,[status(thm)],[c_28170,c_2785])).

tff(c_28242,plain,(
    ! [B_771,C_772] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_771,C_772)) ),
    inference(splitLeft,[status(thm)],[c_28233])).

tff(c_27526,plain,(
    ! [B_763,C_764] :
      ( r2_hidden('#skF_3'('#skF_5',B_763,C_764),k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_763,C_764)) ) ),
    inference(resolution,[status(thm)],[c_26470,c_152])).

tff(c_27589,plain,(
    ! [B_763,C_764] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_763,C_764)) ) ),
    inference(resolution,[status(thm)],[c_27526,c_2785])).

tff(c_27598,plain,(
    ! [B_763,C_764] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_763,C_764)) ),
    inference(splitLeft,[status(thm)],[c_27589])).

tff(c_27411,plain,(
    ! [B_761,C_762] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_761,C_762)) ) ),
    inference(resolution,[status(thm)],[c_27348,c_2785])).

tff(c_27420,plain,(
    ! [B_761,C_762] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_761,C_762)) ),
    inference(splitLeft,[status(thm)],[c_27411])).

tff(c_27500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27420,c_26858])).

tff(c_27501,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_27411])).

tff(c_27679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27598,c_27501])).

tff(c_27680,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_27589])).

tff(c_28324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28242,c_27680])).

tff(c_28325,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_28233])).

tff(c_28505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28422,c_28325])).

tff(c_28506,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_28413])).

tff(c_29152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29068,c_28506])).

tff(c_29153,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_29059])).

tff(c_29565,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29480,c_29153])).

tff(c_29566,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_23909])).

tff(c_30425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30339,c_29566])).

tff(c_30426,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),k3_xboole_0('#skF_6','#skF_8')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_23907])).

tff(c_30541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30454,c_30426])).

tff(c_30542,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),k3_xboole_0('#skF_6','#skF_8')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_23910])).

tff(c_30658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30570,c_30542])).

tff(c_30659,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_23908])).

tff(c_30905,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30816,c_30659])).

tff(c_30906,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_27407])).

tff(c_31322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30934,c_30906])).

tff(c_31323,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_27406])).

tff(c_31442,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31351,c_31323])).

tff(c_31443,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_6','#skF_8')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_24781])).

tff(c_31563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31471,c_31443])).

tff(c_31564,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_6','#skF_8')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_24610])).

tff(c_31983,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31890,c_31564])).

tff(c_31984,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_29055])).

tff(c_32106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32012,c_31984])).

tff(c_32107,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_28409])).

tff(c_44009,plain,(
    ! [B_941,C_942] :
      ( r2_hidden('#skF_3'('#skF_5',B_941,C_942),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_941,C_942)) ) ),
    inference(resolution,[status(thm)],[c_32107,c_152])).

tff(c_44093,plain,(
    ! [B_941,C_942] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_941,C_942)) ) ),
    inference(resolution,[status(thm)],[c_44009,c_2785])).

tff(c_44102,plain,(
    ! [B_941,C_942] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_941,C_942)) ),
    inference(splitLeft,[status(thm)],[c_44093])).

tff(c_27585,plain,(
    ! [B_763,C_764] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_763,C_764)) ) ),
    inference(resolution,[status(thm)],[c_27526,c_6231])).

tff(c_34812,plain,(
    ! [B_763,C_764] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_763,C_764)) ),
    inference(splitLeft,[status(thm)],[c_27585])).

tff(c_29054,plain,(
    ! [B_781,C_782] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_781,C_782)) ) ),
    inference(resolution,[status(thm)],[c_28996,c_6232])).

tff(c_34684,plain,(
    ! [B_781,C_782] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_781,C_782)) ),
    inference(splitLeft,[status(thm)],[c_29054])).

tff(c_28408,plain,(
    ! [B_773,C_774] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_773,C_774)) ) ),
    inference(resolution,[status(thm)],[c_28350,c_6232])).

tff(c_34048,plain,(
    ! [B_773,C_774] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_773,C_774)) ),
    inference(splitLeft,[status(thm)],[c_28408])).

tff(c_27584,plain,(
    ! [B_763,C_764] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_763,C_764)) ) ),
    inference(resolution,[status(thm)],[c_27526,c_6232])).

tff(c_33606,plain,(
    ! [B_763,C_764] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_763,C_764)) ),
    inference(splitLeft,[status(thm)],[c_27584])).

tff(c_28229,plain,(
    ! [B_771,C_772] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_771,C_772)) ) ),
    inference(resolution,[status(thm)],[c_28170,c_6231])).

tff(c_33481,plain,(
    ! [B_771,C_772] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_771,C_772)) ),
    inference(splitLeft,[status(thm)],[c_28229])).

tff(c_28228,plain,(
    ! [B_771,C_772] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_771,C_772)) ) ),
    inference(resolution,[status(thm)],[c_28170,c_6232])).

tff(c_32135,plain,(
    ! [B_771,C_772] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_771,C_772)) ),
    inference(splitLeft,[status(thm)],[c_28228])).

tff(c_32230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32135,c_32107])).

tff(c_32231,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_28228])).

tff(c_33577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33481,c_32231])).

tff(c_33578,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_28229])).

tff(c_33703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33606,c_33578])).

tff(c_33704,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_27584])).

tff(c_34146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34048,c_33704])).

tff(c_34147,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_28408])).

tff(c_34783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34684,c_34147])).

tff(c_34784,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_29054])).

tff(c_34912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34812,c_34784])).

tff(c_34913,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_27585])).

tff(c_42859,plain,(
    ! [B_931,C_932] :
      ( r2_hidden('#skF_3'('#skF_5',B_931,C_932),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_931,C_932)) ) ),
    inference(resolution,[status(thm)],[c_34913,c_152])).

tff(c_42940,plain,(
    ! [B_931,C_932] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_931,C_932)) ) ),
    inference(resolution,[status(thm)],[c_42859,c_2785])).

tff(c_43859,plain,(
    ! [B_931,C_932] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_931,C_932)) ),
    inference(splitLeft,[status(thm)],[c_42940])).

tff(c_42274,plain,(
    ! [B_924,C_925] :
      ( r2_hidden('#skF_3'('#skF_5',B_924,C_925),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_924,C_925)) ) ),
    inference(resolution,[status(thm)],[c_33578,c_152])).

tff(c_42355,plain,(
    ! [B_924,C_925] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_924,C_925)) ) ),
    inference(resolution,[status(thm)],[c_42274,c_2785])).

tff(c_42364,plain,(
    ! [B_924,C_925] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_924,C_925)) ),
    inference(splitLeft,[status(thm)],[c_42355])).

tff(c_41369,plain,(
    ! [B_915,C_916] :
      ( r2_hidden('#skF_3'('#skF_5',B_915,C_916),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_915,C_916)) ) ),
    inference(resolution,[status(thm)],[c_32231,c_152])).

tff(c_41447,plain,(
    ! [B_915,C_916] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_915,C_916)) ) ),
    inference(resolution,[status(thm)],[c_41369,c_2785])).

tff(c_42129,plain,(
    ! [B_915,C_916] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_915,C_916)) ),
    inference(splitLeft,[status(thm)],[c_41447])).

tff(c_40797,plain,(
    ! [B_908,C_909] :
      ( r2_hidden('#skF_3'('#skF_5',B_908,C_909),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_908,C_909)) ) ),
    inference(resolution,[status(thm)],[c_34784,c_152])).

tff(c_40875,plain,(
    ! [B_908,C_909] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_908,C_909)) ) ),
    inference(resolution,[status(thm)],[c_40797,c_2785])).

tff(c_40884,plain,(
    ! [B_908,C_909] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_908,C_909)) ),
    inference(splitLeft,[status(thm)],[c_40875])).

tff(c_39903,plain,(
    ! [B_899,C_900] :
      ( r2_hidden('#skF_3'('#skF_5',B_899,C_900),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_899,C_900)) ) ),
    inference(resolution,[status(thm)],[c_31984,c_152])).

tff(c_39978,plain,(
    ! [B_899,C_900] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_899,C_900)) ) ),
    inference(resolution,[status(thm)],[c_39903,c_2785])).

tff(c_40654,plain,(
    ! [B_899,C_900] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_899,C_900)) ),
    inference(splitLeft,[status(thm)],[c_39978])).

tff(c_39677,plain,(
    ! [B_897,C_898] :
      ( r2_hidden('#skF_3'('#skF_5',B_897,C_898),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_897,C_898)) ) ),
    inference(resolution,[status(thm)],[c_34147,c_152])).

tff(c_39752,plain,(
    ! [B_897,C_898] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_897,C_898)) ) ),
    inference(resolution,[status(thm)],[c_39677,c_2785])).

tff(c_39761,plain,(
    ! [B_897,C_898] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_897,C_898)) ),
    inference(splitLeft,[status(thm)],[c_39752])).

tff(c_38939,plain,(
    ! [B_889,C_890] :
      ( r2_hidden('#skF_3'('#skF_5',B_889,C_890),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_889,C_890)) ) ),
    inference(resolution,[status(thm)],[c_33704,c_152])).

tff(c_39014,plain,(
    ! [B_889,C_890] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_889,C_890)) ) ),
    inference(resolution,[status(thm)],[c_38939,c_2785])).

tff(c_39536,plain,(
    ! [B_889,C_890] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_889,C_890)) ),
    inference(splitLeft,[status(thm)],[c_39014])).

tff(c_38715,plain,(
    ! [B_887,C_888] :
      ( r2_hidden('#skF_3'('#skF_5',B_887,C_888),k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_887,C_888)) ) ),
    inference(resolution,[status(thm)],[c_31443,c_152])).

tff(c_38790,plain,(
    ! [B_887,C_888] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_887,C_888)) ) ),
    inference(resolution,[status(thm)],[c_38715,c_2785])).

tff(c_38799,plain,(
    ! [B_887,C_888] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_887,C_888)) ),
    inference(splitLeft,[status(thm)],[c_38790])).

tff(c_38492,plain,(
    ! [B_885,C_886] :
      ( r2_hidden('#skF_3'('#skF_5',B_885,C_886),k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_885,C_886)) ) ),
    inference(resolution,[status(thm)],[c_31564,c_152])).

tff(c_38567,plain,(
    ! [B_885,C_886] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_885,C_886)) ) ),
    inference(resolution,[status(thm)],[c_38492,c_2785])).

tff(c_38576,plain,(
    ! [B_885,C_886] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_885,C_886)) ),
    inference(splitLeft,[status(thm)],[c_38567])).

tff(c_37945,plain,(
    ! [B_878,C_879] :
      ( r2_hidden('#skF_3'('#skF_5',B_878,C_879),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_878,C_879)) ) ),
    inference(resolution,[status(thm)],[c_31323,c_152])).

tff(c_38020,plain,(
    ! [B_878,C_879] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_878,C_879)) ) ),
    inference(resolution,[status(thm)],[c_37945,c_2785])).

tff(c_38029,plain,(
    ! [B_878,C_879] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_878,C_879)) ),
    inference(splitLeft,[status(thm)],[c_38020])).

tff(c_37584,plain,(
    ! [B_870,C_871] :
      ( r2_hidden('#skF_3'('#skF_5',B_870,C_871),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_870,C_871)) ) ),
    inference(resolution,[status(thm)],[c_30906,c_152])).

tff(c_37659,plain,(
    ! [B_870,C_871] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_870,C_871)) ) ),
    inference(resolution,[status(thm)],[c_37584,c_2785])).

tff(c_37808,plain,(
    ! [B_870,C_871] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_870,C_871)) ),
    inference(splitLeft,[status(thm)],[c_37659])).

tff(c_37364,plain,(
    ! [B_868,C_869] :
      ( r2_hidden('#skF_3'('#skF_5',B_868,C_869),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_868,C_869)) ) ),
    inference(resolution,[status(thm)],[c_30659,c_152])).

tff(c_37439,plain,(
    ! [B_868,C_869] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_868,C_869)) ) ),
    inference(resolution,[status(thm)],[c_37364,c_2785])).

tff(c_37448,plain,(
    ! [B_868,C_869] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_868,C_869)) ),
    inference(splitLeft,[status(thm)],[c_37439])).

tff(c_36313,plain,(
    ! [B_858,C_859] :
      ( r2_hidden('#skF_3'('#skF_5',B_858,C_859),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_858,C_859)) ) ),
    inference(resolution,[status(thm)],[c_30542,c_152])).

tff(c_36385,plain,(
    ! [B_858,C_859] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_858,C_859)) ) ),
    inference(resolution,[status(thm)],[c_36313,c_2785])).

tff(c_37229,plain,(
    ! [B_858,C_859] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_858,C_859)) ),
    inference(splitLeft,[status(thm)],[c_36385])).

tff(c_35782,plain,(
    ! [B_851,C_852] :
      ( r2_hidden('#skF_3'('#skF_5',B_851,C_852),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_851,C_852)) ) ),
    inference(resolution,[status(thm)],[c_30426,c_152])).

tff(c_35854,plain,(
    ! [B_851,C_852] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_851,C_852)) ) ),
    inference(resolution,[status(thm)],[c_35782,c_2785])).

tff(c_35863,plain,(
    ! [B_851,C_852] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_851,C_852)) ),
    inference(splitLeft,[status(thm)],[c_35854])).

tff(c_34941,plain,(
    ! [B_842,C_843] :
      ( r2_hidden('#skF_3'('#skF_5',B_842,C_843),k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),k3_xboole_0('#skF_6','#skF_8')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_842,C_843)) ) ),
    inference(resolution,[status(thm)],[c_29566,c_152])).

tff(c_35010,plain,(
    ! [B_842,C_843] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_842,C_843)) ) ),
    inference(resolution,[status(thm)],[c_34941,c_2785])).

tff(c_35652,plain,(
    ! [B_842,C_843] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_842,C_843)) ),
    inference(splitLeft,[status(thm)],[c_35010])).

tff(c_35753,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35652,c_34913])).

tff(c_35754,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_35010])).

tff(c_36284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35863,c_35754])).

tff(c_36285,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_35854])).

tff(c_37332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37229,c_36285])).

tff(c_37333,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_36385])).

tff(c_37552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37448,c_37333])).

tff(c_37553,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_37439])).

tff(c_37913,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37808,c_37553])).

tff(c_37914,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_37659])).

tff(c_38460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38029,c_37914])).

tff(c_38461,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_38020])).

tff(c_38683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38576,c_38461])).

tff(c_38684,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_38567])).

tff(c_38907,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38799,c_38684])).

tff(c_38908,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),k3_xboole_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_38790])).

tff(c_39645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39536,c_38908])).

tff(c_39646,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_39014])).

tff(c_39871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39761,c_39646])).

tff(c_39872,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_39752])).

tff(c_40765,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40654,c_39872])).

tff(c_40766,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_39978])).

tff(c_41337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40884,c_40766])).

tff(c_41338,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_40875])).

tff(c_42242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42129,c_41338])).

tff(c_42243,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_41447])).

tff(c_42827,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42364,c_42243])).

tff(c_42828,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_42355])).

tff(c_43974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43859,c_42828])).

tff(c_43975,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_6','#skF_8')),'#skF_8'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_42940])).

tff(c_44218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44102,c_43975])).

tff(c_44219,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_6','#skF_8')),'#skF_6'),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_44093])).

tff(c_44700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44582,c_44219])).

tff(c_44701,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_44421])).

tff(c_45244,plain,(
    ! [B_957,C_958] :
      ( r2_hidden('#skF_3'('#skF_5',B_957,C_958),k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_957,C_958)) ) ),
    inference(resolution,[status(thm)],[c_44701,c_152])).

tff(c_6312,plain,(
    ! [A_1,B_374,C_375] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(A_1,k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_3'('#skF_5',B_374,C_375),A_1)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_374,C_375)) ) ),
    inference(resolution,[status(thm)],[c_6282,c_2835])).

tff(c_45309,plain,(
    ! [B_957,C_958] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_957,C_958)) ) ),
    inference(resolution,[status(thm)],[c_45244,c_6312])).

tff(c_52820,plain,(
    ! [B_957,C_958] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_957,C_958)) ),
    inference(splitLeft,[status(thm)],[c_45309])).

tff(c_44415,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_6872,c_44253])).

tff(c_52432,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_44415])).

tff(c_44414,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_7129,c_44253])).

tff(c_51266,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_44414])).

tff(c_44417,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_7098,c_44253])).

tff(c_50880,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_44417])).

tff(c_44416,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_6572,c_44253])).

tff(c_50713,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_44416])).

tff(c_44422,plain,(
    ! [B_74,C_76] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_74,C_76)) ) ),
    inference(resolution,[status(thm)],[c_309,c_44253])).

tff(c_44735,plain,(
    ! [B_74,C_76] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_74,C_76)) ),
    inference(splitLeft,[status(thm)],[c_44422])).

tff(c_44854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44735,c_44701])).

tff(c_44855,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_44422])).

tff(c_45495,plain,(
    ! [B_959,C_960] :
      ( r2_hidden('#skF_3'('#skF_5',B_959,C_960),k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_959,C_960)) ) ),
    inference(resolution,[status(thm)],[c_44855,c_152])).

tff(c_45577,plain,(
    ! [B_959,C_960] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_959,C_960)) ) ),
    inference(resolution,[status(thm)],[c_45495,c_6232])).

tff(c_46906,plain,(
    ! [B_959,C_960] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_959,C_960)) ),
    inference(splitLeft,[status(thm)],[c_45577])).

tff(c_45327,plain,(
    ! [B_957,C_958] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_957,C_958)) ) ),
    inference(resolution,[status(thm)],[c_45244,c_6231])).

tff(c_46221,plain,(
    ! [B_957,C_958] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_957,C_958)) ),
    inference(splitLeft,[status(thm)],[c_45327])).

tff(c_45326,plain,(
    ! [B_957,C_958] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_957,C_958)) ) ),
    inference(resolution,[status(thm)],[c_45244,c_6232])).

tff(c_46062,plain,(
    ! [B_957,C_958] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_957,C_958)) ),
    inference(splitLeft,[status(thm)],[c_45326])).

tff(c_45578,plain,(
    ! [B_959,C_960] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_959,C_960)) ) ),
    inference(resolution,[status(thm)],[c_45495,c_6231])).

tff(c_45904,plain,(
    ! [B_959,C_960] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_959,C_960)) ),
    inference(splitLeft,[status(thm)],[c_45578])).

tff(c_44418,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_6599,c_44253])).

tff(c_45747,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_44418])).

tff(c_45582,plain,(
    ! [B_959,C_960] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_959,C_960)) ) ),
    inference(resolution,[status(thm)],[c_45495,c_2785])).

tff(c_45591,plain,(
    ! [B_959,C_960] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_959,C_960)) ),
    inference(splitLeft,[status(thm)],[c_45582])).

tff(c_45331,plain,(
    ! [B_957,C_958] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_957,C_958)) ) ),
    inference(resolution,[status(thm)],[c_45244,c_2785])).

tff(c_45340,plain,(
    ! [B_957,C_958] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_957,C_958)) ),
    inference(splitLeft,[status(thm)],[c_45331])).

tff(c_45460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45340,c_44855])).

tff(c_45461,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_45331])).

tff(c_45712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45591,c_45461])).

tff(c_45713,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_45582])).

tff(c_45869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45747,c_45713])).

tff(c_45870,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_44418])).

tff(c_46027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45904,c_45870])).

tff(c_46028,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_45578])).

tff(c_46186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46062,c_46028])).

tff(c_46187,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_45326])).

tff(c_46871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46221,c_46187])).

tff(c_46872,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_45327])).

tff(c_47032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46906,c_46872])).

tff(c_47033,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_45577])).

tff(c_49920,plain,(
    ! [B_994,C_995] :
      ( r2_hidden('#skF_3'('#skF_5',B_994,C_995),k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_994,C_995)) ) ),
    inference(resolution,[status(thm)],[c_47033,c_152])).

tff(c_50013,plain,(
    ! [B_994,C_995] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_994,C_995)) ) ),
    inference(resolution,[status(thm)],[c_49920,c_2785])).

tff(c_50022,plain,(
    ! [B_994,C_995] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_994,C_995)) ),
    inference(splitLeft,[status(thm)],[c_50013])).

tff(c_49509,plain,(
    ! [B_990,C_991] :
      ( r2_hidden('#skF_3'('#skF_5',B_990,C_991),k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_990,C_991)) ) ),
    inference(resolution,[status(thm)],[c_46028,c_152])).

tff(c_49602,plain,(
    ! [B_990,C_991] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_990,C_991)) ) ),
    inference(resolution,[status(thm)],[c_49509,c_2785])).

tff(c_49611,plain,(
    ! [B_990,C_991] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_990,C_991)) ),
    inference(splitLeft,[status(thm)],[c_49602])).

tff(c_48537,plain,(
    ! [B_981,C_982] :
      ( r2_hidden('#skF_3'('#skF_5',B_981,C_982),k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_981,C_982)) ) ),
    inference(resolution,[status(thm)],[c_46187,c_152])).

tff(c_48627,plain,(
    ! [B_981,C_982] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_981,C_982)) ) ),
    inference(resolution,[status(thm)],[c_48537,c_2785])).

tff(c_48636,plain,(
    ! [B_981,C_982] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_981,C_982)) ),
    inference(splitLeft,[status(thm)],[c_48627])).

tff(c_48028,plain,(
    ! [B_976,C_977] :
      ( r2_hidden('#skF_3'('#skF_5',B_976,C_977),k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_976,C_977)) ) ),
    inference(resolution,[status(thm)],[c_46872,c_152])).

tff(c_48118,plain,(
    ! [B_976,C_977] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_976,C_977)) ) ),
    inference(resolution,[status(thm)],[c_48028,c_2785])).

tff(c_48127,plain,(
    ! [B_976,C_977] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_976,C_977)) ),
    inference(splitLeft,[status(thm)],[c_48118])).

tff(c_47067,plain,(
    ! [B_967,C_968] :
      ( r2_hidden('#skF_3'('#skF_5',B_967,C_968),k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_967,C_968)) ) ),
    inference(resolution,[status(thm)],[c_45870,c_152])).

tff(c_47154,plain,(
    ! [B_967,C_968] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_967,C_968)) ) ),
    inference(resolution,[status(thm)],[c_47067,c_2785])).

tff(c_47163,plain,(
    ! [B_967,C_968] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_967,C_968)) ),
    inference(splitLeft,[status(thm)],[c_47154])).

tff(c_47290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47163,c_47033])).

tff(c_47291,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_47154])).

tff(c_48255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48127,c_47291])).

tff(c_48256,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_48118])).

tff(c_48765,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48636,c_48256])).

tff(c_48766,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_48627])).

tff(c_49741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49611,c_48766])).

tff(c_49742,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_6'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_49602])).

tff(c_50153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50022,c_49742])).

tff(c_50154,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_6')),'#skF_8'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_50013])).

tff(c_50845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50713,c_50154])).

tff(c_50846,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_6'),k3_xboole_0('#skF_8','#skF_6')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_44416])).

tff(c_51231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50880,c_50846])).

tff(c_51232,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8','#skF_6'),'#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_44417])).

tff(c_52397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51266,c_51232])).

tff(c_52398,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_8'),k3_xboole_0('#skF_8','#skF_6')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_44414])).

tff(c_52567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52432,c_52398])).

tff(c_52568,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6','#skF_8'),'#skF_6'),k3_xboole_0('#skF_8','#skF_6')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_44415])).

tff(c_52956,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52820,c_52568])).

tff(c_52957,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6',k3_xboole_0('#skF_8','#skF_6')),k3_xboole_0('#skF_8','#skF_6')),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_45309])).

tff(c_53153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53014,c_52957])).

tff(c_53154,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0('#skF_9','#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_53012])).

tff(c_155,plain,(
    ! [A_47,C_16,D_17,C_49,B_48] :
      ( r2_hidden('#skF_4'(A_47,B_48,C_49),D_17)
      | ~ r2_hidden(A_47,k2_zfmisc_1(C_16,D_17))
      | ~ r2_hidden(A_47,k2_zfmisc_1(B_48,C_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_26])).

tff(c_53188,plain,(
    ! [B_1029,C_1030] :
      ( r2_hidden('#skF_4'('#skF_5',B_1029,C_1030),k3_xboole_0('#skF_9','#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1029,C_1030)) ) ),
    inference(resolution,[status(thm)],[c_53154,c_155])).

tff(c_52999,plain,(
    ! [A_1022,B_65,C_67] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(A_1022,'#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_5',B_65,C_67),A_1022)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_65,C_67)) ) ),
    inference(resolution,[status(thm)],[c_274,c_52991])).

tff(c_53247,plain,(
    ! [B_1029,C_1030] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1029,C_1030)) ) ),
    inference(resolution,[status(thm)],[c_53188,c_52999])).

tff(c_53409,plain,(
    ! [B_1029,C_1030] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1029,C_1030)) ),
    inference(splitLeft,[status(thm)],[c_53247])).

tff(c_53549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53409,c_53154])).

tff(c_53550,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_53247])).

tff(c_53741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53599,c_53550])).

tff(c_53742,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0('#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_53595])).

tff(c_53776,plain,(
    ! [B_1038,C_1039] :
      ( r2_hidden('#skF_4'('#skF_5',B_1038,C_1039),k3_xboole_0('#skF_7','#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1038,C_1039)) ) ),
    inference(resolution,[status(thm)],[c_53742,c_155])).

tff(c_149,plain,(
    ! [A_47,C_16,D_17,C_49,B_48] :
      ( r2_hidden(A_47,k2_zfmisc_1(C_16,D_17))
      | ~ r2_hidden('#skF_4'(A_47,B_48,C_49),D_17)
      | ~ r2_hidden('#skF_3'(A_47,B_48,C_49),C_16)
      | ~ r2_hidden(A_47,k2_zfmisc_1(B_48,C_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_24])).

tff(c_63758,plain,(
    ! [C_1169,B_1170,C_1171] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(C_1169,k3_xboole_0('#skF_7','#skF_9')))
      | ~ r2_hidden('#skF_3'('#skF_5',B_1170,C_1171),C_1169)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1170,C_1171)) ) ),
    inference(resolution,[status(thm)],[c_53776,c_149])).

tff(c_63876,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1(k3_xboole_0('#skF_6','#skF_8'),k3_xboole_0('#skF_7','#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_6599,c_63758])).

tff(c_63946,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_63876])).

tff(c_53187,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_4'('#skF_5',B_48,C_49),k3_xboole_0('#skF_9','#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_53154,c_155])).

tff(c_53594,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_53187,c_53584])).

tff(c_53866,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_53594])).

tff(c_54143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53866,c_53742])).

tff(c_54144,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_53594])).

tff(c_54177,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_4'('#skF_5',B_48,C_49),k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_54144,c_155])).

tff(c_54959,plain,(
    ! [A_1058,B_1059,B_1060,C_1061] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(A_1058,B_1059)))
      | ~ r2_hidden('#skF_4'('#skF_5',B_1060,C_1061),B_1059)
      | ~ r2_hidden('#skF_4'('#skF_5',B_1060,C_1061),A_1058)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1060,C_1061)) ) ),
    inference(resolution,[status(thm)],[c_309,c_52602])).

tff(c_56840,plain,(
    ! [A_1073,B_1074,C_1075] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(A_1073,'#skF_9')))
      | ~ r2_hidden('#skF_4'('#skF_5',B_1074,C_1075),A_1073)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1074,C_1075)) ) ),
    inference(resolution,[status(thm)],[c_273,c_54959])).

tff(c_56860,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_54177,c_56840])).

tff(c_60710,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_56860])).

tff(c_53838,plain,(
    ! [B_1038,C_1039] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1038,C_1039)) ) ),
    inference(resolution,[status(thm)],[c_53776,c_52999])).

tff(c_54375,plain,(
    ! [B_1038,C_1039] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1038,C_1039)) ),
    inference(splitLeft,[status(thm)],[c_53838])).

tff(c_53000,plain,(
    ! [A_1022,B_65,C_67] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(A_1022,'#skF_9')))
      | ~ r2_hidden('#skF_4'('#skF_5',B_65,C_67),A_1022)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_65,C_67)) ) ),
    inference(resolution,[status(thm)],[c_273,c_52991])).

tff(c_53837,plain,(
    ! [B_1038,C_1039] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1038,C_1039)) ) ),
    inference(resolution,[status(thm)],[c_53776,c_53000])).

tff(c_54178,plain,(
    ! [B_1038,C_1039] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1038,C_1039)) ),
    inference(splitLeft,[status(thm)],[c_53837])).

tff(c_54340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54178,c_54144])).

tff(c_54341,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_53837])).

tff(c_54520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54375,c_54341])).

tff(c_54521,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_53838])).

tff(c_54554,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_4'('#skF_5',B_48,C_49),k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_54521,c_155])).

tff(c_56029,plain,(
    ! [A_1067,B_1068,C_1069] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(A_1067,'#skF_7')))
      | ~ r2_hidden('#skF_4'('#skF_5',B_1068,C_1069),A_1067)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1068,C_1069)) ) ),
    inference(resolution,[status(thm)],[c_274,c_54959])).

tff(c_56051,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_54554,c_56029])).

tff(c_60155,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_56051])).

tff(c_54374,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_4'('#skF_5',B_48,C_49),k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_54341,c_155])).

tff(c_56050,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_54374,c_56029])).

tff(c_59786,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_56050])).

tff(c_56049,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_54177,c_56029])).

tff(c_59583,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_56049])).

tff(c_54985,plain,(
    ! [B_1062,C_1063] :
      ( r2_hidden('#skF_4'('#skF_5',B_1062,C_1063),k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1062,C_1063)) ) ),
    inference(resolution,[status(thm)],[c_54144,c_155])).

tff(c_55049,plain,(
    ! [B_1062,C_1063] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1062,C_1063)) ) ),
    inference(resolution,[status(thm)],[c_54985,c_53000])).

tff(c_59216,plain,(
    ! [B_1062,C_1063] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1062,C_1063)) ),
    inference(splitLeft,[status(thm)],[c_55049])).

tff(c_56861,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_54374,c_56840])).

tff(c_59016,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_56861])).

tff(c_53583,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_4'('#skF_5',B_48,C_49),k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_53550,c_155])).

tff(c_56863,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_53583,c_56840])).

tff(c_58808,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_56863])).

tff(c_55050,plain,(
    ! [B_1062,C_1063] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1062,C_1063)) ) ),
    inference(resolution,[status(thm)],[c_54985,c_52999])).

tff(c_58444,plain,(
    ! [B_1062,C_1063] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1062,C_1063)) ),
    inference(splitLeft,[status(thm)],[c_55050])).

tff(c_56862,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_54554,c_56840])).

tff(c_58247,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_56862])).

tff(c_54689,plain,(
    ! [B_1052,C_1053] :
      ( r2_hidden('#skF_4'('#skF_5',B_1052,C_1053),k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1052,C_1053)) ) ),
    inference(resolution,[status(thm)],[c_53550,c_155])).

tff(c_54751,plain,(
    ! [B_1052,C_1053] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1052,C_1053)) ) ),
    inference(resolution,[status(thm)],[c_54689,c_52999])).

tff(c_58030,plain,(
    ! [B_1052,C_1053] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1052,C_1053)) ),
    inference(splitLeft,[status(thm)],[c_54751])).

tff(c_56052,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_53583,c_56029])).

tff(c_57669,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_56052])).

tff(c_56865,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_53187,c_56840])).

tff(c_57454,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_56865])).

tff(c_53775,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_4'('#skF_5',B_48,C_49),k3_xboole_0('#skF_7','#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_53742,c_155])).

tff(c_56864,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_53775,c_56840])).

tff(c_57095,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_56864])).

tff(c_56866,plain,(
    ! [B_65,C_67] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0('#skF_7','#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_65,C_67)) ) ),
    inference(resolution,[status(thm)],[c_274,c_56840])).

tff(c_56903,plain,(
    ! [B_65,C_67] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_65,C_67)) ),
    inference(splitLeft,[status(thm)],[c_56866])).

tff(c_56054,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_53187,c_56029])).

tff(c_56683,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_56054])).

tff(c_56053,plain,(
    ! [B_48,C_49] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_53775,c_56029])).

tff(c_56247,plain,(
    ! [B_48,C_49] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(splitLeft,[status(thm)],[c_56053])).

tff(c_56057,plain,(
    ! [B_65,C_67] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0('#skF_9','#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_65,C_67)) ) ),
    inference(resolution,[status(thm)],[c_273,c_56029])).

tff(c_56059,plain,(
    ! [B_65,C_67] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_65,C_67)) ),
    inference(splitLeft,[status(thm)],[c_56057])).

tff(c_54779,plain,(
    ! [B_1054,C_1055] :
      ( r2_hidden('#skF_4'('#skF_5',B_1054,C_1055),k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1054,C_1055)) ) ),
    inference(resolution,[status(thm)],[c_54521,c_155])).

tff(c_54840,plain,(
    ! [B_1054,C_1055] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1054,C_1055)) ) ),
    inference(resolution,[status(thm)],[c_54779,c_53000])).

tff(c_55843,plain,(
    ! [B_1054,C_1055] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1054,C_1055)) ),
    inference(splitLeft,[status(thm)],[c_54840])).

tff(c_54841,plain,(
    ! [B_1054,C_1055] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1054,C_1055)) ) ),
    inference(resolution,[status(thm)],[c_54779,c_52999])).

tff(c_55658,plain,(
    ! [B_1054,C_1055] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1054,C_1055)) ),
    inference(splitLeft,[status(thm)],[c_54841])).

tff(c_54869,plain,(
    ! [B_1056,C_1057] :
      ( r2_hidden('#skF_4'('#skF_5',B_1056,C_1057),k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1056,C_1057)) ) ),
    inference(resolution,[status(thm)],[c_54341,c_155])).

tff(c_54930,plain,(
    ! [B_1056,C_1057] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1056,C_1057)) ) ),
    inference(resolution,[status(thm)],[c_54869,c_53000])).

tff(c_55443,plain,(
    ! [B_1056,C_1057] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1056,C_1057)) ),
    inference(splitLeft,[status(thm)],[c_54930])).

tff(c_54931,plain,(
    ! [B_1056,C_1057] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'),'#skF_7')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1056,C_1057)) ) ),
    inference(resolution,[status(thm)],[c_54869,c_52999])).

tff(c_55260,plain,(
    ! [B_1056,C_1057] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1056,C_1057)) ),
    inference(splitLeft,[status(thm)],[c_54931])).

tff(c_54750,plain,(
    ! [B_1052,C_1053] :
      ( r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'),'#skF_9')))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1052,C_1053)) ) ),
    inference(resolution,[status(thm)],[c_54689,c_53000])).

tff(c_55078,plain,(
    ! [B_1052,C_1053] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_1052,C_1053)) ),
    inference(splitLeft,[status(thm)],[c_54750])).

tff(c_55225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55078,c_54521])).

tff(c_55226,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_54750])).

tff(c_55408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55260,c_55226])).

tff(c_55409,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_54931])).

tff(c_55623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55443,c_55409])).

tff(c_55624,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_54930])).

tff(c_55808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55658,c_55624])).

tff(c_55809,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_54841])).

tff(c_55994,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55843,c_55809])).

tff(c_55995,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_54840])).

tff(c_56212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56059,c_55995])).

tff(c_56213,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0('#skF_9','#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_56057])).

tff(c_56401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56247,c_56213])).

tff(c_56402,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_56053])).

tff(c_56838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56683,c_56402])).

tff(c_56839,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_56054])).

tff(c_57060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56903,c_56839])).

tff(c_57061,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0('#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_56866])).

tff(c_57419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57095,c_57061])).

tff(c_57420,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_56864])).

tff(c_57634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57454,c_57420])).

tff(c_57635,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_56865])).

tff(c_57829,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57669,c_57635])).

tff(c_57830,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_56052])).

tff(c_58191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58030,c_57830])).

tff(c_58192,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_54751])).

tff(c_58409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58247,c_58192])).

tff(c_58410,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_56862])).

tff(c_58607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58444,c_58410])).

tff(c_58608,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_55050])).

tff(c_58972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58808,c_58608])).

tff(c_58973,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_7'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_56863])).

tff(c_59181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59016,c_58973])).

tff(c_59182,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_56861])).

tff(c_59548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59216,c_59182])).

tff(c_59549,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_6',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_55049])).

tff(c_59751,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59583,c_59549])).

tff(c_59752,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_56049])).

tff(c_59954,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59786,c_59752])).

tff(c_59955,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_9'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_56050])).

tff(c_60324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60155,c_59955])).

tff(c_60325,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7','#skF_9'),'#skF_7'),'#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_56051])).

tff(c_61046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60710,c_60325])).

tff(c_61047,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1('#skF_8',k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9','#skF_7'),'#skF_9'),'#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_56860])).

tff(c_64124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63946,c_61047])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.80/15.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.34/15.99  
% 27.34/15.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.34/15.99  %$ r2_hidden > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 27.34/15.99  
% 27.34/15.99  %Foreground sorts:
% 27.34/15.99  
% 27.34/15.99  
% 27.34/15.99  %Background operators:
% 27.34/15.99  
% 27.34/15.99  
% 27.34/15.99  %Foreground operators:
% 27.34/15.99  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 27.34/15.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.34/15.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 27.34/15.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 27.34/15.99  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 27.34/15.99  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 27.34/15.99  tff('#skF_7', type, '#skF_7': $i).
% 27.34/15.99  tff('#skF_5', type, '#skF_5': $i).
% 27.34/15.99  tff('#skF_6', type, '#skF_6': $i).
% 27.34/15.99  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 27.34/15.99  tff('#skF_9', type, '#skF_9': $i).
% 27.34/15.99  tff('#skF_8', type, '#skF_8': $i).
% 27.34/15.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.34/15.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 27.34/15.99  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 27.34/15.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.34/15.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 27.34/15.99  
% 27.34/16.05  tff(f_56, negated_conjecture, ~(![A, B, C, D, E]: ((r2_hidden(A, k2_zfmisc_1(B, C)) & r2_hidden(A, k2_zfmisc_1(D, E))) => r2_hidden(A, k2_zfmisc_1(k3_xboole_0(B, D), k3_xboole_0(C, E))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_zfmisc_1)).
% 27.34/16.05  tff(f_43, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 27.34/16.05  tff(f_49, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 27.34/16.05  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 27.34/16.05  tff(c_30, plain, (~r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_7', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 27.34/16.05  tff(c_34, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 27.34/16.05  tff(c_143, plain, (![A_47, B_48, C_49]: (k4_tarski('#skF_3'(A_47, B_48, C_49), '#skF_4'(A_47, B_48, C_49))=A_47 | ~r2_hidden(A_47, k2_zfmisc_1(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 27.34/16.05  tff(c_28, plain, (![A_14, C_16, B_15, D_17]: (r2_hidden(A_14, C_16) | ~r2_hidden(k4_tarski(A_14, B_15), k2_zfmisc_1(C_16, D_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 27.34/16.05  tff(c_277, plain, (![D_73, C_75, B_74, A_72, C_76]: (r2_hidden('#skF_3'(A_72, B_74, C_76), C_75) | ~r2_hidden(A_72, k2_zfmisc_1(C_75, D_73)) | ~r2_hidden(A_72, k2_zfmisc_1(B_74, C_76)))), inference(superposition, [status(thm), theory('equality')], [c_143, c_28])).
% 27.34/16.05  tff(c_310, plain, (![B_74, C_76]: (r2_hidden('#skF_3'('#skF_5', B_74, C_76), '#skF_6') | ~r2_hidden('#skF_5', k2_zfmisc_1(B_74, C_76)))), inference(resolution, [status(thm)], [c_34, c_277])).
% 27.34/16.05  tff(c_32, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 27.34/16.05  tff(c_309, plain, (![B_74, C_76]: (r2_hidden('#skF_3'('#skF_5', B_74, C_76), '#skF_8') | ~r2_hidden('#skF_5', k2_zfmisc_1(B_74, C_76)))), inference(resolution, [status(thm)], [c_32, c_277])).
% 27.34/16.05  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 27.34/16.05  tff(c_26, plain, (![B_15, D_17, A_14, C_16]: (r2_hidden(B_15, D_17) | ~r2_hidden(k4_tarski(A_14, B_15), k2_zfmisc_1(C_16, D_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 27.34/16.05  tff(c_241, plain, (![C_67, D_64, A_63, C_66, B_65]: (r2_hidden('#skF_4'(A_63, B_65, C_67), D_64) | ~r2_hidden(A_63, k2_zfmisc_1(C_66, D_64)) | ~r2_hidden(A_63, k2_zfmisc_1(B_65, C_67)))), inference(superposition, [status(thm), theory('equality')], [c_143, c_26])).
% 27.34/16.05  tff(c_273, plain, (![B_65, C_67]: (r2_hidden('#skF_4'('#skF_5', B_65, C_67), '#skF_9') | ~r2_hidden('#skF_5', k2_zfmisc_1(B_65, C_67)))), inference(resolution, [status(thm)], [c_32, c_241])).
% 27.34/16.05  tff(c_24, plain, (![A_14, B_15, C_16, D_17]: (r2_hidden(k4_tarski(A_14, B_15), k2_zfmisc_1(C_16, D_17)) | ~r2_hidden(B_15, D_17) | ~r2_hidden(A_14, C_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 27.34/16.05  tff(c_2774, plain, (![B_211, A_209, D_210, C_213, C_212]: (r2_hidden(A_209, k2_zfmisc_1(C_212, D_210)) | ~r2_hidden('#skF_4'(A_209, B_211, C_213), D_210) | ~r2_hidden('#skF_3'(A_209, B_211, C_213), C_212) | ~r2_hidden(A_209, k2_zfmisc_1(B_211, C_213)))), inference(superposition, [status(thm), theory('equality')], [c_143, c_24])).
% 27.34/16.05  tff(c_2821, plain, (![C_217, B_218, C_219]: (r2_hidden('#skF_5', k2_zfmisc_1(C_217, '#skF_9')) | ~r2_hidden('#skF_3'('#skF_5', B_218, C_219), C_217) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_218, C_219)))), inference(resolution, [status(thm)], [c_273, c_2774])).
% 27.34/16.05  tff(c_6223, plain, (![A_364, B_365, B_366, C_367]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(A_364, B_365), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_366, C_367)) | ~r2_hidden('#skF_3'('#skF_5', B_366, C_367), B_365) | ~r2_hidden('#skF_3'('#skF_5', B_366, C_367), A_364))), inference(resolution, [status(thm)], [c_2, c_2821])).
% 27.34/16.05  tff(c_6547, plain, (![A_381, B_382, C_383]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(A_381, '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_3'('#skF_5', B_382, C_383), A_381) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_382, C_383)))), inference(resolution, [status(thm)], [c_309, c_6223])).
% 27.34/16.05  tff(c_6558, plain, (![B_74, C_76]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_74, C_76)))), inference(resolution, [status(thm)], [c_310, c_6547])).
% 27.34/16.05  tff(c_6574, plain, (![B_74, C_76]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_74, C_76)))), inference(splitLeft, [status(thm)], [c_6558])).
% 27.34/16.05  tff(c_6234, plain, (![A_368, B_369, C_370]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(A_368, '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_3'('#skF_5', B_369, C_370), A_368) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_369, C_370)))), inference(resolution, [status(thm)], [c_310, c_6223])).
% 27.34/16.05  tff(c_6244, plain, (![B_74, C_76]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_74, C_76)))), inference(resolution, [status(thm)], [c_309, c_6234])).
% 27.34/16.05  tff(c_6246, plain, (![B_74, C_76]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_74, C_76)))), inference(splitLeft, [status(thm)], [c_6244])).
% 27.34/16.05  tff(c_2832, plain, (![B_74, C_76]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_74, C_76)))), inference(resolution, [status(thm)], [c_310, c_2821])).
% 27.34/16.05  tff(c_2836, plain, (![B_74, C_76]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_74, C_76)))), inference(splitLeft, [status(thm)], [c_2832])).
% 27.34/16.05  tff(c_274, plain, (![B_65, C_67]: (r2_hidden('#skF_4'('#skF_5', B_65, C_67), '#skF_7') | ~r2_hidden('#skF_5', k2_zfmisc_1(B_65, C_67)))), inference(resolution, [status(thm)], [c_34, c_241])).
% 27.34/16.05  tff(c_2788, plain, (![C_214, B_215, C_216]: (r2_hidden('#skF_5', k2_zfmisc_1(C_214, '#skF_7')) | ~r2_hidden('#skF_3'('#skF_5', B_215, C_216), C_214) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_215, C_216)))), inference(resolution, [status(thm)], [c_274, c_2774])).
% 27.34/16.05  tff(c_2801, plain, (![B_74, C_76]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_74, C_76)))), inference(resolution, [status(thm)], [c_309, c_2788])).
% 27.34/16.05  tff(c_2803, plain, (![B_74, C_76]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_74, C_76)))), inference(splitLeft, [status(thm)], [c_2801])).
% 27.34/16.05  tff(c_2807, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2803, c_32])).
% 27.34/16.05  tff(c_2808, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_2801])).
% 27.34/16.05  tff(c_2842, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2836, c_2808])).
% 27.34/16.05  tff(c_2843, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', '#skF_9'))), inference(splitRight, [status(thm)], [c_2832])).
% 27.34/16.05  tff(c_6268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6246, c_2843])).
% 27.34/16.05  tff(c_6269, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_6244])).
% 27.34/16.05  tff(c_152, plain, (![A_47, C_16, D_17, C_49, B_48]: (r2_hidden('#skF_3'(A_47, B_48, C_49), C_16) | ~r2_hidden(A_47, k2_zfmisc_1(C_16, D_17)) | ~r2_hidden(A_47, k2_zfmisc_1(B_48, C_49)))), inference(superposition, [status(thm), theory('equality')], [c_143, c_28])).
% 27.34/16.05  tff(c_6282, plain, (![B_374, C_375]: (r2_hidden('#skF_3'('#skF_5', B_374, C_375), k3_xboole_0('#skF_8', '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_374, C_375)))), inference(resolution, [status(thm)], [c_6269, c_152])).
% 27.34/16.05  tff(c_6231, plain, (![A_364, B_74, C_76]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(A_364, '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_3'('#skF_5', B_74, C_76), A_364) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_74, C_76)))), inference(resolution, [status(thm)], [c_310, c_6223])).
% 27.34/16.05  tff(c_6311, plain, (![B_374, C_375]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_374, C_375)))), inference(resolution, [status(thm)], [c_6282, c_6231])).
% 27.34/16.05  tff(c_6534, plain, (![B_374, C_375]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_374, C_375)))), inference(splitLeft, [status(thm)], [c_6311])).
% 27.34/16.05  tff(c_2785, plain, (![C_212, B_65, C_67]: (r2_hidden('#skF_5', k2_zfmisc_1(C_212, '#skF_7')) | ~r2_hidden('#skF_3'('#skF_5', B_65, C_67), C_212) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_65, C_67)))), inference(resolution, [status(thm)], [c_274, c_2774])).
% 27.34/16.05  tff(c_6315, plain, (![B_374, C_375]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_374, C_375)))), inference(resolution, [status(thm)], [c_6282, c_2785])).
% 27.34/16.05  tff(c_6324, plain, (![B_374, C_375]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_374, C_375)))), inference(splitLeft, [status(thm)], [c_6315])).
% 27.34/16.05  tff(c_6334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6324, c_6269])).
% 27.34/16.05  tff(c_6335, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_6315])).
% 27.34/16.05  tff(c_6545, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6534, c_6335])).
% 27.34/16.05  tff(c_6546, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_6311])).
% 27.34/16.05  tff(c_6587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6574, c_6546])).
% 27.34/16.05  tff(c_6588, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_6558])).
% 27.34/16.05  tff(c_6599, plain, (![B_48, C_49]: (r2_hidden('#skF_3'('#skF_5', B_48, C_49), k3_xboole_0('#skF_6', '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_6588, c_152])).
% 27.34/16.05  tff(c_52602, plain, (![A_1020, A_1019, B_1017, C_1016, C_1021, B_1018]: (r2_hidden(A_1020, k2_zfmisc_1(C_1016, k3_xboole_0(A_1019, B_1018))) | ~r2_hidden('#skF_3'(A_1020, B_1017, C_1021), C_1016) | ~r2_hidden(A_1020, k2_zfmisc_1(B_1017, C_1021)) | ~r2_hidden('#skF_4'(A_1020, B_1017, C_1021), B_1018) | ~r2_hidden('#skF_4'(A_1020, B_1017, C_1021), A_1019))), inference(resolution, [status(thm)], [c_2, c_2774])).
% 27.34/16.05  tff(c_52991, plain, (![A_1022, B_1023, B_1024, C_1025]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(A_1022, B_1023))) | ~r2_hidden('#skF_4'('#skF_5', B_1024, C_1025), B_1023) | ~r2_hidden('#skF_4'('#skF_5', B_1024, C_1025), A_1022) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1024, C_1025)))), inference(resolution, [status(thm)], [c_310, c_52602])).
% 27.34/16.05  tff(c_53584, plain, (![A_1035, B_1036, C_1037]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(A_1035, '#skF_9'))) | ~r2_hidden('#skF_4'('#skF_5', B_1036, C_1037), A_1035) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1036, C_1037)))), inference(resolution, [status(thm)], [c_273, c_52991])).
% 27.34/16.05  tff(c_53595, plain, (![B_65, C_67]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0('#skF_7', '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_65, C_67)))), inference(resolution, [status(thm)], [c_274, c_53584])).
% 27.34/16.05  tff(c_53599, plain, (![B_65, C_67]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_65, C_67)))), inference(splitLeft, [status(thm)], [c_53595])).
% 27.34/16.05  tff(c_53002, plain, (![A_1026, B_1027, C_1028]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(A_1026, '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_5', B_1027, C_1028), A_1026) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1027, C_1028)))), inference(resolution, [status(thm)], [c_274, c_52991])).
% 27.34/16.05  tff(c_53012, plain, (![B_65, C_67]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0('#skF_9', '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_65, C_67)))), inference(resolution, [status(thm)], [c_273, c_53002])).
% 27.34/16.05  tff(c_53014, plain, (![B_65, C_67]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_65, C_67)))), inference(splitLeft, [status(thm)], [c_53012])).
% 27.34/16.05  tff(c_2835, plain, (![A_1, B_2, B_218, C_219]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(A_1, B_2), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_218, C_219)) | ~r2_hidden('#skF_3'('#skF_5', B_218, C_219), B_2) | ~r2_hidden('#skF_3'('#skF_5', B_218, C_219), A_1))), inference(resolution, [status(thm)], [c_2, c_2821])).
% 27.34/16.05  tff(c_44253, plain, (![A_943, B_944, C_945]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(A_943, k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_3'('#skF_5', B_944, C_945), A_943) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_944, C_945)))), inference(resolution, [status(thm)], [c_6282, c_2835])).
% 27.34/16.05  tff(c_44421, plain, (![B_74, C_76]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_74, C_76)))), inference(resolution, [status(thm)], [c_310, c_44253])).
% 27.34/16.05  tff(c_44582, plain, (![B_74, C_76]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_74, C_76)))), inference(splitLeft, [status(thm)], [c_44421])).
% 27.34/16.05  tff(c_6601, plain, (![B_384, C_385]: (r2_hidden('#skF_3'('#skF_5', B_384, C_385), k3_xboole_0('#skF_6', '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_384, C_385)))), inference(resolution, [status(thm)], [c_6588, c_152])).
% 27.34/16.05  tff(c_23815, plain, (![A_720, B_721, C_722]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(A_720, k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_3'('#skF_5', B_721, C_722), A_720) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_721, C_722)))), inference(resolution, [status(thm)], [c_6601, c_2835])).
% 27.34/16.05  tff(c_23915, plain, (![B_74, C_76]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_74, C_76)))), inference(resolution, [status(thm)], [c_309, c_23815])).
% 27.34/16.05  tff(c_24014, plain, (![B_74, C_76]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_74, C_76)))), inference(splitLeft, [status(thm)], [c_23915])).
% 27.34/16.05  tff(c_23914, plain, (![B_74, C_76]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_74, C_76)))), inference(resolution, [status(thm)], [c_310, c_23815])).
% 27.34/16.05  tff(c_23917, plain, (![B_74, C_76]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_74, C_76)))), inference(splitLeft, [status(thm)], [c_23914])).
% 27.34/16.05  tff(c_7393, plain, (![B_403, C_404]: (r2_hidden('#skF_3'('#skF_5', B_403, C_404), k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_403, C_404)))), inference(resolution, [status(thm)], [c_6546, c_152])).
% 27.34/16.05  tff(c_7425, plain, (![B_403, C_404]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_403, C_404)))), inference(resolution, [status(thm)], [c_7393, c_6231])).
% 27.34/16.05  tff(c_8267, plain, (![B_403, C_404]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_403, C_404)))), inference(splitLeft, [status(thm)], [c_7425])).
% 27.34/16.05  tff(c_6232, plain, (![A_364, B_74, C_76]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(A_364, '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_3'('#skF_5', B_74, C_76), A_364) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_74, C_76)))), inference(resolution, [status(thm)], [c_309, c_6223])).
% 27.34/16.05  tff(c_7424, plain, (![B_403, C_404]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_403, C_404)))), inference(resolution, [status(thm)], [c_7393, c_6232])).
% 27.34/16.05  tff(c_8227, plain, (![B_403, C_404]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_403, C_404)))), inference(splitLeft, [status(thm)], [c_7424])).
% 27.34/16.05  tff(c_6633, plain, (![B_384, C_385]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_384, C_385)))), inference(resolution, [status(thm)], [c_6601, c_6231])).
% 27.34/16.05  tff(c_6845, plain, (![B_384, C_385]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_384, C_385)))), inference(splitLeft, [status(thm)], [c_6633])).
% 27.34/16.05  tff(c_6637, plain, (![B_384, C_385]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_384, C_385)))), inference(resolution, [status(thm)], [c_6601, c_2785])).
% 27.34/16.05  tff(c_6817, plain, (![B_384, C_385]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_384, C_385)))), inference(splitLeft, [status(thm)], [c_6637])).
% 27.34/16.05  tff(c_6831, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6817, c_6588])).
% 27.34/16.05  tff(c_6832, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_6637])).
% 27.34/16.05  tff(c_6860, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6845, c_6832])).
% 27.34/16.05  tff(c_6861, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_6633])).
% 27.34/16.05  tff(c_7471, plain, (![B_405, C_406]: (r2_hidden('#skF_3'('#skF_5', B_405, C_406), k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_405, C_406)))), inference(resolution, [status(thm)], [c_6861, c_152])).
% 27.34/16.05  tff(c_7503, plain, (![B_405, C_406]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_405, C_406)))), inference(resolution, [status(thm)], [c_7471, c_6231])).
% 27.34/16.05  tff(c_8188, plain, (![B_405, C_406]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_405, C_406)))), inference(splitLeft, [status(thm)], [c_7503])).
% 27.34/16.05  tff(c_6632, plain, (![B_384, C_385]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_384, C_385)))), inference(resolution, [status(thm)], [c_6601, c_6232])).
% 27.34/16.05  tff(c_7100, plain, (![B_384, C_385]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_384, C_385)))), inference(splitLeft, [status(thm)], [c_6632])).
% 27.34/16.05  tff(c_6280, plain, (![B_48, C_49]: (r2_hidden('#skF_3'('#skF_5', B_48, C_49), k3_xboole_0('#skF_8', '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_6269, c_152])).
% 27.34/16.05  tff(c_6557, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_6280, c_6547])).
% 27.34/16.05  tff(c_6874, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_6557])).
% 27.34/16.05  tff(c_6890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6874, c_6861])).
% 27.34/16.05  tff(c_6891, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_6557])).
% 27.34/16.05  tff(c_7117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7100, c_6891])).
% 27.34/16.05  tff(c_7118, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_6632])).
% 27.34/16.05  tff(c_7736, plain, (![B_412, C_413]: (r2_hidden('#skF_3'('#skF_5', B_412, C_413), k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_412, C_413)))), inference(resolution, [status(thm)], [c_7118, c_152])).
% 27.34/16.05  tff(c_7772, plain, (![B_412, C_413]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_412, C_413)))), inference(resolution, [status(thm)], [c_7736, c_2785])).
% 27.34/16.05  tff(c_7781, plain, (![B_412, C_413]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_412, C_413)))), inference(splitLeft, [status(thm)], [c_7772])).
% 27.34/16.05  tff(c_7507, plain, (![B_405, C_406]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_405, C_406)))), inference(resolution, [status(thm)], [c_7471, c_2785])).
% 27.34/16.05  tff(c_7516, plain, (![B_405, C_406]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_405, C_406)))), inference(splitLeft, [status(thm)], [c_7507])).
% 27.34/16.05  tff(c_7429, plain, (![B_403, C_404]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_403, C_404)))), inference(resolution, [status(thm)], [c_7393, c_2785])).
% 27.34/16.05  tff(c_7438, plain, (![B_403, C_404]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_403, C_404)))), inference(splitLeft, [status(thm)], [c_7429])).
% 27.34/16.05  tff(c_7131, plain, (![B_396, C_397]: (r2_hidden('#skF_3'('#skF_5', B_396, C_397), k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_396, C_397)))), inference(resolution, [status(thm)], [c_6891, c_152])).
% 27.34/16.05  tff(c_7167, plain, (![B_396, C_397]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_396, C_397)))), inference(resolution, [status(thm)], [c_7131, c_2785])).
% 27.34/16.05  tff(c_7176, plain, (![B_396, C_397]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_396, C_397)))), inference(splitLeft, [status(thm)], [c_7167])).
% 27.34/16.05  tff(c_7194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7176, c_7118])).
% 27.34/16.05  tff(c_7195, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_7167])).
% 27.34/16.05  tff(c_7457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7438, c_7195])).
% 27.34/16.05  tff(c_7458, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_7429])).
% 27.34/16.05  tff(c_7536, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7516, c_7458])).
% 27.34/16.05  tff(c_7537, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_7507])).
% 27.34/16.05  tff(c_7802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7781, c_7537])).
% 27.34/16.05  tff(c_7803, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_7772])).
% 27.34/16.05  tff(c_8210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8188, c_7803])).
% 27.34/16.05  tff(c_8211, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_7503])).
% 27.34/16.05  tff(c_8250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8227, c_8211])).
% 27.34/16.05  tff(c_8251, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_7424])).
% 27.34/16.05  tff(c_8298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8267, c_8251])).
% 27.34/16.05  tff(c_8299, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_7425])).
% 27.34/16.05  tff(c_10341, plain, (![B_480, C_481]: (r2_hidden('#skF_3'('#skF_5', B_480, C_481), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_480, C_481)))), inference(resolution, [status(thm)], [c_8299, c_152])).
% 27.34/16.05  tff(c_10372, plain, (![B_480, C_481]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_480, C_481)))), inference(resolution, [status(thm)], [c_10341, c_6232])).
% 27.34/16.05  tff(c_12066, plain, (![B_480, C_481]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_480, C_481)))), inference(splitLeft, [status(thm)], [c_10372])).
% 27.34/16.05  tff(c_7768, plain, (![B_412, C_413]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_412, C_413)))), inference(resolution, [status(thm)], [c_7736, c_6231])).
% 27.34/16.05  tff(c_8407, plain, (![B_412, C_413]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_412, C_413)))), inference(splitLeft, [status(thm)], [c_7768])).
% 27.34/16.05  tff(c_7502, plain, (![B_405, C_406]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_405, C_406)))), inference(resolution, [status(thm)], [c_7471, c_6232])).
% 27.34/16.05  tff(c_8357, plain, (![B_405, C_406]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_405, C_406)))), inference(splitLeft, [status(thm)], [c_7502])).
% 27.34/16.05  tff(c_7163, plain, (![B_396, C_397]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_396, C_397)))), inference(resolution, [status(thm)], [c_7131, c_6231])).
% 27.34/16.05  tff(c_8315, plain, (![B_396, C_397]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_396, C_397)))), inference(splitLeft, [status(thm)], [c_7163])).
% 27.34/16.05  tff(c_8340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8315, c_8299])).
% 27.34/16.05  tff(c_8341, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_7163])).
% 27.34/16.05  tff(c_8383, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8357, c_8341])).
% 27.34/16.05  tff(c_8384, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_7502])).
% 27.34/16.05  tff(c_8434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8407, c_8384])).
% 27.34/16.05  tff(c_8435, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_7768])).
% 27.34/16.05  tff(c_10640, plain, (![B_487, C_488]: (r2_hidden('#skF_3'('#skF_5', B_487, C_488), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_487, C_488)))), inference(resolution, [status(thm)], [c_8435, c_152])).
% 27.34/16.05  tff(c_10676, plain, (![B_487, C_488]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_487, C_488)))), inference(resolution, [status(thm)], [c_10640, c_2785])).
% 27.34/16.05  tff(c_10685, plain, (![B_487, C_488]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_487, C_488)))), inference(splitLeft, [status(thm)], [c_10676])).
% 27.34/16.05  tff(c_10377, plain, (![B_480, C_481]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_480, C_481)))), inference(resolution, [status(thm)], [c_10341, c_2785])).
% 27.34/16.05  tff(c_10386, plain, (![B_480, C_481]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_480, C_481)))), inference(splitLeft, [status(thm)], [c_10377])).
% 27.34/16.05  tff(c_7162, plain, (![B_396, C_397]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_396, C_397)))), inference(resolution, [status(thm)], [c_7131, c_6232])).
% 27.34/16.05  tff(c_8700, plain, (![B_396, C_397]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_396, C_397)))), inference(splitLeft, [status(thm)], [c_7162])).
% 27.34/16.05  tff(c_7767, plain, (![B_412, C_413]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_412, C_413)))), inference(resolution, [status(thm)], [c_7736, c_6232])).
% 27.34/16.05  tff(c_8451, plain, (![B_412, C_413]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_412, C_413)))), inference(splitLeft, [status(thm)], [c_7767])).
% 27.34/16.05  tff(c_8479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8451, c_8435])).
% 27.34/16.05  tff(c_8480, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_7767])).
% 27.34/16.05  tff(c_8729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8700, c_8480])).
% 27.34/16.05  tff(c_8730, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_7162])).
% 27.34/16.05  tff(c_10231, plain, (![B_474, C_475]: (r2_hidden('#skF_3'('#skF_5', B_474, C_475), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_474, C_475)))), inference(resolution, [status(thm)], [c_8730, c_152])).
% 27.34/16.05  tff(c_10267, plain, (![B_474, C_475]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_474, C_475)))), inference(resolution, [status(thm)], [c_10231, c_2785])).
% 27.34/16.05  tff(c_10276, plain, (![B_474, C_475]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_474, C_475)))), inference(splitLeft, [status(thm)], [c_10267])).
% 27.34/16.05  tff(c_9955, plain, (![B_467, C_468]: (r2_hidden('#skF_3'('#skF_5', B_467, C_468), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_467, C_468)))), inference(resolution, [status(thm)], [c_8341, c_152])).
% 27.34/16.05  tff(c_9991, plain, (![B_467, C_468]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_467, C_468)))), inference(resolution, [status(thm)], [c_9955, c_2785])).
% 27.34/16.05  tff(c_10000, plain, (![B_467, C_468]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_467, C_468)))), inference(splitLeft, [status(thm)], [c_9991])).
% 27.34/16.05  tff(c_9847, plain, (![B_461, C_462]: (r2_hidden('#skF_3'('#skF_5', B_461, C_462), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_461, C_462)))), inference(resolution, [status(thm)], [c_8384, c_152])).
% 27.34/16.05  tff(c_9883, plain, (![B_461, C_462]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_461, C_462)))), inference(resolution, [status(thm)], [c_9847, c_2785])).
% 27.34/16.05  tff(c_9892, plain, (![B_461, C_462]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_461, C_462)))), inference(splitLeft, [status(thm)], [c_9883])).
% 27.34/16.05  tff(c_9546, plain, (![B_454, C_455]: (r2_hidden('#skF_3'('#skF_5', B_454, C_455), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_454, C_455)))), inference(resolution, [status(thm)], [c_8211, c_152])).
% 27.34/16.05  tff(c_9582, plain, (![B_454, C_455]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_454, C_455)))), inference(resolution, [status(thm)], [c_9546, c_2785])).
% 27.34/16.05  tff(c_9591, plain, (![B_454, C_455]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_454, C_455)))), inference(splitLeft, [status(thm)], [c_9582])).
% 27.34/16.05  tff(c_9035, plain, (![B_445, C_446]: (r2_hidden('#skF_3'('#skF_5', B_445, C_446), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_445, C_446)))), inference(resolution, [status(thm)], [c_8251, c_152])).
% 27.34/16.05  tff(c_9071, plain, (![B_445, C_446]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_445, C_446)))), inference(resolution, [status(thm)], [c_9035, c_2785])).
% 27.34/16.05  tff(c_9080, plain, (![B_445, C_446]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_445, C_446)))), inference(splitLeft, [status(thm)], [c_9071])).
% 27.34/16.05  tff(c_8753, plain, (![B_438, C_439]: (r2_hidden('#skF_3'('#skF_5', B_438, C_439), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_438, C_439)))), inference(resolution, [status(thm)], [c_8480, c_152])).
% 27.34/16.05  tff(c_8789, plain, (![B_438, C_439]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_438, C_439)))), inference(resolution, [status(thm)], [c_8753, c_2785])).
% 27.34/16.05  tff(c_8798, plain, (![B_438, C_439]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_438, C_439)))), inference(splitLeft, [status(thm)], [c_8789])).
% 27.34/16.05  tff(c_8828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8798, c_8730])).
% 27.34/16.05  tff(c_8829, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_8789])).
% 27.34/16.05  tff(c_9111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9080, c_8829])).
% 27.34/16.05  tff(c_9112, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_9071])).
% 27.34/16.05  tff(c_9623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9591, c_9112])).
% 27.34/16.05  tff(c_9624, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_9582])).
% 27.34/16.05  tff(c_9925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9892, c_9624])).
% 27.34/16.05  tff(c_9926, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_9883])).
% 27.34/16.05  tff(c_10034, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10000, c_9926])).
% 27.34/16.05  tff(c_10035, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_9991])).
% 27.34/16.05  tff(c_10311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10276, c_10035])).
% 27.34/16.05  tff(c_10312, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_10267])).
% 27.34/16.05  tff(c_10422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10386, c_10312])).
% 27.34/16.05  tff(c_10423, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_10377])).
% 27.34/16.05  tff(c_10722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10685, c_10423])).
% 27.34/16.05  tff(c_10723, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_10676])).
% 27.34/16.05  tff(c_12104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12066, c_10723])).
% 27.34/16.05  tff(c_12105, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_10372])).
% 27.34/16.05  tff(c_23105, plain, (![B_711, C_712]: (r2_hidden('#skF_3'('#skF_5', B_711, C_712), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_711, C_712)))), inference(resolution, [status(thm)], [c_12105, c_152])).
% 27.34/16.05  tff(c_23162, plain, (![B_711, C_712]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_711, C_712)))), inference(resolution, [status(thm)], [c_23105, c_2785])).
% 27.34/16.05  tff(c_23720, plain, (![B_711, C_712]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_711, C_712)))), inference(splitLeft, [status(thm)], [c_23162])).
% 27.34/16.05  tff(c_9066, plain, (![B_445, C_446]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_445, C_446)))), inference(resolution, [status(thm)], [c_9035, c_6232])).
% 27.34/16.05  tff(c_13188, plain, (![B_445, C_446]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_445, C_446)))), inference(splitLeft, [status(thm)], [c_9066])).
% 27.34/16.05  tff(c_9878, plain, (![B_461, C_462]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_461, C_462)))), inference(resolution, [status(thm)], [c_9847, c_6232])).
% 27.34/16.05  tff(c_12611, plain, (![B_461, C_462]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_461, C_462)))), inference(splitLeft, [status(thm)], [c_9878])).
% 27.34/16.05  tff(c_10672, plain, (![B_487, C_488]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_487, C_488)))), inference(resolution, [status(thm)], [c_10640, c_6231])).
% 27.34/16.05  tff(c_12326, plain, (![B_487, C_488]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_487, C_488)))), inference(splitLeft, [status(thm)], [c_10672])).
% 27.34/16.05  tff(c_9578, plain, (![B_454, C_455]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_454, C_455)))), inference(resolution, [status(thm)], [c_9546, c_6231])).
% 27.34/16.05  tff(c_12262, plain, (![B_454, C_455]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_454, C_455)))), inference(splitLeft, [status(thm)], [c_9578])).
% 27.34/16.05  tff(c_10263, plain, (![B_474, C_475]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_474, C_475)))), inference(resolution, [status(thm)], [c_10231, c_6231])).
% 27.34/16.05  tff(c_12189, plain, (![B_474, C_475]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_474, C_475)))), inference(splitLeft, [status(thm)], [c_10263])).
% 27.34/16.05  tff(c_10671, plain, (![B_487, C_488]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_487, C_488)))), inference(resolution, [status(thm)], [c_10640, c_6232])).
% 27.34/16.05  tff(c_12127, plain, (![B_487, C_488]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_487, C_488)))), inference(splitLeft, [status(thm)], [c_10671])).
% 27.34/16.05  tff(c_12166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12127, c_12105])).
% 27.34/16.05  tff(c_12167, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_10671])).
% 27.34/16.05  tff(c_12229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12189, c_12167])).
% 27.34/16.05  tff(c_12230, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_10263])).
% 27.34/16.05  tff(c_12303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12262, c_12230])).
% 27.34/16.05  tff(c_12304, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_9578])).
% 27.34/16.05  tff(c_12588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12326, c_12304])).
% 27.34/16.05  tff(c_12589, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_10672])).
% 27.34/16.05  tff(c_13165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12611, c_12589])).
% 27.34/16.05  tff(c_13166, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_9878])).
% 27.34/16.05  tff(c_13232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13188, c_13166])).
% 27.34/16.05  tff(c_13233, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_9066])).
% 27.34/16.05  tff(c_22678, plain, (![B_704, C_705]: (r2_hidden('#skF_3'('#skF_5', B_704, C_705), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_704, C_705)))), inference(resolution, [status(thm)], [c_13233, c_152])).
% 27.34/16.05  tff(c_22735, plain, (![B_704, C_705]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_704, C_705)))), inference(resolution, [status(thm)], [c_22678, c_2785])).
% 27.34/16.05  tff(c_22744, plain, (![B_704, C_705]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_704, C_705)))), inference(splitLeft, [status(thm)], [c_22735])).
% 27.34/16.05  tff(c_21979, plain, (![B_695, C_696]: (r2_hidden('#skF_3'('#skF_5', B_695, C_696), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_695, C_696)))), inference(resolution, [status(thm)], [c_12304, c_152])).
% 27.34/16.05  tff(c_22033, plain, (![B_695, C_696]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_695, C_696)))), inference(resolution, [status(thm)], [c_21979, c_2785])).
% 27.34/16.05  tff(c_22585, plain, (![B_695, C_696]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_695, C_696)))), inference(splitLeft, [status(thm)], [c_22033])).
% 27.34/16.05  tff(c_21824, plain, (![B_693, C_694]: (r2_hidden('#skF_3'('#skF_5', B_693, C_694), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_693, C_694)))), inference(resolution, [status(thm)], [c_12167, c_152])).
% 27.34/16.05  tff(c_21878, plain, (![B_693, C_694]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_693, C_694)))), inference(resolution, [status(thm)], [c_21824, c_2785])).
% 27.34/16.05  tff(c_21887, plain, (![B_693, C_694]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_693, C_694)))), inference(splitLeft, [status(thm)], [c_21878])).
% 27.34/16.05  tff(c_21136, plain, (![B_684, C_685]: (r2_hidden('#skF_3'('#skF_5', B_684, C_685), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_684, C_685)))), inference(resolution, [status(thm)], [c_12230, c_152])).
% 27.34/16.05  tff(c_21187, plain, (![B_684, C_685]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_684, C_685)))), inference(resolution, [status(thm)], [c_21136, c_2785])).
% 27.34/16.05  tff(c_21733, plain, (![B_684, C_685]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_684, C_685)))), inference(splitLeft, [status(thm)], [c_21187])).
% 27.34/16.05  tff(c_20735, plain, (![B_677, C_678]: (r2_hidden('#skF_3'('#skF_5', B_677, C_678), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_677, C_678)))), inference(resolution, [status(thm)], [c_13166, c_152])).
% 27.34/16.05  tff(c_20786, plain, (![B_677, C_678]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_677, C_678)))), inference(resolution, [status(thm)], [c_20735, c_2785])).
% 27.34/16.05  tff(c_20795, plain, (![B_677, C_678]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_677, C_678)))), inference(splitLeft, [status(thm)], [c_20786])).
% 27.34/16.05  tff(c_8784, plain, (![B_438, C_439]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_438, C_439)))), inference(resolution, [status(thm)], [c_8753, c_6232])).
% 27.34/16.05  tff(c_14916, plain, (![B_438, C_439]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_438, C_439)))), inference(splitLeft, [status(thm)], [c_8784])).
% 27.34/16.05  tff(c_9067, plain, (![B_445, C_446]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_445, C_446)))), inference(resolution, [status(thm)], [c_9035, c_6231])).
% 27.34/16.05  tff(c_14621, plain, (![B_445, C_446]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_445, C_446)))), inference(splitLeft, [status(thm)], [c_9067])).
% 27.34/16.05  tff(c_9987, plain, (![B_467, C_468]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_467, C_468)))), inference(resolution, [status(thm)], [c_9955, c_6231])).
% 27.34/16.05  tff(c_14540, plain, (![B_467, C_468]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_467, C_468)))), inference(splitLeft, [status(thm)], [c_9987])).
% 27.34/16.05  tff(c_9577, plain, (![B_454, C_455]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_454, C_455)))), inference(resolution, [status(thm)], [c_9546, c_6232])).
% 27.34/16.05  tff(c_14247, plain, (![B_454, C_455]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_454, C_455)))), inference(splitLeft, [status(thm)], [c_9577])).
% 27.34/16.05  tff(c_10373, plain, (![B_480, C_481]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_480, C_481)))), inference(resolution, [status(thm)], [c_10341, c_6231])).
% 27.34/16.05  tff(c_14175, plain, (![B_480, C_481]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_480, C_481)))), inference(splitLeft, [status(thm)], [c_10373])).
% 27.34/16.05  tff(c_9986, plain, (![B_467, C_468]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_467, C_468)))), inference(resolution, [status(thm)], [c_9955, c_6232])).
% 27.34/16.05  tff(c_13575, plain, (![B_467, C_468]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_467, C_468)))), inference(splitLeft, [status(thm)], [c_9986])).
% 27.34/16.05  tff(c_13620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13575, c_13233])).
% 27.34/16.05  tff(c_13621, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_9986])).
% 27.34/16.05  tff(c_14221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14175, c_13621])).
% 27.34/16.05  tff(c_14222, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_10373])).
% 27.34/16.05  tff(c_14514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14247, c_14222])).
% 27.34/16.05  tff(c_14515, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_9577])).
% 27.34/16.05  tff(c_14595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14540, c_14515])).
% 27.34/16.05  tff(c_14596, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_9987])).
% 27.34/16.05  tff(c_14670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14621, c_14596])).
% 27.34/16.05  tff(c_14671, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_9067])).
% 27.34/16.05  tff(c_14966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14916, c_14671])).
% 27.34/16.05  tff(c_14967, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_8784])).
% 27.34/16.05  tff(c_20058, plain, (![B_668, C_669]: (r2_hidden('#skF_3'('#skF_5', B_668, C_669), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_668, C_669)))), inference(resolution, [status(thm)], [c_14967, c_152])).
% 27.34/16.05  tff(c_20106, plain, (![B_668, C_669]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_668, C_669)))), inference(resolution, [status(thm)], [c_20058, c_2785])).
% 27.34/16.05  tff(c_20646, plain, (![B_668, C_669]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_668, C_669)))), inference(splitLeft, [status(thm)], [c_20106])).
% 27.34/16.05  tff(c_19663, plain, (![B_661, C_662]: (r2_hidden('#skF_3'('#skF_5', B_661, C_662), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_661, C_662)))), inference(resolution, [status(thm)], [c_14596, c_152])).
% 27.34/16.05  tff(c_19711, plain, (![B_661, C_662]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_661, C_662)))), inference(resolution, [status(thm)], [c_19663, c_2785])).
% 27.34/16.05  tff(c_19720, plain, (![B_661, C_662]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_661, C_662)))), inference(splitLeft, [status(thm)], [c_19711])).
% 27.34/16.05  tff(c_10262, plain, (![B_474, C_475]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_474, C_475)))), inference(resolution, [status(thm)], [c_10231, c_6232])).
% 27.34/16.05  tff(c_14999, plain, (![B_474, C_475]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_474, C_475)))), inference(splitLeft, [status(thm)], [c_10262])).
% 27.34/16.05  tff(c_15050, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14999, c_14967])).
% 27.34/16.05  tff(c_15051, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_10262])).
% 27.34/16.05  tff(c_18997, plain, (![B_652, C_653]: (r2_hidden('#skF_3'('#skF_5', B_652, C_653), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_652, C_653)))), inference(resolution, [status(thm)], [c_15051, c_152])).
% 27.34/16.05  tff(c_19042, plain, (![B_652, C_653]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_652, C_653)))), inference(resolution, [status(thm)], [c_18997, c_2785])).
% 27.34/16.05  tff(c_19576, plain, (![B_652, C_653]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_652, C_653)))), inference(splitLeft, [status(thm)], [c_19042])).
% 27.34/16.05  tff(c_18622, plain, (![B_645, C_646]: (r2_hidden('#skF_3'('#skF_5', B_645, C_646), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_645, C_646)))), inference(resolution, [status(thm)], [c_14222, c_152])).
% 27.34/16.05  tff(c_18667, plain, (![B_645, C_646]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_645, C_646)))), inference(resolution, [status(thm)], [c_18622, c_2785])).
% 27.34/16.05  tff(c_18676, plain, (![B_645, C_646]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_645, C_646)))), inference(splitLeft, [status(thm)], [c_18667])).
% 27.34/16.05  tff(c_17967, plain, (![B_636, C_637]: (r2_hidden('#skF_3'('#skF_5', B_636, C_637), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_636, C_637)))), inference(resolution, [status(thm)], [c_14515, c_152])).
% 27.34/16.05  tff(c_18009, plain, (![B_636, C_637]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_636, C_637)))), inference(resolution, [status(thm)], [c_17967, c_2785])).
% 27.34/16.05  tff(c_18537, plain, (![B_636, C_637]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_636, C_637)))), inference(splitLeft, [status(thm)], [c_18009])).
% 27.34/16.05  tff(c_8785, plain, (![B_438, C_439]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_438, C_439)))), inference(resolution, [status(thm)], [c_8753, c_6231])).
% 27.34/16.05  tff(c_15350, plain, (![B_438, C_439]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_438, C_439)))), inference(splitLeft, [status(thm)], [c_8785])).
% 27.34/16.05  tff(c_9879, plain, (![B_461, C_462]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_461, C_462)))), inference(resolution, [status(thm)], [c_9847, c_6231])).
% 27.34/16.05  tff(c_15076, plain, (![B_461, C_462]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_461, C_462)))), inference(splitLeft, [status(thm)], [c_9879])).
% 27.34/16.05  tff(c_15128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15076, c_15051])).
% 27.34/16.05  tff(c_15129, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_9879])).
% 27.34/16.05  tff(c_15403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15350, c_15129])).
% 27.34/16.05  tff(c_15404, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_8785])).
% 27.34/16.05  tff(c_17605, plain, (![B_629, C_630]: (r2_hidden('#skF_3'('#skF_5', B_629, C_630), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_629, C_630)))), inference(resolution, [status(thm)], [c_15404, c_152])).
% 27.34/16.05  tff(c_17647, plain, (![B_629, C_630]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_629, C_630)))), inference(resolution, [status(thm)], [c_17605, c_2785])).
% 27.34/16.05  tff(c_17656, plain, (![B_629, C_630]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_629, C_630)))), inference(splitLeft, [status(thm)], [c_17647])).
% 27.34/16.05  tff(c_16961, plain, (![B_620, C_621]: (r2_hidden('#skF_3'('#skF_5', B_620, C_621), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_620, C_621)))), inference(resolution, [status(thm)], [c_13621, c_152])).
% 27.34/16.05  tff(c_17000, plain, (![B_620, C_621]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_620, C_621)))), inference(resolution, [status(thm)], [c_16961, c_2785])).
% 27.34/16.05  tff(c_17522, plain, (![B_620, C_621]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_620, C_621)))), inference(splitLeft, [status(thm)], [c_17000])).
% 27.34/16.05  tff(c_16395, plain, (![B_606, C_607]: (r2_hidden('#skF_3'('#skF_5', B_606, C_607), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_606, C_607)))), inference(resolution, [status(thm)], [c_12589, c_152])).
% 27.34/16.05  tff(c_16434, plain, (![B_606, C_607]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_606, C_607)))), inference(resolution, [status(thm)], [c_16395, c_2785])).
% 27.34/16.05  tff(c_16443, plain, (![B_606, C_607]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_606, C_607)))), inference(splitLeft, [status(thm)], [c_16434])).
% 27.34/16.05  tff(c_15778, plain, (![B_597, C_598]: (r2_hidden('#skF_3'('#skF_5', B_597, C_598), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_597, C_598)))), inference(resolution, [status(thm)], [c_14671, c_152])).
% 27.34/16.05  tff(c_15814, plain, (![B_597, C_598]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_597, C_598)))), inference(resolution, [status(thm)], [c_15778, c_2785])).
% 27.34/16.05  tff(c_15823, plain, (![B_597, C_598]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_597, C_598)))), inference(splitLeft, [status(thm)], [c_15814])).
% 27.34/16.05  tff(c_15436, plain, (![B_590, C_591]: (r2_hidden('#skF_3'('#skF_5', B_590, C_591), k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_590, C_591)))), inference(resolution, [status(thm)], [c_15129, c_152])).
% 27.34/16.05  tff(c_15472, plain, (![B_590, C_591]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_590, C_591)))), inference(resolution, [status(thm)], [c_15436, c_2785])).
% 27.34/16.05  tff(c_15481, plain, (![B_590, C_591]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_590, C_591)))), inference(splitLeft, [status(thm)], [c_15472])).
% 27.34/16.05  tff(c_15535, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15481, c_15404])).
% 27.34/16.05  tff(c_15536, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_15472])).
% 27.34/16.05  tff(c_15878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15823, c_15536])).
% 27.34/16.05  tff(c_15879, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_15814])).
% 27.34/16.05  tff(c_16499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16443, c_15879])).
% 27.34/16.05  tff(c_16500, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_16434])).
% 27.34/16.05  tff(c_17579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17522, c_16500])).
% 27.34/16.05  tff(c_17580, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_17000])).
% 27.34/16.05  tff(c_17941, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17656, c_17580])).
% 27.34/16.05  tff(c_17942, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_17647])).
% 27.34/16.05  tff(c_18596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18537, c_17942])).
% 27.34/16.05  tff(c_18597, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_18009])).
% 27.34/16.05  tff(c_18971, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18676, c_18597])).
% 27.34/16.05  tff(c_18972, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_18667])).
% 27.34/16.05  tff(c_19637, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19576, c_18972])).
% 27.34/16.05  tff(c_19638, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_19042])).
% 27.34/16.05  tff(c_20032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19720, c_19638])).
% 27.34/16.05  tff(c_20033, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_6'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_19711])).
% 27.34/16.05  tff(c_20709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20646, c_20033])).
% 27.34/16.05  tff(c_20710, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_8'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_20106])).
% 27.34/16.05  tff(c_21110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20795, c_20710])).
% 27.34/16.05  tff(c_21111, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_8'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_20786])).
% 27.34/16.05  tff(c_21798, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21733, c_21111])).
% 27.34/16.05  tff(c_21799, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), '#skF_8'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_21187])).
% 27.34/16.05  tff(c_21953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21887, c_21799])).
% 27.34/16.05  tff(c_21954, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), '#skF_6'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_21878])).
% 27.34/16.05  tff(c_22652, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22585, c_21954])).
% 27.34/16.05  tff(c_22653, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), '#skF_6'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_22033])).
% 27.34/16.05  tff(c_23079, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22744, c_22653])).
% 27.34/16.05  tff(c_23080, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_8'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_22735])).
% 27.34/16.05  tff(c_23789, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23720, c_23080])).
% 27.34/16.05  tff(c_23790, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), '#skF_6'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_23162])).
% 27.34/16.05  tff(c_23988, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23917, c_23790])).
% 27.34/16.05  tff(c_23989, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_9'))), inference(splitRight, [status(thm)], [c_23914])).
% 27.34/16.05  tff(c_24535, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24014, c_23989])).
% 27.34/16.05  tff(c_24536, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_9'))), inference(splitRight, [status(thm)], [c_23915])).
% 27.34/16.05  tff(c_24732, plain, (![B_731, C_732]: (r2_hidden('#skF_3'('#skF_5', B_731, C_732), k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_731, C_732)))), inference(resolution, [status(thm)], [c_24536, c_152])).
% 27.34/16.05  tff(c_24791, plain, (![B_731, C_732]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_731, C_732)))), inference(resolution, [status(thm)], [c_24732, c_6231])).
% 27.34/16.05  tff(c_26288, plain, (![B_731, C_732]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_731, C_732)))), inference(splitLeft, [status(thm)], [c_24791])).
% 27.34/16.05  tff(c_24561, plain, (![B_729, C_730]: (r2_hidden('#skF_3'('#skF_5', B_729, C_730), k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_729, C_730)))), inference(resolution, [status(thm)], [c_23989, c_152])).
% 27.34/16.05  tff(c_24620, plain, (![B_729, C_730]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_729, C_730)))), inference(resolution, [status(thm)], [c_24561, c_6231])).
% 27.34/16.05  tff(c_25729, plain, (![B_729, C_730]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_729, C_730)))), inference(splitLeft, [status(thm)], [c_24620])).
% 27.34/16.05  tff(c_23913, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_6280, c_23815])).
% 27.34/16.05  tff(c_25353, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_23913])).
% 27.34/16.05  tff(c_24795, plain, (![B_731, C_732]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_731, C_732)))), inference(resolution, [status(thm)], [c_24732, c_2785])).
% 27.34/16.05  tff(c_24804, plain, (![B_731, C_732]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_731, C_732)))), inference(splitLeft, [status(thm)], [c_24795])).
% 27.34/16.05  tff(c_24624, plain, (![B_729, C_730]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_729, C_730)))), inference(resolution, [status(thm)], [c_24561, c_2785])).
% 27.34/16.05  tff(c_24633, plain, (![B_729, C_730]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_729, C_730)))), inference(splitLeft, [status(thm)], [c_24624])).
% 27.34/16.05  tff(c_24706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24633, c_24536])).
% 27.34/16.05  tff(c_24707, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_24624])).
% 27.34/16.05  tff(c_25327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24804, c_24707])).
% 27.34/16.05  tff(c_25328, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_24795])).
% 27.34/16.05  tff(c_25428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25353, c_25328])).
% 27.34/16.05  tff(c_25429, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9'))), inference(splitRight, [status(thm)], [c_23913])).
% 27.34/16.05  tff(c_25805, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25729, c_25429])).
% 27.34/16.05  tff(c_25806, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_24620])).
% 27.34/16.05  tff(c_26365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26288, c_25806])).
% 27.34/16.05  tff(c_26366, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_24791])).
% 27.34/16.05  tff(c_28350, plain, (![B_773, C_774]: (r2_hidden('#skF_3'('#skF_5', B_773, C_774), k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_773, C_774)))), inference(resolution, [status(thm)], [c_26366, c_152])).
% 27.34/16.05  tff(c_28409, plain, (![B_773, C_774]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_773, C_774)))), inference(resolution, [status(thm)], [c_28350, c_6231])).
% 27.34/16.05  tff(c_32012, plain, (![B_773, C_774]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_773, C_774)))), inference(splitLeft, [status(thm)], [c_28409])).
% 27.34/16.05  tff(c_24790, plain, (![B_731, C_732]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_731, C_732)))), inference(resolution, [status(thm)], [c_24732, c_6232])).
% 27.34/16.05  tff(c_26778, plain, (![B_731, C_732]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_731, C_732)))), inference(splitLeft, [status(thm)], [c_24790])).
% 27.34/16.05  tff(c_24619, plain, (![B_729, C_730]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_729, C_730)))), inference(resolution, [status(thm)], [c_24561, c_6232])).
% 27.34/16.05  tff(c_26391, plain, (![B_729, C_730]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_729, C_730)))), inference(splitLeft, [status(thm)], [c_24619])).
% 27.34/16.05  tff(c_26469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26391, c_26366])).
% 27.34/16.05  tff(c_26470, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_24619])).
% 27.34/16.05  tff(c_26857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26778, c_26470])).
% 27.34/16.05  tff(c_26858, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_24790])).
% 27.34/16.05  tff(c_28996, plain, (![B_781, C_782]: (r2_hidden('#skF_3'('#skF_5', B_781, C_782), k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_781, C_782)))), inference(resolution, [status(thm)], [c_26858, c_152])).
% 27.34/16.05  tff(c_29055, plain, (![B_781, C_782]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_781, C_782)))), inference(resolution, [status(thm)], [c_28996, c_6231])).
% 27.34/16.05  tff(c_31890, plain, (![B_781, C_782]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_781, C_782)))), inference(splitLeft, [status(thm)], [c_29055])).
% 27.34/16.05  tff(c_6634, plain, (![A_1, B_384, C_385]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(A_1, k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_3'('#skF_5', B_384, C_385), A_1) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_384, C_385)))), inference(resolution, [status(thm)], [c_6601, c_2835])).
% 27.34/16.05  tff(c_24610, plain, (![B_729, C_730]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_729, C_730)))), inference(resolution, [status(thm)], [c_24561, c_6634])).
% 27.34/16.05  tff(c_31471, plain, (![B_729, C_730]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_729, C_730)))), inference(splitLeft, [status(thm)], [c_24610])).
% 27.34/16.05  tff(c_24781, plain, (![B_731, C_732]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_731, C_732)))), inference(resolution, [status(thm)], [c_24732, c_6634])).
% 27.34/16.05  tff(c_31351, plain, (![B_731, C_732]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_731, C_732)))), inference(splitLeft, [status(thm)], [c_24781])).
% 27.34/16.05  tff(c_27348, plain, (![B_761, C_762]: (r2_hidden('#skF_3'('#skF_5', B_761, C_762), k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_761, C_762)))), inference(resolution, [status(thm)], [c_25429, c_152])).
% 27.34/16.05  tff(c_27406, plain, (![B_761, C_762]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_761, C_762)))), inference(resolution, [status(thm)], [c_27348, c_6232])).
% 27.34/16.05  tff(c_30934, plain, (![B_761, C_762]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_761, C_762)))), inference(splitLeft, [status(thm)], [c_27406])).
% 27.34/16.05  tff(c_27407, plain, (![B_761, C_762]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_761, C_762)))), inference(resolution, [status(thm)], [c_27348, c_6231])).
% 27.34/16.05  tff(c_30816, plain, (![B_761, C_762]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_761, C_762)))), inference(splitLeft, [status(thm)], [c_27407])).
% 27.34/16.05  tff(c_6872, plain, (![B_48, C_49]: (r2_hidden('#skF_3'('#skF_5', B_48, C_49), k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_6861, c_152])).
% 27.34/16.05  tff(c_23908, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_6872, c_23815])).
% 27.34/16.05  tff(c_30570, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_23908])).
% 27.34/16.05  tff(c_7098, plain, (![B_48, C_49]: (r2_hidden('#skF_3'('#skF_5', B_48, C_49), k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_6891, c_152])).
% 27.34/16.05  tff(c_23910, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_7098, c_23815])).
% 27.34/16.05  tff(c_30454, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_23910])).
% 27.34/16.05  tff(c_7129, plain, (![B_48, C_49]: (r2_hidden('#skF_3'('#skF_5', B_48, C_49), k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_7118, c_152])).
% 27.34/16.05  tff(c_23907, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_7129, c_23815])).
% 27.34/16.05  tff(c_30339, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_23907])).
% 27.34/16.05  tff(c_6572, plain, (![B_48, C_49]: (r2_hidden('#skF_3'('#skF_5', B_48, C_49), k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_6546, c_152])).
% 27.34/16.05  tff(c_23909, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_6572, c_23815])).
% 27.34/16.05  tff(c_29480, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_23909])).
% 27.34/16.05  tff(c_29059, plain, (![B_781, C_782]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_781, C_782)))), inference(resolution, [status(thm)], [c_28996, c_2785])).
% 27.34/16.05  tff(c_29068, plain, (![B_781, C_782]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_781, C_782)))), inference(splitLeft, [status(thm)], [c_29059])).
% 27.34/16.05  tff(c_28413, plain, (![B_773, C_774]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_773, C_774)))), inference(resolution, [status(thm)], [c_28350, c_2785])).
% 27.34/16.05  tff(c_28422, plain, (![B_773, C_774]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_773, C_774)))), inference(splitLeft, [status(thm)], [c_28413])).
% 27.34/16.05  tff(c_28170, plain, (![B_771, C_772]: (r2_hidden('#skF_3'('#skF_5', B_771, C_772), k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_771, C_772)))), inference(resolution, [status(thm)], [c_25806, c_152])).
% 27.34/16.05  tff(c_28233, plain, (![B_771, C_772]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_771, C_772)))), inference(resolution, [status(thm)], [c_28170, c_2785])).
% 27.34/16.05  tff(c_28242, plain, (![B_771, C_772]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_771, C_772)))), inference(splitLeft, [status(thm)], [c_28233])).
% 27.34/16.05  tff(c_27526, plain, (![B_763, C_764]: (r2_hidden('#skF_3'('#skF_5', B_763, C_764), k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_763, C_764)))), inference(resolution, [status(thm)], [c_26470, c_152])).
% 27.34/16.05  tff(c_27589, plain, (![B_763, C_764]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_763, C_764)))), inference(resolution, [status(thm)], [c_27526, c_2785])).
% 27.34/16.05  tff(c_27598, plain, (![B_763, C_764]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_763, C_764)))), inference(splitLeft, [status(thm)], [c_27589])).
% 27.34/16.05  tff(c_27411, plain, (![B_761, C_762]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_761, C_762)))), inference(resolution, [status(thm)], [c_27348, c_2785])).
% 27.34/16.05  tff(c_27420, plain, (![B_761, C_762]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_761, C_762)))), inference(splitLeft, [status(thm)], [c_27411])).
% 27.34/16.05  tff(c_27500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27420, c_26858])).
% 27.34/16.05  tff(c_27501, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_27411])).
% 27.34/16.05  tff(c_27679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27598, c_27501])).
% 27.34/16.05  tff(c_27680, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_27589])).
% 27.34/16.05  tff(c_28324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28242, c_27680])).
% 27.34/16.05  tff(c_28325, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_28233])).
% 27.34/16.05  tff(c_28505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28422, c_28325])).
% 27.34/16.05  tff(c_28506, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_28413])).
% 27.34/16.05  tff(c_29152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29068, c_28506])).
% 27.34/16.05  tff(c_29153, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_29059])).
% 27.34/16.05  tff(c_29565, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29480, c_29153])).
% 27.34/16.05  tff(c_29566, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9'))), inference(splitRight, [status(thm)], [c_23909])).
% 27.34/16.05  tff(c_30425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30339, c_29566])).
% 27.34/16.05  tff(c_30426, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9'))), inference(splitRight, [status(thm)], [c_23907])).
% 27.34/16.05  tff(c_30541, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30454, c_30426])).
% 27.34/16.05  tff(c_30542, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9'))), inference(splitRight, [status(thm)], [c_23910])).
% 27.34/16.05  tff(c_30658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30570, c_30542])).
% 27.34/16.05  tff(c_30659, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9'))), inference(splitRight, [status(thm)], [c_23908])).
% 27.34/16.05  tff(c_30905, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30816, c_30659])).
% 27.34/16.05  tff(c_30906, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_27407])).
% 27.34/16.05  tff(c_31322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30934, c_30906])).
% 27.34/16.05  tff(c_31323, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_27406])).
% 27.34/16.05  tff(c_31442, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31351, c_31323])).
% 27.34/16.05  tff(c_31443, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9'))), inference(splitRight, [status(thm)], [c_24781])).
% 27.34/16.05  tff(c_31563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31471, c_31443])).
% 27.34/16.05  tff(c_31564, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_9'))), inference(splitRight, [status(thm)], [c_24610])).
% 27.34/16.05  tff(c_31983, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31890, c_31564])).
% 27.34/16.05  tff(c_31984, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_29055])).
% 27.34/16.05  tff(c_32106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32012, c_31984])).
% 27.34/16.05  tff(c_32107, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_28409])).
% 27.34/16.05  tff(c_44009, plain, (![B_941, C_942]: (r2_hidden('#skF_3'('#skF_5', B_941, C_942), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_941, C_942)))), inference(resolution, [status(thm)], [c_32107, c_152])).
% 27.34/16.05  tff(c_44093, plain, (![B_941, C_942]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_941, C_942)))), inference(resolution, [status(thm)], [c_44009, c_2785])).
% 27.34/16.05  tff(c_44102, plain, (![B_941, C_942]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_941, C_942)))), inference(splitLeft, [status(thm)], [c_44093])).
% 27.34/16.05  tff(c_27585, plain, (![B_763, C_764]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_763, C_764)))), inference(resolution, [status(thm)], [c_27526, c_6231])).
% 27.34/16.05  tff(c_34812, plain, (![B_763, C_764]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_763, C_764)))), inference(splitLeft, [status(thm)], [c_27585])).
% 27.34/16.05  tff(c_29054, plain, (![B_781, C_782]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_781, C_782)))), inference(resolution, [status(thm)], [c_28996, c_6232])).
% 27.34/16.05  tff(c_34684, plain, (![B_781, C_782]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_781, C_782)))), inference(splitLeft, [status(thm)], [c_29054])).
% 27.34/16.05  tff(c_28408, plain, (![B_773, C_774]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_773, C_774)))), inference(resolution, [status(thm)], [c_28350, c_6232])).
% 27.34/16.05  tff(c_34048, plain, (![B_773, C_774]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_773, C_774)))), inference(splitLeft, [status(thm)], [c_28408])).
% 27.34/16.05  tff(c_27584, plain, (![B_763, C_764]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_763, C_764)))), inference(resolution, [status(thm)], [c_27526, c_6232])).
% 27.34/16.05  tff(c_33606, plain, (![B_763, C_764]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_763, C_764)))), inference(splitLeft, [status(thm)], [c_27584])).
% 27.34/16.05  tff(c_28229, plain, (![B_771, C_772]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_771, C_772)))), inference(resolution, [status(thm)], [c_28170, c_6231])).
% 27.34/16.05  tff(c_33481, plain, (![B_771, C_772]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_771, C_772)))), inference(splitLeft, [status(thm)], [c_28229])).
% 27.34/16.05  tff(c_28228, plain, (![B_771, C_772]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_771, C_772)))), inference(resolution, [status(thm)], [c_28170, c_6232])).
% 27.34/16.05  tff(c_32135, plain, (![B_771, C_772]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_771, C_772)))), inference(splitLeft, [status(thm)], [c_28228])).
% 27.34/16.05  tff(c_32230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32135, c_32107])).
% 27.34/16.05  tff(c_32231, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_28228])).
% 27.34/16.05  tff(c_33577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33481, c_32231])).
% 27.34/16.05  tff(c_33578, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_28229])).
% 27.34/16.05  tff(c_33703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33606, c_33578])).
% 27.34/16.05  tff(c_33704, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_27584])).
% 27.34/16.05  tff(c_34146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34048, c_33704])).
% 27.34/16.05  tff(c_34147, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_28408])).
% 27.34/16.05  tff(c_34783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34684, c_34147])).
% 27.34/16.05  tff(c_34784, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_29054])).
% 27.34/16.05  tff(c_34912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34812, c_34784])).
% 27.34/16.05  tff(c_34913, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_27585])).
% 27.34/16.05  tff(c_42859, plain, (![B_931, C_932]: (r2_hidden('#skF_3'('#skF_5', B_931, C_932), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_931, C_932)))), inference(resolution, [status(thm)], [c_34913, c_152])).
% 27.34/16.05  tff(c_42940, plain, (![B_931, C_932]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_931, C_932)))), inference(resolution, [status(thm)], [c_42859, c_2785])).
% 27.34/16.05  tff(c_43859, plain, (![B_931, C_932]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_931, C_932)))), inference(splitLeft, [status(thm)], [c_42940])).
% 27.34/16.05  tff(c_42274, plain, (![B_924, C_925]: (r2_hidden('#skF_3'('#skF_5', B_924, C_925), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_924, C_925)))), inference(resolution, [status(thm)], [c_33578, c_152])).
% 27.34/16.05  tff(c_42355, plain, (![B_924, C_925]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_924, C_925)))), inference(resolution, [status(thm)], [c_42274, c_2785])).
% 27.34/16.05  tff(c_42364, plain, (![B_924, C_925]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_924, C_925)))), inference(splitLeft, [status(thm)], [c_42355])).
% 27.34/16.05  tff(c_41369, plain, (![B_915, C_916]: (r2_hidden('#skF_3'('#skF_5', B_915, C_916), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_915, C_916)))), inference(resolution, [status(thm)], [c_32231, c_152])).
% 27.34/16.05  tff(c_41447, plain, (![B_915, C_916]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_915, C_916)))), inference(resolution, [status(thm)], [c_41369, c_2785])).
% 27.34/16.05  tff(c_42129, plain, (![B_915, C_916]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_915, C_916)))), inference(splitLeft, [status(thm)], [c_41447])).
% 27.34/16.05  tff(c_40797, plain, (![B_908, C_909]: (r2_hidden('#skF_3'('#skF_5', B_908, C_909), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_908, C_909)))), inference(resolution, [status(thm)], [c_34784, c_152])).
% 27.34/16.05  tff(c_40875, plain, (![B_908, C_909]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_908, C_909)))), inference(resolution, [status(thm)], [c_40797, c_2785])).
% 27.34/16.05  tff(c_40884, plain, (![B_908, C_909]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_908, C_909)))), inference(splitLeft, [status(thm)], [c_40875])).
% 27.34/16.05  tff(c_39903, plain, (![B_899, C_900]: (r2_hidden('#skF_3'('#skF_5', B_899, C_900), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_899, C_900)))), inference(resolution, [status(thm)], [c_31984, c_152])).
% 27.34/16.05  tff(c_39978, plain, (![B_899, C_900]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_899, C_900)))), inference(resolution, [status(thm)], [c_39903, c_2785])).
% 27.34/16.05  tff(c_40654, plain, (![B_899, C_900]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_899, C_900)))), inference(splitLeft, [status(thm)], [c_39978])).
% 27.34/16.05  tff(c_39677, plain, (![B_897, C_898]: (r2_hidden('#skF_3'('#skF_5', B_897, C_898), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_897, C_898)))), inference(resolution, [status(thm)], [c_34147, c_152])).
% 27.34/16.05  tff(c_39752, plain, (![B_897, C_898]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_897, C_898)))), inference(resolution, [status(thm)], [c_39677, c_2785])).
% 27.34/16.05  tff(c_39761, plain, (![B_897, C_898]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_897, C_898)))), inference(splitLeft, [status(thm)], [c_39752])).
% 27.34/16.05  tff(c_38939, plain, (![B_889, C_890]: (r2_hidden('#skF_3'('#skF_5', B_889, C_890), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_889, C_890)))), inference(resolution, [status(thm)], [c_33704, c_152])).
% 27.34/16.05  tff(c_39014, plain, (![B_889, C_890]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_889, C_890)))), inference(resolution, [status(thm)], [c_38939, c_2785])).
% 27.34/16.05  tff(c_39536, plain, (![B_889, C_890]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_889, C_890)))), inference(splitLeft, [status(thm)], [c_39014])).
% 27.34/16.05  tff(c_38715, plain, (![B_887, C_888]: (r2_hidden('#skF_3'('#skF_5', B_887, C_888), k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_887, C_888)))), inference(resolution, [status(thm)], [c_31443, c_152])).
% 27.34/16.05  tff(c_38790, plain, (![B_887, C_888]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_887, C_888)))), inference(resolution, [status(thm)], [c_38715, c_2785])).
% 27.34/16.05  tff(c_38799, plain, (![B_887, C_888]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_887, C_888)))), inference(splitLeft, [status(thm)], [c_38790])).
% 27.34/16.05  tff(c_38492, plain, (![B_885, C_886]: (r2_hidden('#skF_3'('#skF_5', B_885, C_886), k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_885, C_886)))), inference(resolution, [status(thm)], [c_31564, c_152])).
% 27.34/16.05  tff(c_38567, plain, (![B_885, C_886]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_885, C_886)))), inference(resolution, [status(thm)], [c_38492, c_2785])).
% 27.34/16.05  tff(c_38576, plain, (![B_885, C_886]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_885, C_886)))), inference(splitLeft, [status(thm)], [c_38567])).
% 27.34/16.05  tff(c_37945, plain, (![B_878, C_879]: (r2_hidden('#skF_3'('#skF_5', B_878, C_879), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_878, C_879)))), inference(resolution, [status(thm)], [c_31323, c_152])).
% 27.34/16.05  tff(c_38020, plain, (![B_878, C_879]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_878, C_879)))), inference(resolution, [status(thm)], [c_37945, c_2785])).
% 27.34/16.05  tff(c_38029, plain, (![B_878, C_879]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_878, C_879)))), inference(splitLeft, [status(thm)], [c_38020])).
% 27.34/16.05  tff(c_37584, plain, (![B_870, C_871]: (r2_hidden('#skF_3'('#skF_5', B_870, C_871), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_870, C_871)))), inference(resolution, [status(thm)], [c_30906, c_152])).
% 27.34/16.05  tff(c_37659, plain, (![B_870, C_871]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_870, C_871)))), inference(resolution, [status(thm)], [c_37584, c_2785])).
% 27.34/16.05  tff(c_37808, plain, (![B_870, C_871]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_870, C_871)))), inference(splitLeft, [status(thm)], [c_37659])).
% 27.34/16.05  tff(c_37364, plain, (![B_868, C_869]: (r2_hidden('#skF_3'('#skF_5', B_868, C_869), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_868, C_869)))), inference(resolution, [status(thm)], [c_30659, c_152])).
% 27.34/16.05  tff(c_37439, plain, (![B_868, C_869]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_868, C_869)))), inference(resolution, [status(thm)], [c_37364, c_2785])).
% 27.34/16.05  tff(c_37448, plain, (![B_868, C_869]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_868, C_869)))), inference(splitLeft, [status(thm)], [c_37439])).
% 27.34/16.05  tff(c_36313, plain, (![B_858, C_859]: (r2_hidden('#skF_3'('#skF_5', B_858, C_859), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_858, C_859)))), inference(resolution, [status(thm)], [c_30542, c_152])).
% 27.34/16.05  tff(c_36385, plain, (![B_858, C_859]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_858, C_859)))), inference(resolution, [status(thm)], [c_36313, c_2785])).
% 27.34/16.05  tff(c_37229, plain, (![B_858, C_859]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_858, C_859)))), inference(splitLeft, [status(thm)], [c_36385])).
% 27.34/16.05  tff(c_35782, plain, (![B_851, C_852]: (r2_hidden('#skF_3'('#skF_5', B_851, C_852), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_851, C_852)))), inference(resolution, [status(thm)], [c_30426, c_152])).
% 27.34/16.05  tff(c_35854, plain, (![B_851, C_852]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_851, C_852)))), inference(resolution, [status(thm)], [c_35782, c_2785])).
% 27.34/16.05  tff(c_35863, plain, (![B_851, C_852]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_851, C_852)))), inference(splitLeft, [status(thm)], [c_35854])).
% 27.34/16.05  tff(c_34941, plain, (![B_842, C_843]: (r2_hidden('#skF_3'('#skF_5', B_842, C_843), k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), k3_xboole_0('#skF_6', '#skF_8'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_842, C_843)))), inference(resolution, [status(thm)], [c_29566, c_152])).
% 27.34/16.05  tff(c_35010, plain, (![B_842, C_843]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_842, C_843)))), inference(resolution, [status(thm)], [c_34941, c_2785])).
% 27.34/16.05  tff(c_35652, plain, (![B_842, C_843]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_842, C_843)))), inference(splitLeft, [status(thm)], [c_35010])).
% 27.34/16.05  tff(c_35753, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35652, c_34913])).
% 27.34/16.05  tff(c_35754, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_35010])).
% 27.34/16.05  tff(c_36284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35863, c_35754])).
% 27.34/16.05  tff(c_36285, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_35854])).
% 27.34/16.05  tff(c_37332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37229, c_36285])).
% 27.34/16.05  tff(c_37333, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_36385])).
% 27.34/16.05  tff(c_37552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37448, c_37333])).
% 27.34/16.05  tff(c_37553, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_37439])).
% 27.34/16.05  tff(c_37913, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37808, c_37553])).
% 27.34/16.05  tff(c_37914, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_37659])).
% 27.34/16.05  tff(c_38460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38029, c_37914])).
% 27.34/16.05  tff(c_38461, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_38020])).
% 27.34/16.05  tff(c_38683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38576, c_38461])).
% 27.34/16.05  tff(c_38684, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_38567])).
% 27.34/16.05  tff(c_38907, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38799, c_38684])).
% 27.34/16.05  tff(c_38908, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), k3_xboole_0('#skF_6', '#skF_8')), '#skF_7'))), inference(splitRight, [status(thm)], [c_38790])).
% 27.34/16.05  tff(c_39645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39536, c_38908])).
% 27.34/16.05  tff(c_39646, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_39014])).
% 27.34/16.05  tff(c_39871, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39761, c_39646])).
% 27.34/16.05  tff(c_39872, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_39752])).
% 27.34/16.05  tff(c_40765, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40654, c_39872])).
% 27.34/16.05  tff(c_40766, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_39978])).
% 27.34/16.05  tff(c_41337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40884, c_40766])).
% 27.34/16.05  tff(c_41338, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_40875])).
% 27.34/16.05  tff(c_42242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42129, c_41338])).
% 27.34/16.05  tff(c_42243, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_41447])).
% 27.34/16.05  tff(c_42827, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42364, c_42243])).
% 27.34/16.05  tff(c_42828, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_42355])).
% 27.34/16.05  tff(c_43974, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43859, c_42828])).
% 27.34/16.05  tff(c_43975, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', '#skF_8')), '#skF_8'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_42940])).
% 27.34/16.05  tff(c_44218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44102, c_43975])).
% 27.34/16.05  tff(c_44219, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_6', '#skF_8')), '#skF_6'), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_44093])).
% 27.34/16.05  tff(c_44700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44582, c_44219])).
% 27.34/16.05  tff(c_44701, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_9'))), inference(splitRight, [status(thm)], [c_44421])).
% 27.34/16.05  tff(c_45244, plain, (![B_957, C_958]: (r2_hidden('#skF_3'('#skF_5', B_957, C_958), k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_957, C_958)))), inference(resolution, [status(thm)], [c_44701, c_152])).
% 27.34/16.05  tff(c_6312, plain, (![A_1, B_374, C_375]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(A_1, k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_3'('#skF_5', B_374, C_375), A_1) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_374, C_375)))), inference(resolution, [status(thm)], [c_6282, c_2835])).
% 27.34/16.05  tff(c_45309, plain, (![B_957, C_958]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_957, C_958)))), inference(resolution, [status(thm)], [c_45244, c_6312])).
% 27.34/16.05  tff(c_52820, plain, (![B_957, C_958]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_957, C_958)))), inference(splitLeft, [status(thm)], [c_45309])).
% 27.34/16.05  tff(c_44415, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_6872, c_44253])).
% 27.34/16.05  tff(c_52432, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_44415])).
% 27.34/16.05  tff(c_44414, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_7129, c_44253])).
% 27.34/16.05  tff(c_51266, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_44414])).
% 27.34/16.05  tff(c_44417, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_7098, c_44253])).
% 27.34/16.05  tff(c_50880, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_44417])).
% 27.34/16.05  tff(c_44416, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_6572, c_44253])).
% 27.34/16.05  tff(c_50713, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_44416])).
% 27.34/16.05  tff(c_44422, plain, (![B_74, C_76]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_74, C_76)))), inference(resolution, [status(thm)], [c_309, c_44253])).
% 27.34/16.05  tff(c_44735, plain, (![B_74, C_76]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_74, C_76)))), inference(splitLeft, [status(thm)], [c_44422])).
% 27.34/16.05  tff(c_44854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44735, c_44701])).
% 27.34/16.05  tff(c_44855, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_9'))), inference(splitRight, [status(thm)], [c_44422])).
% 27.34/16.05  tff(c_45495, plain, (![B_959, C_960]: (r2_hidden('#skF_3'('#skF_5', B_959, C_960), k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_959, C_960)))), inference(resolution, [status(thm)], [c_44855, c_152])).
% 27.34/16.05  tff(c_45577, plain, (![B_959, C_960]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_959, C_960)))), inference(resolution, [status(thm)], [c_45495, c_6232])).
% 27.34/16.05  tff(c_46906, plain, (![B_959, C_960]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_959, C_960)))), inference(splitLeft, [status(thm)], [c_45577])).
% 27.34/16.05  tff(c_45327, plain, (![B_957, C_958]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_957, C_958)))), inference(resolution, [status(thm)], [c_45244, c_6231])).
% 27.34/16.05  tff(c_46221, plain, (![B_957, C_958]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_957, C_958)))), inference(splitLeft, [status(thm)], [c_45327])).
% 27.34/16.05  tff(c_45326, plain, (![B_957, C_958]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_957, C_958)))), inference(resolution, [status(thm)], [c_45244, c_6232])).
% 27.34/16.05  tff(c_46062, plain, (![B_957, C_958]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_957, C_958)))), inference(splitLeft, [status(thm)], [c_45326])).
% 27.34/16.05  tff(c_45578, plain, (![B_959, C_960]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_959, C_960)))), inference(resolution, [status(thm)], [c_45495, c_6231])).
% 27.34/16.05  tff(c_45904, plain, (![B_959, C_960]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_959, C_960)))), inference(splitLeft, [status(thm)], [c_45578])).
% 27.34/16.05  tff(c_44418, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_6599, c_44253])).
% 27.34/16.05  tff(c_45747, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_44418])).
% 27.34/16.05  tff(c_45582, plain, (![B_959, C_960]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_959, C_960)))), inference(resolution, [status(thm)], [c_45495, c_2785])).
% 27.34/16.05  tff(c_45591, plain, (![B_959, C_960]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_959, C_960)))), inference(splitLeft, [status(thm)], [c_45582])).
% 27.34/16.05  tff(c_45331, plain, (![B_957, C_958]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_957, C_958)))), inference(resolution, [status(thm)], [c_45244, c_2785])).
% 27.34/16.05  tff(c_45340, plain, (![B_957, C_958]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_957, C_958)))), inference(splitLeft, [status(thm)], [c_45331])).
% 27.34/16.05  tff(c_45460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45340, c_44855])).
% 27.34/16.05  tff(c_45461, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_7'))), inference(splitRight, [status(thm)], [c_45331])).
% 27.34/16.05  tff(c_45712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45591, c_45461])).
% 27.34/16.05  tff(c_45713, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_7'))), inference(splitRight, [status(thm)], [c_45582])).
% 27.34/16.05  tff(c_45869, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45747, c_45713])).
% 27.34/16.05  tff(c_45870, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9'))), inference(splitRight, [status(thm)], [c_44418])).
% 27.34/16.05  tff(c_46027, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45904, c_45870])).
% 27.34/16.05  tff(c_46028, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_45578])).
% 27.34/16.05  tff(c_46186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46062, c_46028])).
% 27.34/16.05  tff(c_46187, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_45326])).
% 27.34/16.05  tff(c_46871, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46221, c_46187])).
% 27.34/16.05  tff(c_46872, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_9'))), inference(splitRight, [status(thm)], [c_45327])).
% 27.34/16.05  tff(c_47032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46906, c_46872])).
% 27.34/16.05  tff(c_47033, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_45577])).
% 27.34/16.05  tff(c_49920, plain, (![B_994, C_995]: (r2_hidden('#skF_3'('#skF_5', B_994, C_995), k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_994, C_995)))), inference(resolution, [status(thm)], [c_47033, c_152])).
% 27.34/16.05  tff(c_50013, plain, (![B_994, C_995]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_994, C_995)))), inference(resolution, [status(thm)], [c_49920, c_2785])).
% 27.34/16.05  tff(c_50022, plain, (![B_994, C_995]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_994, C_995)))), inference(splitLeft, [status(thm)], [c_50013])).
% 27.34/16.05  tff(c_49509, plain, (![B_990, C_991]: (r2_hidden('#skF_3'('#skF_5', B_990, C_991), k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_990, C_991)))), inference(resolution, [status(thm)], [c_46028, c_152])).
% 27.34/16.05  tff(c_49602, plain, (![B_990, C_991]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_990, C_991)))), inference(resolution, [status(thm)], [c_49509, c_2785])).
% 27.34/16.05  tff(c_49611, plain, (![B_990, C_991]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_990, C_991)))), inference(splitLeft, [status(thm)], [c_49602])).
% 27.34/16.05  tff(c_48537, plain, (![B_981, C_982]: (r2_hidden('#skF_3'('#skF_5', B_981, C_982), k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_981, C_982)))), inference(resolution, [status(thm)], [c_46187, c_152])).
% 27.34/16.05  tff(c_48627, plain, (![B_981, C_982]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_981, C_982)))), inference(resolution, [status(thm)], [c_48537, c_2785])).
% 27.34/16.05  tff(c_48636, plain, (![B_981, C_982]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_981, C_982)))), inference(splitLeft, [status(thm)], [c_48627])).
% 27.34/16.05  tff(c_48028, plain, (![B_976, C_977]: (r2_hidden('#skF_3'('#skF_5', B_976, C_977), k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_976, C_977)))), inference(resolution, [status(thm)], [c_46872, c_152])).
% 27.34/16.05  tff(c_48118, plain, (![B_976, C_977]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_976, C_977)))), inference(resolution, [status(thm)], [c_48028, c_2785])).
% 27.34/16.05  tff(c_48127, plain, (![B_976, C_977]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_976, C_977)))), inference(splitLeft, [status(thm)], [c_48118])).
% 27.34/16.05  tff(c_47067, plain, (![B_967, C_968]: (r2_hidden('#skF_3'('#skF_5', B_967, C_968), k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_967, C_968)))), inference(resolution, [status(thm)], [c_45870, c_152])).
% 27.34/16.05  tff(c_47154, plain, (![B_967, C_968]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_967, C_968)))), inference(resolution, [status(thm)], [c_47067, c_2785])).
% 27.34/16.05  tff(c_47163, plain, (![B_967, C_968]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_967, C_968)))), inference(splitLeft, [status(thm)], [c_47154])).
% 27.34/16.05  tff(c_47290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47163, c_47033])).
% 27.34/16.05  tff(c_47291, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_7'))), inference(splitRight, [status(thm)], [c_47154])).
% 27.34/16.05  tff(c_48255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48127, c_47291])).
% 27.34/16.05  tff(c_48256, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_48118])).
% 27.34/16.05  tff(c_48765, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48636, c_48256])).
% 27.34/16.05  tff(c_48766, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_48627])).
% 27.34/16.05  tff(c_49741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49611, c_48766])).
% 27.34/16.05  tff(c_49742, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_6'), '#skF_7'))), inference(splitRight, [status(thm)], [c_49602])).
% 27.34/16.05  tff(c_50153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50022, c_49742])).
% 27.34/16.05  tff(c_50154, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_6')), '#skF_8'), '#skF_7'))), inference(splitRight, [status(thm)], [c_50013])).
% 27.34/16.05  tff(c_50845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50713, c_50154])).
% 27.34/16.05  tff(c_50846, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_6'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9'))), inference(splitRight, [status(thm)], [c_44416])).
% 27.34/16.05  tff(c_51231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50880, c_50846])).
% 27.34/16.05  tff(c_51232, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_8', '#skF_6'), '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9'))), inference(splitRight, [status(thm)], [c_44417])).
% 27.34/16.05  tff(c_52397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51266, c_51232])).
% 27.34/16.05  tff(c_52398, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_8'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9'))), inference(splitRight, [status(thm)], [c_44414])).
% 27.34/16.05  tff(c_52567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52432, c_52398])).
% 27.34/16.05  tff(c_52568, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_6', '#skF_8'), '#skF_6'), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9'))), inference(splitRight, [status(thm)], [c_44415])).
% 27.34/16.05  tff(c_52956, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52820, c_52568])).
% 27.34/16.05  tff(c_52957, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_6', k3_xboole_0('#skF_8', '#skF_6')), k3_xboole_0('#skF_8', '#skF_6')), '#skF_9'))), inference(splitRight, [status(thm)], [c_45309])).
% 27.34/16.05  tff(c_53153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53014, c_52957])).
% 27.34/16.05  tff(c_53154, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0('#skF_9', '#skF_7')))), inference(splitRight, [status(thm)], [c_53012])).
% 27.34/16.05  tff(c_155, plain, (![A_47, C_16, D_17, C_49, B_48]: (r2_hidden('#skF_4'(A_47, B_48, C_49), D_17) | ~r2_hidden(A_47, k2_zfmisc_1(C_16, D_17)) | ~r2_hidden(A_47, k2_zfmisc_1(B_48, C_49)))), inference(superposition, [status(thm), theory('equality')], [c_143, c_26])).
% 27.34/16.05  tff(c_53188, plain, (![B_1029, C_1030]: (r2_hidden('#skF_4'('#skF_5', B_1029, C_1030), k3_xboole_0('#skF_9', '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1029, C_1030)))), inference(resolution, [status(thm)], [c_53154, c_155])).
% 27.34/16.05  tff(c_52999, plain, (![A_1022, B_65, C_67]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(A_1022, '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_5', B_65, C_67), A_1022) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_65, C_67)))), inference(resolution, [status(thm)], [c_274, c_52991])).
% 27.34/16.05  tff(c_53247, plain, (![B_1029, C_1030]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1029, C_1030)))), inference(resolution, [status(thm)], [c_53188, c_52999])).
% 27.34/16.05  tff(c_53409, plain, (![B_1029, C_1030]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1029, C_1030)))), inference(splitLeft, [status(thm)], [c_53247])).
% 27.34/16.05  tff(c_53549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53409, c_53154])).
% 27.34/16.05  tff(c_53550, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7')))), inference(splitRight, [status(thm)], [c_53247])).
% 27.34/16.05  tff(c_53741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53599, c_53550])).
% 27.34/16.05  tff(c_53742, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0('#skF_7', '#skF_9')))), inference(splitRight, [status(thm)], [c_53595])).
% 27.34/16.05  tff(c_53776, plain, (![B_1038, C_1039]: (r2_hidden('#skF_4'('#skF_5', B_1038, C_1039), k3_xboole_0('#skF_7', '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1038, C_1039)))), inference(resolution, [status(thm)], [c_53742, c_155])).
% 27.34/16.05  tff(c_149, plain, (![A_47, C_16, D_17, C_49, B_48]: (r2_hidden(A_47, k2_zfmisc_1(C_16, D_17)) | ~r2_hidden('#skF_4'(A_47, B_48, C_49), D_17) | ~r2_hidden('#skF_3'(A_47, B_48, C_49), C_16) | ~r2_hidden(A_47, k2_zfmisc_1(B_48, C_49)))), inference(superposition, [status(thm), theory('equality')], [c_143, c_24])).
% 27.34/16.05  tff(c_63758, plain, (![C_1169, B_1170, C_1171]: (r2_hidden('#skF_5', k2_zfmisc_1(C_1169, k3_xboole_0('#skF_7', '#skF_9'))) | ~r2_hidden('#skF_3'('#skF_5', B_1170, C_1171), C_1169) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1170, C_1171)))), inference(resolution, [status(thm)], [c_53776, c_149])).
% 27.34/16.05  tff(c_63876, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1(k3_xboole_0('#skF_6', '#skF_8'), k3_xboole_0('#skF_7', '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_6599, c_63758])).
% 27.34/16.05  tff(c_63946, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(negUnitSimplification, [status(thm)], [c_30, c_63876])).
% 27.34/16.05  tff(c_53187, plain, (![B_48, C_49]: (r2_hidden('#skF_4'('#skF_5', B_48, C_49), k3_xboole_0('#skF_9', '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_53154, c_155])).
% 27.34/16.05  tff(c_53594, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_53187, c_53584])).
% 27.34/16.05  tff(c_53866, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_53594])).
% 27.34/16.05  tff(c_54143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53866, c_53742])).
% 27.34/16.05  tff(c_54144, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9')))), inference(splitRight, [status(thm)], [c_53594])).
% 27.34/16.05  tff(c_54177, plain, (![B_48, C_49]: (r2_hidden('#skF_4'('#skF_5', B_48, C_49), k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_54144, c_155])).
% 27.34/16.05  tff(c_54959, plain, (![A_1058, B_1059, B_1060, C_1061]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(A_1058, B_1059))) | ~r2_hidden('#skF_4'('#skF_5', B_1060, C_1061), B_1059) | ~r2_hidden('#skF_4'('#skF_5', B_1060, C_1061), A_1058) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1060, C_1061)))), inference(resolution, [status(thm)], [c_309, c_52602])).
% 27.34/16.05  tff(c_56840, plain, (![A_1073, B_1074, C_1075]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(A_1073, '#skF_9'))) | ~r2_hidden('#skF_4'('#skF_5', B_1074, C_1075), A_1073) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1074, C_1075)))), inference(resolution, [status(thm)], [c_273, c_54959])).
% 27.34/16.05  tff(c_56860, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_54177, c_56840])).
% 27.34/16.05  tff(c_60710, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_56860])).
% 27.34/16.05  tff(c_53838, plain, (![B_1038, C_1039]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1038, C_1039)))), inference(resolution, [status(thm)], [c_53776, c_52999])).
% 27.34/16.05  tff(c_54375, plain, (![B_1038, C_1039]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1038, C_1039)))), inference(splitLeft, [status(thm)], [c_53838])).
% 27.34/16.05  tff(c_53000, plain, (![A_1022, B_65, C_67]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(A_1022, '#skF_9'))) | ~r2_hidden('#skF_4'('#skF_5', B_65, C_67), A_1022) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_65, C_67)))), inference(resolution, [status(thm)], [c_273, c_52991])).
% 27.34/16.05  tff(c_53837, plain, (![B_1038, C_1039]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1038, C_1039)))), inference(resolution, [status(thm)], [c_53776, c_53000])).
% 27.34/16.05  tff(c_54178, plain, (![B_1038, C_1039]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1038, C_1039)))), inference(splitLeft, [status(thm)], [c_53837])).
% 27.34/16.05  tff(c_54340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54178, c_54144])).
% 27.34/16.05  tff(c_54341, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9')))), inference(splitRight, [status(thm)], [c_53837])).
% 27.34/16.05  tff(c_54520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54375, c_54341])).
% 27.34/16.05  tff(c_54521, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7')))), inference(splitRight, [status(thm)], [c_53838])).
% 27.34/16.05  tff(c_54554, plain, (![B_48, C_49]: (r2_hidden('#skF_4'('#skF_5', B_48, C_49), k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_54521, c_155])).
% 27.34/16.05  tff(c_56029, plain, (![A_1067, B_1068, C_1069]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(A_1067, '#skF_7'))) | ~r2_hidden('#skF_4'('#skF_5', B_1068, C_1069), A_1067) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1068, C_1069)))), inference(resolution, [status(thm)], [c_274, c_54959])).
% 27.34/16.05  tff(c_56051, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_54554, c_56029])).
% 27.34/16.05  tff(c_60155, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_56051])).
% 27.34/16.05  tff(c_54374, plain, (![B_48, C_49]: (r2_hidden('#skF_4'('#skF_5', B_48, C_49), k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_54341, c_155])).
% 27.34/16.05  tff(c_56050, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_54374, c_56029])).
% 27.34/16.05  tff(c_59786, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_56050])).
% 27.34/16.05  tff(c_56049, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_54177, c_56029])).
% 27.34/16.05  tff(c_59583, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_56049])).
% 27.34/16.05  tff(c_54985, plain, (![B_1062, C_1063]: (r2_hidden('#skF_4'('#skF_5', B_1062, C_1063), k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1062, C_1063)))), inference(resolution, [status(thm)], [c_54144, c_155])).
% 27.34/16.05  tff(c_55049, plain, (![B_1062, C_1063]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1062, C_1063)))), inference(resolution, [status(thm)], [c_54985, c_53000])).
% 27.34/16.05  tff(c_59216, plain, (![B_1062, C_1063]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1062, C_1063)))), inference(splitLeft, [status(thm)], [c_55049])).
% 27.34/16.05  tff(c_56861, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_54374, c_56840])).
% 27.34/16.05  tff(c_59016, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_56861])).
% 27.34/16.05  tff(c_53583, plain, (![B_48, C_49]: (r2_hidden('#skF_4'('#skF_5', B_48, C_49), k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_53550, c_155])).
% 27.34/16.05  tff(c_56863, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_53583, c_56840])).
% 27.34/16.05  tff(c_58808, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_56863])).
% 27.34/16.05  tff(c_55050, plain, (![B_1062, C_1063]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1062, C_1063)))), inference(resolution, [status(thm)], [c_54985, c_52999])).
% 27.34/16.05  tff(c_58444, plain, (![B_1062, C_1063]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1062, C_1063)))), inference(splitLeft, [status(thm)], [c_55050])).
% 27.34/16.05  tff(c_56862, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_54554, c_56840])).
% 27.34/16.05  tff(c_58247, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_56862])).
% 27.34/16.05  tff(c_54689, plain, (![B_1052, C_1053]: (r2_hidden('#skF_4'('#skF_5', B_1052, C_1053), k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1052, C_1053)))), inference(resolution, [status(thm)], [c_53550, c_155])).
% 27.34/16.05  tff(c_54751, plain, (![B_1052, C_1053]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1052, C_1053)))), inference(resolution, [status(thm)], [c_54689, c_52999])).
% 27.34/16.05  tff(c_58030, plain, (![B_1052, C_1053]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1052, C_1053)))), inference(splitLeft, [status(thm)], [c_54751])).
% 27.34/16.05  tff(c_56052, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_53583, c_56029])).
% 27.34/16.05  tff(c_57669, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_56052])).
% 27.34/16.05  tff(c_56865, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_53187, c_56840])).
% 27.34/16.05  tff(c_57454, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_56865])).
% 27.34/16.05  tff(c_53775, plain, (![B_48, C_49]: (r2_hidden('#skF_4'('#skF_5', B_48, C_49), k3_xboole_0('#skF_7', '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_53742, c_155])).
% 27.34/16.05  tff(c_56864, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_53775, c_56840])).
% 27.34/16.05  tff(c_57095, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_56864])).
% 27.34/16.05  tff(c_56866, plain, (![B_65, C_67]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0('#skF_7', '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_65, C_67)))), inference(resolution, [status(thm)], [c_274, c_56840])).
% 27.34/16.05  tff(c_56903, plain, (![B_65, C_67]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_65, C_67)))), inference(splitLeft, [status(thm)], [c_56866])).
% 27.34/16.05  tff(c_56054, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_53187, c_56029])).
% 27.34/16.05  tff(c_56683, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_56054])).
% 27.34/16.05  tff(c_56053, plain, (![B_48, C_49]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_53775, c_56029])).
% 27.34/16.05  tff(c_56247, plain, (![B_48, C_49]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(splitLeft, [status(thm)], [c_56053])).
% 27.34/16.05  tff(c_56057, plain, (![B_65, C_67]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0('#skF_9', '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_65, C_67)))), inference(resolution, [status(thm)], [c_273, c_56029])).
% 27.34/16.05  tff(c_56059, plain, (![B_65, C_67]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_65, C_67)))), inference(splitLeft, [status(thm)], [c_56057])).
% 27.34/16.05  tff(c_54779, plain, (![B_1054, C_1055]: (r2_hidden('#skF_4'('#skF_5', B_1054, C_1055), k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1054, C_1055)))), inference(resolution, [status(thm)], [c_54521, c_155])).
% 27.34/16.05  tff(c_54840, plain, (![B_1054, C_1055]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1054, C_1055)))), inference(resolution, [status(thm)], [c_54779, c_53000])).
% 27.34/16.05  tff(c_55843, plain, (![B_1054, C_1055]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1054, C_1055)))), inference(splitLeft, [status(thm)], [c_54840])).
% 27.34/16.05  tff(c_54841, plain, (![B_1054, C_1055]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1054, C_1055)))), inference(resolution, [status(thm)], [c_54779, c_52999])).
% 27.34/16.05  tff(c_55658, plain, (![B_1054, C_1055]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1054, C_1055)))), inference(splitLeft, [status(thm)], [c_54841])).
% 27.34/16.05  tff(c_54869, plain, (![B_1056, C_1057]: (r2_hidden('#skF_4'('#skF_5', B_1056, C_1057), k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9')) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1056, C_1057)))), inference(resolution, [status(thm)], [c_54341, c_155])).
% 27.34/16.05  tff(c_54930, plain, (![B_1056, C_1057]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1056, C_1057)))), inference(resolution, [status(thm)], [c_54869, c_53000])).
% 27.34/16.05  tff(c_55443, plain, (![B_1056, C_1057]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1056, C_1057)))), inference(splitLeft, [status(thm)], [c_54930])).
% 27.34/16.05  tff(c_54931, plain, (![B_1056, C_1057]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9'), '#skF_7'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1056, C_1057)))), inference(resolution, [status(thm)], [c_54869, c_52999])).
% 27.34/16.05  tff(c_55260, plain, (![B_1056, C_1057]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1056, C_1057)))), inference(splitLeft, [status(thm)], [c_54931])).
% 27.34/16.05  tff(c_54750, plain, (![B_1052, C_1053]: (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7'), '#skF_9'))) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_1052, C_1053)))), inference(resolution, [status(thm)], [c_54689, c_53000])).
% 27.34/16.05  tff(c_55078, plain, (![B_1052, C_1053]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_1052, C_1053)))), inference(splitLeft, [status(thm)], [c_54750])).
% 27.34/16.05  tff(c_55225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55078, c_54521])).
% 27.34/16.05  tff(c_55226, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7'), '#skF_9')))), inference(splitRight, [status(thm)], [c_54750])).
% 27.34/16.05  tff(c_55408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55260, c_55226])).
% 27.34/16.05  tff(c_55409, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9'), '#skF_7')))), inference(splitRight, [status(thm)], [c_54931])).
% 27.34/16.05  tff(c_55623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55443, c_55409])).
% 27.34/16.05  tff(c_55624, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9'), '#skF_9')))), inference(splitRight, [status(thm)], [c_54930])).
% 27.34/16.05  tff(c_55808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55658, c_55624])).
% 27.34/16.05  tff(c_55809, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7'), '#skF_7')))), inference(splitRight, [status(thm)], [c_54841])).
% 27.34/16.05  tff(c_55994, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55843, c_55809])).
% 27.34/16.05  tff(c_55995, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7'), '#skF_9')))), inference(splitRight, [status(thm)], [c_54840])).
% 27.34/16.05  tff(c_56212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56059, c_55995])).
% 27.34/16.05  tff(c_56213, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0('#skF_9', '#skF_7')))), inference(splitRight, [status(thm)], [c_56057])).
% 27.34/16.05  tff(c_56401, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56247, c_56213])).
% 27.34/16.05  tff(c_56402, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7')))), inference(splitRight, [status(thm)], [c_56053])).
% 27.34/16.05  tff(c_56838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56683, c_56402])).
% 27.34/16.05  tff(c_56839, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7')))), inference(splitRight, [status(thm)], [c_56054])).
% 27.34/16.05  tff(c_57060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56903, c_56839])).
% 27.34/16.05  tff(c_57061, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0('#skF_7', '#skF_9')))), inference(splitRight, [status(thm)], [c_56866])).
% 27.34/16.05  tff(c_57419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57095, c_57061])).
% 27.34/16.05  tff(c_57420, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9')))), inference(splitRight, [status(thm)], [c_56864])).
% 27.34/16.05  tff(c_57634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57454, c_57420])).
% 27.34/16.05  tff(c_57635, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9')))), inference(splitRight, [status(thm)], [c_56865])).
% 27.34/16.05  tff(c_57829, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57669, c_57635])).
% 27.34/16.05  tff(c_57830, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7'), '#skF_7')))), inference(splitRight, [status(thm)], [c_56052])).
% 27.34/16.05  tff(c_58191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58030, c_57830])).
% 27.34/16.05  tff(c_58192, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7'), '#skF_7')))), inference(splitRight, [status(thm)], [c_54751])).
% 27.34/16.05  tff(c_58409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58247, c_58192])).
% 27.34/16.05  tff(c_58410, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7'), '#skF_9')))), inference(splitRight, [status(thm)], [c_56862])).
% 27.34/16.05  tff(c_58607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58444, c_58410])).
% 27.34/16.05  tff(c_58608, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9'), '#skF_7')))), inference(splitRight, [status(thm)], [c_55050])).
% 27.34/16.05  tff(c_58972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58808, c_58608])).
% 27.34/16.05  tff(c_58973, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_7'), '#skF_9')))), inference(splitRight, [status(thm)], [c_56863])).
% 27.34/16.05  tff(c_59181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59016, c_58973])).
% 27.34/16.05  tff(c_59182, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9'), '#skF_9')))), inference(splitRight, [status(thm)], [c_56861])).
% 27.34/16.05  tff(c_59548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59216, c_59182])).
% 27.34/16.05  tff(c_59549, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_6', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9'), '#skF_9')))), inference(splitRight, [status(thm)], [c_55049])).
% 27.34/16.05  tff(c_59751, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59583, c_59549])).
% 27.34/16.05  tff(c_59752, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9'), '#skF_7')))), inference(splitRight, [status(thm)], [c_56049])).
% 27.34/16.05  tff(c_59954, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59786, c_59752])).
% 27.34/16.05  tff(c_59955, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_9'), '#skF_7')))), inference(splitRight, [status(thm)], [c_56050])).
% 27.34/16.05  tff(c_60324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60155, c_59955])).
% 27.34/16.05  tff(c_60325, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_7', '#skF_9'), '#skF_7'), '#skF_7')))), inference(splitRight, [status(thm)], [c_56051])).
% 27.34/16.05  tff(c_61046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60710, c_60325])).
% 27.34/16.05  tff(c_61047, plain, (r2_hidden('#skF_5', k2_zfmisc_1('#skF_8', k3_xboole_0(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_7'), '#skF_9'), '#skF_9')))), inference(splitRight, [status(thm)], [c_56860])).
% 27.34/16.05  tff(c_64124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63946, c_61047])).
% 27.34/16.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.34/16.05  
% 27.34/16.05  Inference rules
% 27.34/16.05  ----------------------
% 27.34/16.05  #Ref     : 0
% 27.34/16.05  #Sup     : 13495
% 27.34/16.05  #Fact    : 0
% 27.34/16.05  #Define  : 0
% 27.34/16.05  #Split   : 158
% 27.34/16.05  #Chain   : 0
% 27.34/16.05  #Close   : 0
% 27.34/16.05  
% 27.34/16.05  Ordering : KBO
% 27.34/16.05  
% 27.34/16.05  Simplification rules
% 27.34/16.05  ----------------------
% 27.34/16.05  #Subsume      : 10096
% 27.34/16.05  #Demod        : 1504
% 27.34/16.05  #Tautology    : 258
% 27.34/16.05  #SimpNegUnit  : 13799
% 27.34/16.05  #BackRed      : 12714
% 27.34/16.05  
% 27.34/16.05  #Partial instantiations: 0
% 27.34/16.05  #Strategies tried      : 1
% 27.34/16.05  
% 27.34/16.05  Timing (in seconds)
% 27.34/16.05  ----------------------
% 27.34/16.06  Preprocessing        : 0.29
% 27.34/16.06  Parsing              : 0.15
% 27.34/16.06  CNF conversion       : 0.02
% 27.34/16.06  Main loop            : 14.82
% 27.34/16.06  Inferencing          : 2.03
% 27.34/16.06  Reduction            : 4.97
% 27.34/16.06  Demodulation         : 4.11
% 27.34/16.06  BG Simplification    : 0.40
% 27.34/16.06  Subsumption          : 6.41
% 27.34/16.06  Abstraction          : 0.68
% 27.34/16.06  MUC search           : 0.00
% 27.34/16.06  Cooper               : 0.00
% 27.34/16.06  Total                : 15.32
% 27.34/16.06  Index Insertion      : 0.00
% 27.34/16.06  Index Deletion       : 0.00
% 27.34/16.06  Index Matching       : 0.00
% 27.34/16.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
