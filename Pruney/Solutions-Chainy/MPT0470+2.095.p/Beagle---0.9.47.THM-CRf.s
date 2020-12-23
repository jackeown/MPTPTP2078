%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:14 EST 2020

% Result     : Theorem 24.79s
% Output     : CNFRefutation 24.79s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 190 expanded)
%              Number of leaves         :   29 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          :  136 ( 394 expanded)
%              Number of equality atoms :   25 (  76 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_5 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_40,plain,
    ( k5_relat_1('#skF_9',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    k5_relat_1(k1_xboole_0,'#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_42,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_47,plain,(
    ! [B_132,A_133] :
      ( v1_relat_1(B_132)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_133))
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_51,plain,(
    ! [A_5] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_10,c_47])).

tff(c_52,plain,(
    ! [A_5] : ~ v1_relat_1(A_5) ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_55,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42])).

tff(c_56,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_295,plain,(
    ! [A_204,B_205,C_206] :
      ( r2_hidden(k4_tarski('#skF_4'(A_204,B_205,C_206),'#skF_6'(A_204,B_205,C_206)),A_204)
      | r2_hidden(k4_tarski('#skF_7'(A_204,B_205,C_206),'#skF_8'(A_204,B_205,C_206)),C_206)
      | k5_relat_1(A_204,B_205) = C_206
      | ~ v1_relat_1(C_206)
      | ~ v1_relat_1(B_205)
      | ~ v1_relat_1(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    ! [C_27,D_28,B_22,A_12] :
      ( r2_hidden(k4_tarski(C_27,D_28),B_22)
      | ~ r2_hidden(k4_tarski(C_27,D_28),A_12)
      | ~ r1_tarski(A_12,B_22)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1361,plain,(
    ! [A_335,B_336,C_337,B_338] :
      ( r2_hidden(k4_tarski('#skF_7'(A_335,B_336,C_337),'#skF_8'(A_335,B_336,C_337)),B_338)
      | ~ r1_tarski(C_337,B_338)
      | r2_hidden(k4_tarski('#skF_4'(A_335,B_336,C_337),'#skF_6'(A_335,B_336,C_337)),A_335)
      | k5_relat_1(A_335,B_336) = C_337
      | ~ v1_relat_1(C_337)
      | ~ v1_relat_1(B_336)
      | ~ v1_relat_1(A_335) ) ),
    inference(resolution,[status(thm)],[c_295,c_16])).

tff(c_6,plain,(
    ! [C_4,B_3] : ~ r2_hidden(C_4,k4_xboole_0(B_3,k1_tarski(C_4))) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_40393,plain,(
    ! [C_1485,B_1486,A_1487,B_1488] :
      ( ~ r1_tarski(C_1485,k4_xboole_0(B_1486,k1_tarski(k4_tarski('#skF_7'(A_1487,B_1488,C_1485),'#skF_8'(A_1487,B_1488,C_1485)))))
      | r2_hidden(k4_tarski('#skF_4'(A_1487,B_1488,C_1485),'#skF_6'(A_1487,B_1488,C_1485)),A_1487)
      | k5_relat_1(A_1487,B_1488) = C_1485
      | ~ v1_relat_1(C_1485)
      | ~ v1_relat_1(B_1488)
      | ~ v1_relat_1(A_1487) ) ),
    inference(resolution,[status(thm)],[c_1361,c_6])).

tff(c_40601,plain,(
    ! [A_1487,B_1488] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1487,B_1488,k1_xboole_0),'#skF_6'(A_1487,B_1488,k1_xboole_0)),A_1487)
      | k5_relat_1(A_1487,B_1488) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_1488)
      | ~ v1_relat_1(A_1487) ) ),
    inference(resolution,[status(thm)],[c_2,c_40393])).

tff(c_40673,plain,(
    ! [A_1489,B_1490] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1489,B_1490,k1_xboole_0),'#skF_6'(A_1489,B_1490,k1_xboole_0)),A_1489)
      | k5_relat_1(A_1489,B_1490) = k1_xboole_0
      | ~ v1_relat_1(B_1490)
      | ~ v1_relat_1(A_1489) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_40601])).

tff(c_41179,plain,(
    ! [A_1503,B_1504,B_1505] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1503,B_1504,k1_xboole_0),'#skF_6'(A_1503,B_1504,k1_xboole_0)),B_1505)
      | ~ r1_tarski(A_1503,B_1505)
      | k5_relat_1(A_1503,B_1504) = k1_xboole_0
      | ~ v1_relat_1(B_1504)
      | ~ v1_relat_1(A_1503) ) ),
    inference(resolution,[status(thm)],[c_40673,c_16])).

tff(c_41534,plain,(
    ! [A_1515,B_1516,B_1517] :
      ( ~ r1_tarski(A_1515,k4_xboole_0(B_1516,k1_tarski(k4_tarski('#skF_4'(A_1515,B_1517,k1_xboole_0),'#skF_6'(A_1515,B_1517,k1_xboole_0)))))
      | k5_relat_1(A_1515,B_1517) = k1_xboole_0
      | ~ v1_relat_1(B_1517)
      | ~ v1_relat_1(A_1515) ) ),
    inference(resolution,[status(thm)],[c_41179,c_6])).

tff(c_41812,plain,(
    ! [B_1517] :
      ( k5_relat_1(k1_xboole_0,B_1517) = k1_xboole_0
      | ~ v1_relat_1(B_1517)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_41534])).

tff(c_41884,plain,(
    ! [B_1518] :
      ( k5_relat_1(k1_xboole_0,B_1518) = k1_xboole_0
      | ~ v1_relat_1(B_1518) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_41812])).

tff(c_41899,plain,(
    k5_relat_1(k1_xboole_0,'#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_41884])).

tff(c_41907,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_41899])).

tff(c_41908,plain,(
    k5_relat_1('#skF_9',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_41914,plain,(
    ! [B_1519,A_1520] :
      ( v1_relat_1(B_1519)
      | ~ m1_subset_1(B_1519,k1_zfmisc_1(A_1520))
      | ~ v1_relat_1(A_1520) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_41918,plain,(
    ! [A_5] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_10,c_41914])).

tff(c_41919,plain,(
    ! [A_5] : ~ v1_relat_1(A_5) ),
    inference(splitLeft,[status(thm)],[c_41918])).

tff(c_41922,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41919,c_42])).

tff(c_41923,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_41918])).

tff(c_42284,plain,(
    ! [A_1592,B_1593,C_1594] :
      ( r2_hidden(k4_tarski('#skF_6'(A_1592,B_1593,C_1594),'#skF_5'(A_1592,B_1593,C_1594)),B_1593)
      | r2_hidden(k4_tarski('#skF_7'(A_1592,B_1593,C_1594),'#skF_8'(A_1592,B_1593,C_1594)),C_1594)
      | k5_relat_1(A_1592,B_1593) = C_1594
      | ~ v1_relat_1(C_1594)
      | ~ v1_relat_1(B_1593)
      | ~ v1_relat_1(A_1592) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_41909,plain,(
    k5_relat_1(k1_xboole_0,'#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_42031,plain,(
    ! [D_1555,B_1556,A_1557,E_1558] :
      ( r2_hidden(k4_tarski(D_1555,'#skF_3'(B_1556,D_1555,A_1557,k5_relat_1(A_1557,B_1556),E_1558)),A_1557)
      | ~ r2_hidden(k4_tarski(D_1555,E_1558),k5_relat_1(A_1557,B_1556))
      | ~ v1_relat_1(k5_relat_1(A_1557,B_1556))
      | ~ v1_relat_1(B_1556)
      | ~ v1_relat_1(A_1557) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_42045,plain,(
    ! [D_1555,E_1558] :
      ( r2_hidden(k4_tarski(D_1555,'#skF_3'('#skF_9',D_1555,k1_xboole_0,k1_xboole_0,E_1558)),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_1555,E_1558),k5_relat_1(k1_xboole_0,'#skF_9'))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,'#skF_9'))
      | ~ v1_relat_1('#skF_9')
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41909,c_42031])).

tff(c_42054,plain,(
    ! [D_1559,E_1560] :
      ( r2_hidden(k4_tarski(D_1559,'#skF_3'('#skF_9',D_1559,k1_xboole_0,k1_xboole_0,E_1560)),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_1559,E_1560),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41923,c_42,c_41923,c_41909,c_41909,c_42045])).

tff(c_42058,plain,(
    ! [D_1559,E_1560,B_22] :
      ( r2_hidden(k4_tarski(D_1559,'#skF_3'('#skF_9',D_1559,k1_xboole_0,k1_xboole_0,E_1560)),B_22)
      | ~ r1_tarski(k1_xboole_0,B_22)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_1559,E_1560),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_42054,c_16])).

tff(c_42068,plain,(
    ! [D_1561,E_1562,B_1563] :
      ( r2_hidden(k4_tarski(D_1561,'#skF_3'('#skF_9',D_1561,k1_xboole_0,k1_xboole_0,E_1562)),B_1563)
      | ~ r2_hidden(k4_tarski(D_1561,E_1562),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41923,c_2,c_42058])).

tff(c_42087,plain,(
    ! [D_1561,E_1562] : ~ r2_hidden(k4_tarski(D_1561,E_1562),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_42068,c_6])).

tff(c_42296,plain,(
    ! [A_1592,C_1594] :
      ( r2_hidden(k4_tarski('#skF_7'(A_1592,k1_xboole_0,C_1594),'#skF_8'(A_1592,k1_xboole_0,C_1594)),C_1594)
      | k5_relat_1(A_1592,k1_xboole_0) = C_1594
      | ~ v1_relat_1(C_1594)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_1592) ) ),
    inference(resolution,[status(thm)],[c_42284,c_42087])).

tff(c_42343,plain,(
    ! [A_1595,C_1596] :
      ( r2_hidden(k4_tarski('#skF_7'(A_1595,k1_xboole_0,C_1596),'#skF_8'(A_1595,k1_xboole_0,C_1596)),C_1596)
      | k5_relat_1(A_1595,k1_xboole_0) = C_1596
      | ~ v1_relat_1(C_1596)
      | ~ v1_relat_1(A_1595) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41923,c_42296])).

tff(c_42355,plain,(
    ! [A_1595] :
      ( k5_relat_1(A_1595,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_1595) ) ),
    inference(resolution,[status(thm)],[c_42343,c_42087])).

tff(c_42378,plain,(
    ! [A_1597] :
      ( k5_relat_1(A_1597,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_1597) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41923,c_42355])).

tff(c_42384,plain,(
    k5_relat_1('#skF_9',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_42378])).

tff(c_42389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41908,c_42384])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:44:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.79/15.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.79/15.81  
% 24.79/15.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.79/15.81  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_5 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1
% 24.79/15.81  
% 24.79/15.81  %Foreground sorts:
% 24.79/15.81  
% 24.79/15.81  
% 24.79/15.81  %Background operators:
% 24.79/15.81  
% 24.79/15.81  
% 24.79/15.81  %Foreground operators:
% 24.79/15.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.79/15.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.79/15.81  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 24.79/15.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 24.79/15.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 24.79/15.81  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 24.79/15.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 24.79/15.81  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 24.79/15.81  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 24.79/15.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.79/15.81  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 24.79/15.81  tff('#skF_9', type, '#skF_9': $i).
% 24.79/15.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 24.79/15.81  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 24.79/15.81  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 24.79/15.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.79/15.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 24.79/15.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.79/15.81  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 24.79/15.81  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 24.79/15.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 24.79/15.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 24.79/15.81  
% 24.79/15.82  tff(f_84, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 24.79/15.82  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 24.79/15.82  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 24.79/15.82  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 24.79/15.82  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 24.79/15.82  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 24.79/15.82  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 24.79/15.82  tff(c_40, plain, (k5_relat_1('#skF_9', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 24.79/15.82  tff(c_46, plain, (k5_relat_1(k1_xboole_0, '#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 24.79/15.82  tff(c_42, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_84])).
% 24.79/15.82  tff(c_10, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 24.79/15.82  tff(c_47, plain, (![B_132, A_133]: (v1_relat_1(B_132) | ~m1_subset_1(B_132, k1_zfmisc_1(A_133)) | ~v1_relat_1(A_133))), inference(cnfTransformation, [status(thm)], [f_49])).
% 24.79/15.82  tff(c_51, plain, (![A_5]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_10, c_47])).
% 24.79/15.82  tff(c_52, plain, (![A_5]: (~v1_relat_1(A_5))), inference(splitLeft, [status(thm)], [c_51])).
% 24.79/15.82  tff(c_55, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_42])).
% 24.79/15.82  tff(c_56, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_51])).
% 24.79/15.82  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 24.79/15.82  tff(c_295, plain, (![A_204, B_205, C_206]: (r2_hidden(k4_tarski('#skF_4'(A_204, B_205, C_206), '#skF_6'(A_204, B_205, C_206)), A_204) | r2_hidden(k4_tarski('#skF_7'(A_204, B_205, C_206), '#skF_8'(A_204, B_205, C_206)), C_206) | k5_relat_1(A_204, B_205)=C_206 | ~v1_relat_1(C_206) | ~v1_relat_1(B_205) | ~v1_relat_1(A_204))), inference(cnfTransformation, [status(thm)], [f_77])).
% 24.79/15.82  tff(c_16, plain, (![C_27, D_28, B_22, A_12]: (r2_hidden(k4_tarski(C_27, D_28), B_22) | ~r2_hidden(k4_tarski(C_27, D_28), A_12) | ~r1_tarski(A_12, B_22) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 24.79/15.82  tff(c_1361, plain, (![A_335, B_336, C_337, B_338]: (r2_hidden(k4_tarski('#skF_7'(A_335, B_336, C_337), '#skF_8'(A_335, B_336, C_337)), B_338) | ~r1_tarski(C_337, B_338) | r2_hidden(k4_tarski('#skF_4'(A_335, B_336, C_337), '#skF_6'(A_335, B_336, C_337)), A_335) | k5_relat_1(A_335, B_336)=C_337 | ~v1_relat_1(C_337) | ~v1_relat_1(B_336) | ~v1_relat_1(A_335))), inference(resolution, [status(thm)], [c_295, c_16])).
% 24.79/15.82  tff(c_6, plain, (![C_4, B_3]: (~r2_hidden(C_4, k4_xboole_0(B_3, k1_tarski(C_4))))), inference(cnfTransformation, [status(thm)], [f_34])).
% 24.79/15.82  tff(c_40393, plain, (![C_1485, B_1486, A_1487, B_1488]: (~r1_tarski(C_1485, k4_xboole_0(B_1486, k1_tarski(k4_tarski('#skF_7'(A_1487, B_1488, C_1485), '#skF_8'(A_1487, B_1488, C_1485))))) | r2_hidden(k4_tarski('#skF_4'(A_1487, B_1488, C_1485), '#skF_6'(A_1487, B_1488, C_1485)), A_1487) | k5_relat_1(A_1487, B_1488)=C_1485 | ~v1_relat_1(C_1485) | ~v1_relat_1(B_1488) | ~v1_relat_1(A_1487))), inference(resolution, [status(thm)], [c_1361, c_6])).
% 24.79/15.82  tff(c_40601, plain, (![A_1487, B_1488]: (r2_hidden(k4_tarski('#skF_4'(A_1487, B_1488, k1_xboole_0), '#skF_6'(A_1487, B_1488, k1_xboole_0)), A_1487) | k5_relat_1(A_1487, B_1488)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_1488) | ~v1_relat_1(A_1487))), inference(resolution, [status(thm)], [c_2, c_40393])).
% 24.79/15.82  tff(c_40673, plain, (![A_1489, B_1490]: (r2_hidden(k4_tarski('#skF_4'(A_1489, B_1490, k1_xboole_0), '#skF_6'(A_1489, B_1490, k1_xboole_0)), A_1489) | k5_relat_1(A_1489, B_1490)=k1_xboole_0 | ~v1_relat_1(B_1490) | ~v1_relat_1(A_1489))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_40601])).
% 24.79/15.82  tff(c_41179, plain, (![A_1503, B_1504, B_1505]: (r2_hidden(k4_tarski('#skF_4'(A_1503, B_1504, k1_xboole_0), '#skF_6'(A_1503, B_1504, k1_xboole_0)), B_1505) | ~r1_tarski(A_1503, B_1505) | k5_relat_1(A_1503, B_1504)=k1_xboole_0 | ~v1_relat_1(B_1504) | ~v1_relat_1(A_1503))), inference(resolution, [status(thm)], [c_40673, c_16])).
% 24.79/15.82  tff(c_41534, plain, (![A_1515, B_1516, B_1517]: (~r1_tarski(A_1515, k4_xboole_0(B_1516, k1_tarski(k4_tarski('#skF_4'(A_1515, B_1517, k1_xboole_0), '#skF_6'(A_1515, B_1517, k1_xboole_0))))) | k5_relat_1(A_1515, B_1517)=k1_xboole_0 | ~v1_relat_1(B_1517) | ~v1_relat_1(A_1515))), inference(resolution, [status(thm)], [c_41179, c_6])).
% 24.79/15.82  tff(c_41812, plain, (![B_1517]: (k5_relat_1(k1_xboole_0, B_1517)=k1_xboole_0 | ~v1_relat_1(B_1517) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_41534])).
% 24.79/15.82  tff(c_41884, plain, (![B_1518]: (k5_relat_1(k1_xboole_0, B_1518)=k1_xboole_0 | ~v1_relat_1(B_1518))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_41812])).
% 24.79/15.82  tff(c_41899, plain, (k5_relat_1(k1_xboole_0, '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_41884])).
% 24.79/15.82  tff(c_41907, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_41899])).
% 24.79/15.82  tff(c_41908, plain, (k5_relat_1('#skF_9', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 24.79/15.82  tff(c_41914, plain, (![B_1519, A_1520]: (v1_relat_1(B_1519) | ~m1_subset_1(B_1519, k1_zfmisc_1(A_1520)) | ~v1_relat_1(A_1520))), inference(cnfTransformation, [status(thm)], [f_49])).
% 24.79/15.82  tff(c_41918, plain, (![A_5]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_10, c_41914])).
% 24.79/15.82  tff(c_41919, plain, (![A_5]: (~v1_relat_1(A_5))), inference(splitLeft, [status(thm)], [c_41918])).
% 24.79/15.82  tff(c_41922, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41919, c_42])).
% 24.79/15.82  tff(c_41923, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_41918])).
% 24.79/15.82  tff(c_42284, plain, (![A_1592, B_1593, C_1594]: (r2_hidden(k4_tarski('#skF_6'(A_1592, B_1593, C_1594), '#skF_5'(A_1592, B_1593, C_1594)), B_1593) | r2_hidden(k4_tarski('#skF_7'(A_1592, B_1593, C_1594), '#skF_8'(A_1592, B_1593, C_1594)), C_1594) | k5_relat_1(A_1592, B_1593)=C_1594 | ~v1_relat_1(C_1594) | ~v1_relat_1(B_1593) | ~v1_relat_1(A_1592))), inference(cnfTransformation, [status(thm)], [f_77])).
% 24.79/15.82  tff(c_41909, plain, (k5_relat_1(k1_xboole_0, '#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 24.79/15.82  tff(c_42031, plain, (![D_1555, B_1556, A_1557, E_1558]: (r2_hidden(k4_tarski(D_1555, '#skF_3'(B_1556, D_1555, A_1557, k5_relat_1(A_1557, B_1556), E_1558)), A_1557) | ~r2_hidden(k4_tarski(D_1555, E_1558), k5_relat_1(A_1557, B_1556)) | ~v1_relat_1(k5_relat_1(A_1557, B_1556)) | ~v1_relat_1(B_1556) | ~v1_relat_1(A_1557))), inference(cnfTransformation, [status(thm)], [f_77])).
% 24.79/15.82  tff(c_42045, plain, (![D_1555, E_1558]: (r2_hidden(k4_tarski(D_1555, '#skF_3'('#skF_9', D_1555, k1_xboole_0, k1_xboole_0, E_1558)), k1_xboole_0) | ~r2_hidden(k4_tarski(D_1555, E_1558), k5_relat_1(k1_xboole_0, '#skF_9')) | ~v1_relat_1(k5_relat_1(k1_xboole_0, '#skF_9')) | ~v1_relat_1('#skF_9') | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_41909, c_42031])).
% 24.79/15.82  tff(c_42054, plain, (![D_1559, E_1560]: (r2_hidden(k4_tarski(D_1559, '#skF_3'('#skF_9', D_1559, k1_xboole_0, k1_xboole_0, E_1560)), k1_xboole_0) | ~r2_hidden(k4_tarski(D_1559, E_1560), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_41923, c_42, c_41923, c_41909, c_41909, c_42045])).
% 24.79/15.82  tff(c_42058, plain, (![D_1559, E_1560, B_22]: (r2_hidden(k4_tarski(D_1559, '#skF_3'('#skF_9', D_1559, k1_xboole_0, k1_xboole_0, E_1560)), B_22) | ~r1_tarski(k1_xboole_0, B_22) | ~v1_relat_1(k1_xboole_0) | ~r2_hidden(k4_tarski(D_1559, E_1560), k1_xboole_0))), inference(resolution, [status(thm)], [c_42054, c_16])).
% 24.79/15.82  tff(c_42068, plain, (![D_1561, E_1562, B_1563]: (r2_hidden(k4_tarski(D_1561, '#skF_3'('#skF_9', D_1561, k1_xboole_0, k1_xboole_0, E_1562)), B_1563) | ~r2_hidden(k4_tarski(D_1561, E_1562), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_41923, c_2, c_42058])).
% 24.79/15.82  tff(c_42087, plain, (![D_1561, E_1562]: (~r2_hidden(k4_tarski(D_1561, E_1562), k1_xboole_0))), inference(resolution, [status(thm)], [c_42068, c_6])).
% 24.79/15.82  tff(c_42296, plain, (![A_1592, C_1594]: (r2_hidden(k4_tarski('#skF_7'(A_1592, k1_xboole_0, C_1594), '#skF_8'(A_1592, k1_xboole_0, C_1594)), C_1594) | k5_relat_1(A_1592, k1_xboole_0)=C_1594 | ~v1_relat_1(C_1594) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_1592))), inference(resolution, [status(thm)], [c_42284, c_42087])).
% 24.79/15.82  tff(c_42343, plain, (![A_1595, C_1596]: (r2_hidden(k4_tarski('#skF_7'(A_1595, k1_xboole_0, C_1596), '#skF_8'(A_1595, k1_xboole_0, C_1596)), C_1596) | k5_relat_1(A_1595, k1_xboole_0)=C_1596 | ~v1_relat_1(C_1596) | ~v1_relat_1(A_1595))), inference(demodulation, [status(thm), theory('equality')], [c_41923, c_42296])).
% 24.79/15.82  tff(c_42355, plain, (![A_1595]: (k5_relat_1(A_1595, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_1595))), inference(resolution, [status(thm)], [c_42343, c_42087])).
% 24.79/15.82  tff(c_42378, plain, (![A_1597]: (k5_relat_1(A_1597, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_1597))), inference(demodulation, [status(thm), theory('equality')], [c_41923, c_42355])).
% 24.79/15.82  tff(c_42384, plain, (k5_relat_1('#skF_9', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_42378])).
% 24.79/15.82  tff(c_42389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41908, c_42384])).
% 24.79/15.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.79/15.82  
% 24.79/15.82  Inference rules
% 24.79/15.82  ----------------------
% 24.79/15.82  #Ref     : 0
% 24.79/15.82  #Sup     : 10799
% 24.79/15.82  #Fact    : 38
% 24.79/15.82  #Define  : 0
% 24.79/15.82  #Split   : 24
% 24.79/15.82  #Chain   : 0
% 24.79/15.82  #Close   : 0
% 24.79/15.82  
% 24.79/15.82  Ordering : KBO
% 24.79/15.82  
% 24.79/15.82  Simplification rules
% 24.79/15.82  ----------------------
% 24.79/15.82  #Subsume      : 4408
% 24.79/15.82  #Demod        : 529
% 24.79/15.82  #Tautology    : 166
% 24.79/15.82  #SimpNegUnit  : 184
% 24.79/15.82  #BackRed      : 38
% 24.79/15.82  
% 24.79/15.82  #Partial instantiations: 0
% 24.79/15.82  #Strategies tried      : 1
% 24.79/15.82  
% 24.79/15.82  Timing (in seconds)
% 24.79/15.82  ----------------------
% 24.79/15.83  Preprocessing        : 0.30
% 24.79/15.83  Parsing              : 0.16
% 24.79/15.83  CNF conversion       : 0.03
% 24.79/15.83  Main loop            : 14.77
% 24.79/15.83  Inferencing          : 1.66
% 24.79/15.83  Reduction            : 1.63
% 24.79/15.83  Demodulation         : 0.98
% 24.79/15.83  BG Simplification    : 0.26
% 24.79/15.83  Subsumption          : 10.58
% 24.79/15.83  Abstraction          : 0.46
% 24.79/15.83  MUC search           : 0.00
% 24.79/15.83  Cooper               : 0.00
% 24.79/15.83  Total                : 15.10
% 24.79/15.83  Index Insertion      : 0.00
% 24.79/15.83  Index Deletion       : 0.00
% 24.79/15.83  Index Matching       : 0.00
% 24.79/15.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
