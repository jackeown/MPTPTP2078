%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0385+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:13 EST 2020

% Result     : Theorem 12.41s
% Output     : CNFRefutation 12.81s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 834 expanded)
%              Number of leaves         :   24 ( 288 expanded)
%              Depth                    :   15
%              Number of atoms          :   92 (2047 expanded)
%              Number of equality atoms :   22 ( 411 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k3_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_67,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_70,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_setfam_1(A),k3_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_setfam_1)).

tff(c_61,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_5'(A_52,B_53),A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( ~ r2_hidden('#skF_5'(A_22,B_23),B_23)
      | r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_68,plain,(
    ! [A_52] : r1_tarski(A_52,A_52) ),
    inference(resolution,[status(thm)],[c_61,c_28])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( r2_hidden('#skF_5'(A_22,B_23),A_22)
      | r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    ! [A_3,C_15] :
      ( r2_hidden('#skF_1'(A_3,k1_setfam_1(A_3),C_15),A_3)
      | r2_hidden(C_15,k1_setfam_1(A_3))
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_50,plain,(
    ! [A_46] : r1_tarski(k1_xboole_0,A_46) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_90,plain,(
    ! [A_65,C_66] :
      ( r2_hidden('#skF_9'(A_65,k3_tarski(A_65),C_66),A_65)
      | ~ r2_hidden(C_66,k3_tarski(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ! [C_26,B_23,A_22] :
      ( r2_hidden(C_26,B_23)
      | ~ r2_hidden(C_26,A_22)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_336,plain,(
    ! [A_107,C_108,B_109] :
      ( r2_hidden('#skF_9'(A_107,k3_tarski(A_107),C_108),B_109)
      | ~ r1_tarski(A_107,B_109)
      | ~ r2_hidden(C_108,k3_tarski(A_107)) ) ),
    inference(resolution,[status(thm)],[c_90,c_26])).

tff(c_34,plain,(
    ! [A_27,C_42] :
      ( r2_hidden('#skF_9'(A_27,k3_tarski(A_27),C_42),A_27)
      | ~ r2_hidden(C_42,k3_tarski(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_80,plain,(
    ! [C_63,A_64] :
      ( r2_hidden(C_63,'#skF_9'(A_64,k3_tarski(A_64),C_63))
      | ~ r2_hidden(C_63,k3_tarski(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_120,plain,(
    ! [A_70,C_71] :
      ( ~ r2_hidden('#skF_9'(A_70,k3_tarski(A_70),C_71),C_71)
      | ~ r2_hidden(C_71,k3_tarski(A_70)) ) ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_125,plain,(
    ! [A_27] : ~ r2_hidden(A_27,k3_tarski(A_27)) ),
    inference(resolution,[status(thm)],[c_34,c_120])).

tff(c_884,plain,(
    ! [A_149,C_150] :
      ( ~ r1_tarski(A_149,k3_tarski('#skF_9'(A_149,k3_tarski(A_149),C_150)))
      | ~ r2_hidden(C_150,k3_tarski(A_149)) ) ),
    inference(resolution,[status(thm)],[c_336,c_125])).

tff(c_930,plain,(
    ! [C_151] : ~ r2_hidden(C_151,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_50,c_884])).

tff(c_972,plain,(
    ! [C_15] :
      ( r2_hidden(C_15,k1_setfam_1(k3_tarski(k1_xboole_0)))
      | k3_tarski(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_930])).

tff(c_1317,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_972])).

tff(c_46,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_7'(A_27,B_28),A_27)
      | r2_hidden('#skF_8'(A_27,B_28),B_28)
      | k3_tarski(A_27) = B_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_970,plain,(
    ! [B_28] :
      ( r2_hidden('#skF_8'(k3_tarski(k1_xboole_0),B_28),B_28)
      | k3_tarski(k3_tarski(k1_xboole_0)) = B_28 ) ),
    inference(resolution,[status(thm)],[c_46,c_930])).

tff(c_2649,plain,(
    ! [B_200] :
      ( r2_hidden('#skF_8'(k1_xboole_0,B_200),B_200)
      | k1_xboole_0 = B_200 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1317,c_1317,c_1317,c_970])).

tff(c_16,plain,(
    ! [C_15,D_18,A_3] :
      ( r2_hidden(C_15,D_18)
      | ~ r2_hidden(D_18,A_3)
      | ~ r2_hidden(C_15,k1_setfam_1(A_3))
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3973,plain,(
    ! [C_232,B_233] :
      ( r2_hidden(C_232,'#skF_8'(k1_xboole_0,B_233))
      | ~ r2_hidden(C_232,k1_setfam_1(B_233))
      | k1_xboole_0 = B_233 ) ),
    inference(resolution,[status(thm)],[c_2649,c_16])).

tff(c_27798,plain,(
    ! [B_620,B_621] :
      ( r2_hidden('#skF_5'(k1_setfam_1(B_620),B_621),'#skF_8'(k1_xboole_0,B_620))
      | k1_xboole_0 = B_620
      | r1_tarski(k1_setfam_1(B_620),B_621) ) ),
    inference(resolution,[status(thm)],[c_30,c_3973])).

tff(c_32,plain,(
    ! [C_42,A_27,D_45] :
      ( r2_hidden(C_42,k3_tarski(A_27))
      | ~ r2_hidden(D_45,A_27)
      | ~ r2_hidden(C_42,D_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3875,plain,(
    ! [C_230,B_231] :
      ( r2_hidden(C_230,k3_tarski(B_231))
      | ~ r2_hidden(C_230,'#skF_8'(k1_xboole_0,B_231))
      | k1_xboole_0 = B_231 ) ),
    inference(resolution,[status(thm)],[c_2649,c_32])).

tff(c_3965,plain,(
    ! [A_22,B_231] :
      ( r1_tarski(A_22,k3_tarski(B_231))
      | ~ r2_hidden('#skF_5'(A_22,k3_tarski(B_231)),'#skF_8'(k1_xboole_0,B_231))
      | k1_xboole_0 = B_231 ) ),
    inference(resolution,[status(thm)],[c_3875,c_28])).

tff(c_27842,plain,(
    ! [B_622] :
      ( k1_xboole_0 = B_622
      | r1_tarski(k1_setfam_1(B_622),k3_tarski(B_622)) ) ),
    inference(resolution,[status(thm)],[c_27798,c_3965])).

tff(c_52,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_10'),k3_tarski('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_27978,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_27842,c_52])).

tff(c_24,plain,(
    k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28182,plain,(
    k1_setfam_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27978,c_27978,c_24])).

tff(c_28172,plain,(
    k3_tarski('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27978,c_27978,c_1317])).

tff(c_28256,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_10'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28172,c_52])).

tff(c_28475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_28182,c_28256])).

tff(c_28476,plain,(
    ! [C_15] : r2_hidden(C_15,k1_setfam_1(k3_tarski(k1_xboole_0))) ),
    inference(splitRight,[status(thm)],[c_972])).

tff(c_28620,plain,(
    ! [C_632] : r2_hidden(C_632,k1_setfam_1(k3_tarski(k1_xboole_0))) ),
    inference(splitRight,[status(thm)],[c_972])).

tff(c_28672,plain,(
    ! [C_634] : ~ r2_hidden(k1_setfam_1(k3_tarski(k1_xboole_0)),C_634) ),
    inference(resolution,[status(thm)],[c_28620,c_2])).

tff(c_28681,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_28476,c_28672])).

%------------------------------------------------------------------------------
