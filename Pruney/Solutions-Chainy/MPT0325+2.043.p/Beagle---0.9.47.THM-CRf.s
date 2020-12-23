%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:26 EST 2020

% Result     : Theorem 5.87s
% Output     : CNFRefutation 5.87s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 338 expanded)
%              Number of leaves         :   27 ( 125 expanded)
%              Depth                    :    9
%              Number of atoms          :  137 ( 729 expanded)
%              Number of equality atoms :   28 ( 128 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_40,plain,
    ( ~ r1_tarski('#skF_6','#skF_8')
    | ~ r1_tarski('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_84,plain,(
    ~ r1_tarski('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_18] : r1_xboole_0(A_18,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_489,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_2'(A_104,B_105),B_105)
      | r2_hidden('#skF_3'(A_104,B_105),A_104)
      | B_105 = A_104 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,k3_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_790,plain,(
    ! [A_138,B_139,A_140] :
      ( ~ r1_xboole_0(A_138,B_139)
      | r2_hidden('#skF_3'(A_140,k3_xboole_0(A_138,B_139)),A_140)
      | k3_xboole_0(A_138,B_139) = A_140 ) ),
    inference(resolution,[status(thm)],[c_489,c_18])).

tff(c_813,plain,(
    ! [A_14,A_140] :
      ( ~ r1_xboole_0(A_14,k1_xboole_0)
      | r2_hidden('#skF_3'(A_140,k1_xboole_0),A_140)
      | k3_xboole_0(A_14,k1_xboole_0) = A_140 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_790])).

tff(c_822,plain,(
    ! [A_140] :
      ( r2_hidden('#skF_3'(A_140,k1_xboole_0),A_140)
      | k1_xboole_0 = A_140 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_26,c_813])).

tff(c_44,plain,(
    r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_569,plain,(
    ! [A_108,B_109,C_110,D_111] :
      ( r2_hidden(k4_tarski(A_108,B_109),k2_zfmisc_1(C_110,D_111))
      | ~ r2_hidden(B_109,D_111)
      | ~ r2_hidden(A_108,C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1692,plain,(
    ! [A_256,D_259,B_258,C_257,B_260] :
      ( r2_hidden(k4_tarski(A_256,B_260),B_258)
      | ~ r1_tarski(k2_zfmisc_1(C_257,D_259),B_258)
      | ~ r2_hidden(B_260,D_259)
      | ~ r2_hidden(A_256,C_257) ) ),
    inference(resolution,[status(thm)],[c_569,c_2])).

tff(c_1708,plain,(
    ! [A_261,B_262] :
      ( r2_hidden(k4_tarski(A_261,B_262),k2_zfmisc_1('#skF_7','#skF_8'))
      | ~ r2_hidden(B_262,'#skF_6')
      | ~ r2_hidden(A_261,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_1692])).

tff(c_30,plain,(
    ! [B_20,D_22,A_19,C_21] :
      ( r2_hidden(B_20,D_22)
      | ~ r2_hidden(k4_tarski(A_19,B_20),k2_zfmisc_1(C_21,D_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1721,plain,(
    ! [B_262,A_261] :
      ( r2_hidden(B_262,'#skF_8')
      | ~ r2_hidden(B_262,'#skF_6')
      | ~ r2_hidden(A_261,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1708,c_30])).

tff(c_1725,plain,(
    ! [A_263] : ~ r2_hidden(A_263,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1721])).

tff(c_1829,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_822,c_1725])).

tff(c_171,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44,B_45),A_44)
      | r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_145,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,k3_xboole_0(A_36,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_151,plain,(
    ! [A_14,C_38] :
      ( ~ r1_xboole_0(A_14,k1_xboole_0)
      | ~ r2_hidden(C_38,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_145])).

tff(c_153,plain,(
    ! [C_38] : ~ r2_hidden(C_38,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_151])).

tff(c_184,plain,(
    ! [B_45] : r1_tarski(k1_xboole_0,B_45) ),
    inference(resolution,[status(thm)],[c_171,c_153])).

tff(c_1892,plain,(
    ! [B_45] : r1_tarski('#skF_5',B_45) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1829,c_184])).

tff(c_1909,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1892,c_84])).

tff(c_1911,plain,(
    ! [B_266] :
      ( r2_hidden(B_266,'#skF_8')
      | ~ r2_hidden(B_266,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_1721])).

tff(c_2015,plain,
    ( r2_hidden('#skF_3'('#skF_6',k1_xboole_0),'#skF_8')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_822,c_1911])).

tff(c_2028,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2015])).

tff(c_36,plain,(
    ! [A_23] : k2_zfmisc_1(A_23,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2091,plain,(
    ! [A_23] : k2_zfmisc_1(A_23,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2028,c_2028,c_36])).

tff(c_42,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2093,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2028,c_42])).

tff(c_2288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2091,c_2093])).

tff(c_2290,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2015])).

tff(c_32,plain,(
    ! [A_19,C_21,B_20,D_22] :
      ( r2_hidden(A_19,C_21)
      | ~ r2_hidden(k4_tarski(A_19,B_20),k2_zfmisc_1(C_21,D_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1722,plain,(
    ! [A_261,B_262] :
      ( r2_hidden(A_261,'#skF_7')
      | ~ r2_hidden(B_262,'#skF_6')
      | ~ r2_hidden(A_261,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1708,c_32])).

tff(c_2634,plain,(
    ! [B_301] : ~ r2_hidden(B_301,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1722])).

tff(c_2694,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_822,c_2634])).

tff(c_2761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2290,c_2694])).

tff(c_2763,plain,(
    ! [A_302] :
      ( r2_hidden(A_302,'#skF_7')
      | ~ r2_hidden(A_302,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_1722])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2795,plain,(
    ! [A_303] :
      ( r1_tarski(A_303,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_303,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2763,c_4])).

tff(c_2803,plain,(
    r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_2795])).

tff(c_2808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_84,c_2803])).

tff(c_2809,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_3192,plain,(
    ! [A_373,B_374] :
      ( r2_hidden('#skF_2'(A_373,B_374),B_374)
      | r2_hidden('#skF_3'(A_373,B_374),A_373)
      | B_374 = A_373 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3626,plain,(
    ! [A_427,B_428,A_429] :
      ( ~ r1_xboole_0(A_427,B_428)
      | r2_hidden('#skF_3'(A_429,k3_xboole_0(A_427,B_428)),A_429)
      | k3_xboole_0(A_427,B_428) = A_429 ) ),
    inference(resolution,[status(thm)],[c_3192,c_18])).

tff(c_3649,plain,(
    ! [A_14,A_429] :
      ( ~ r1_xboole_0(A_14,k1_xboole_0)
      | r2_hidden('#skF_3'(A_429,k1_xboole_0),A_429)
      | k3_xboole_0(A_14,k1_xboole_0) = A_429 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3626])).

tff(c_3658,plain,(
    ! [A_429] :
      ( r2_hidden('#skF_3'(A_429,k1_xboole_0),A_429)
      | k1_xboole_0 = A_429 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_26,c_3649])).

tff(c_3315,plain,(
    ! [A_384,B_385,C_386,D_387] :
      ( r2_hidden(k4_tarski(A_384,B_385),k2_zfmisc_1(C_386,D_387))
      | ~ r2_hidden(B_385,D_387)
      | ~ r2_hidden(A_384,C_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4478,plain,(
    ! [C_529,D_528,A_532,B_530,B_531] :
      ( r2_hidden(k4_tarski(A_532,B_530),B_531)
      | ~ r1_tarski(k2_zfmisc_1(C_529,D_528),B_531)
      | ~ r2_hidden(B_530,D_528)
      | ~ r2_hidden(A_532,C_529) ) ),
    inference(resolution,[status(thm)],[c_3315,c_2])).

tff(c_4498,plain,(
    ! [A_533,B_534] :
      ( r2_hidden(k4_tarski(A_533,B_534),k2_zfmisc_1('#skF_7','#skF_8'))
      | ~ r2_hidden(B_534,'#skF_6')
      | ~ r2_hidden(A_533,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_4478])).

tff(c_4512,plain,(
    ! [B_534,A_533] :
      ( r2_hidden(B_534,'#skF_8')
      | ~ r2_hidden(B_534,'#skF_6')
      | ~ r2_hidden(A_533,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4498,c_30])).

tff(c_4819,plain,(
    ! [A_544] : ~ r2_hidden(A_544,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4512])).

tff(c_4938,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3658,c_4819])).

tff(c_38,plain,(
    ! [B_24] : k2_zfmisc_1(k1_xboole_0,B_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5013,plain,(
    ! [B_24] : k2_zfmisc_1('#skF_5',B_24) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4938,c_4938,c_38])).

tff(c_5014,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4938,c_42])).

tff(c_5263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5013,c_5014])).

tff(c_5265,plain,(
    ! [B_555] :
      ( r2_hidden(B_555,'#skF_8')
      | ~ r2_hidden(B_555,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_4512])).

tff(c_5604,plain,(
    ! [B_567] :
      ( r2_hidden('#skF_1'('#skF_6',B_567),'#skF_8')
      | r1_tarski('#skF_6',B_567) ) ),
    inference(resolution,[status(thm)],[c_6,c_5265])).

tff(c_5613,plain,(
    r1_tarski('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_5604,c_4])).

tff(c_5619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2809,c_2809,c_5613])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.87/2.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.87/2.24  
% 5.87/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.87/2.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 5.87/2.24  
% 5.87/2.24  %Foreground sorts:
% 5.87/2.24  
% 5.87/2.24  
% 5.87/2.24  %Background operators:
% 5.87/2.24  
% 5.87/2.24  
% 5.87/2.24  %Foreground operators:
% 5.87/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.87/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.87/2.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.87/2.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.87/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.87/2.24  tff('#skF_7', type, '#skF_7': $i).
% 5.87/2.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.87/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.87/2.24  tff('#skF_5', type, '#skF_5': $i).
% 5.87/2.24  tff('#skF_6', type, '#skF_6': $i).
% 5.87/2.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.87/2.24  tff('#skF_8', type, '#skF_8': $i).
% 5.87/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.87/2.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.87/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.87/2.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.87/2.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.87/2.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.87/2.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.87/2.24  
% 5.87/2.26  tff(f_82, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 5.87/2.26  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.87/2.26  tff(f_55, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.87/2.26  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.87/2.26  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 5.87/2.26  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.87/2.26  tff(f_67, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.87/2.26  tff(f_73, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.87/2.26  tff(c_40, plain, (~r1_tarski('#skF_6', '#skF_8') | ~r1_tarski('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.87/2.26  tff(c_84, plain, (~r1_tarski('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_40])).
% 5.87/2.26  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.87/2.26  tff(c_20, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.87/2.26  tff(c_26, plain, (![A_18]: (r1_xboole_0(A_18, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.87/2.26  tff(c_489, plain, (![A_104, B_105]: (r2_hidden('#skF_2'(A_104, B_105), B_105) | r2_hidden('#skF_3'(A_104, B_105), A_104) | B_105=A_104)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.87/2.26  tff(c_18, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, k3_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.87/2.26  tff(c_790, plain, (![A_138, B_139, A_140]: (~r1_xboole_0(A_138, B_139) | r2_hidden('#skF_3'(A_140, k3_xboole_0(A_138, B_139)), A_140) | k3_xboole_0(A_138, B_139)=A_140)), inference(resolution, [status(thm)], [c_489, c_18])).
% 5.87/2.26  tff(c_813, plain, (![A_14, A_140]: (~r1_xboole_0(A_14, k1_xboole_0) | r2_hidden('#skF_3'(A_140, k1_xboole_0), A_140) | k3_xboole_0(A_14, k1_xboole_0)=A_140)), inference(superposition, [status(thm), theory('equality')], [c_20, c_790])).
% 5.87/2.26  tff(c_822, plain, (![A_140]: (r2_hidden('#skF_3'(A_140, k1_xboole_0), A_140) | k1_xboole_0=A_140)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_26, c_813])).
% 5.87/2.26  tff(c_44, plain, (r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.87/2.26  tff(c_569, plain, (![A_108, B_109, C_110, D_111]: (r2_hidden(k4_tarski(A_108, B_109), k2_zfmisc_1(C_110, D_111)) | ~r2_hidden(B_109, D_111) | ~r2_hidden(A_108, C_110))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.87/2.26  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.87/2.26  tff(c_1692, plain, (![A_256, D_259, B_258, C_257, B_260]: (r2_hidden(k4_tarski(A_256, B_260), B_258) | ~r1_tarski(k2_zfmisc_1(C_257, D_259), B_258) | ~r2_hidden(B_260, D_259) | ~r2_hidden(A_256, C_257))), inference(resolution, [status(thm)], [c_569, c_2])).
% 5.87/2.26  tff(c_1708, plain, (![A_261, B_262]: (r2_hidden(k4_tarski(A_261, B_262), k2_zfmisc_1('#skF_7', '#skF_8')) | ~r2_hidden(B_262, '#skF_6') | ~r2_hidden(A_261, '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_1692])).
% 5.87/2.26  tff(c_30, plain, (![B_20, D_22, A_19, C_21]: (r2_hidden(B_20, D_22) | ~r2_hidden(k4_tarski(A_19, B_20), k2_zfmisc_1(C_21, D_22)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.87/2.26  tff(c_1721, plain, (![B_262, A_261]: (r2_hidden(B_262, '#skF_8') | ~r2_hidden(B_262, '#skF_6') | ~r2_hidden(A_261, '#skF_5'))), inference(resolution, [status(thm)], [c_1708, c_30])).
% 5.87/2.26  tff(c_1725, plain, (![A_263]: (~r2_hidden(A_263, '#skF_5'))), inference(splitLeft, [status(thm)], [c_1721])).
% 5.87/2.26  tff(c_1829, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_822, c_1725])).
% 5.87/2.26  tff(c_171, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44, B_45), A_44) | r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.87/2.26  tff(c_145, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, k3_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.87/2.26  tff(c_151, plain, (![A_14, C_38]: (~r1_xboole_0(A_14, k1_xboole_0) | ~r2_hidden(C_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_145])).
% 5.87/2.26  tff(c_153, plain, (![C_38]: (~r2_hidden(C_38, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_151])).
% 5.87/2.26  tff(c_184, plain, (![B_45]: (r1_tarski(k1_xboole_0, B_45))), inference(resolution, [status(thm)], [c_171, c_153])).
% 5.87/2.26  tff(c_1892, plain, (![B_45]: (r1_tarski('#skF_5', B_45))), inference(demodulation, [status(thm), theory('equality')], [c_1829, c_184])).
% 5.87/2.26  tff(c_1909, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1892, c_84])).
% 5.87/2.26  tff(c_1911, plain, (![B_266]: (r2_hidden(B_266, '#skF_8') | ~r2_hidden(B_266, '#skF_6'))), inference(splitRight, [status(thm)], [c_1721])).
% 5.87/2.26  tff(c_2015, plain, (r2_hidden('#skF_3'('#skF_6', k1_xboole_0), '#skF_8') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_822, c_1911])).
% 5.87/2.26  tff(c_2028, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_2015])).
% 5.87/2.26  tff(c_36, plain, (![A_23]: (k2_zfmisc_1(A_23, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.87/2.26  tff(c_2091, plain, (![A_23]: (k2_zfmisc_1(A_23, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2028, c_2028, c_36])).
% 5.87/2.26  tff(c_42, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.87/2.26  tff(c_2093, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2028, c_42])).
% 5.87/2.26  tff(c_2288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2091, c_2093])).
% 5.87/2.26  tff(c_2290, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_2015])).
% 5.87/2.26  tff(c_32, plain, (![A_19, C_21, B_20, D_22]: (r2_hidden(A_19, C_21) | ~r2_hidden(k4_tarski(A_19, B_20), k2_zfmisc_1(C_21, D_22)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.87/2.26  tff(c_1722, plain, (![A_261, B_262]: (r2_hidden(A_261, '#skF_7') | ~r2_hidden(B_262, '#skF_6') | ~r2_hidden(A_261, '#skF_5'))), inference(resolution, [status(thm)], [c_1708, c_32])).
% 5.87/2.26  tff(c_2634, plain, (![B_301]: (~r2_hidden(B_301, '#skF_6'))), inference(splitLeft, [status(thm)], [c_1722])).
% 5.87/2.26  tff(c_2694, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_822, c_2634])).
% 5.87/2.26  tff(c_2761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2290, c_2694])).
% 5.87/2.26  tff(c_2763, plain, (![A_302]: (r2_hidden(A_302, '#skF_7') | ~r2_hidden(A_302, '#skF_5'))), inference(splitRight, [status(thm)], [c_1722])).
% 5.87/2.26  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.87/2.26  tff(c_2795, plain, (![A_303]: (r1_tarski(A_303, '#skF_7') | ~r2_hidden('#skF_1'(A_303, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_2763, c_4])).
% 5.87/2.26  tff(c_2803, plain, (r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_2795])).
% 5.87/2.26  tff(c_2808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_84, c_2803])).
% 5.87/2.26  tff(c_2809, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_40])).
% 5.87/2.26  tff(c_3192, plain, (![A_373, B_374]: (r2_hidden('#skF_2'(A_373, B_374), B_374) | r2_hidden('#skF_3'(A_373, B_374), A_373) | B_374=A_373)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.87/2.26  tff(c_3626, plain, (![A_427, B_428, A_429]: (~r1_xboole_0(A_427, B_428) | r2_hidden('#skF_3'(A_429, k3_xboole_0(A_427, B_428)), A_429) | k3_xboole_0(A_427, B_428)=A_429)), inference(resolution, [status(thm)], [c_3192, c_18])).
% 5.87/2.26  tff(c_3649, plain, (![A_14, A_429]: (~r1_xboole_0(A_14, k1_xboole_0) | r2_hidden('#skF_3'(A_429, k1_xboole_0), A_429) | k3_xboole_0(A_14, k1_xboole_0)=A_429)), inference(superposition, [status(thm), theory('equality')], [c_20, c_3626])).
% 5.87/2.26  tff(c_3658, plain, (![A_429]: (r2_hidden('#skF_3'(A_429, k1_xboole_0), A_429) | k1_xboole_0=A_429)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_26, c_3649])).
% 5.87/2.26  tff(c_3315, plain, (![A_384, B_385, C_386, D_387]: (r2_hidden(k4_tarski(A_384, B_385), k2_zfmisc_1(C_386, D_387)) | ~r2_hidden(B_385, D_387) | ~r2_hidden(A_384, C_386))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.87/2.26  tff(c_4478, plain, (![C_529, D_528, A_532, B_530, B_531]: (r2_hidden(k4_tarski(A_532, B_530), B_531) | ~r1_tarski(k2_zfmisc_1(C_529, D_528), B_531) | ~r2_hidden(B_530, D_528) | ~r2_hidden(A_532, C_529))), inference(resolution, [status(thm)], [c_3315, c_2])).
% 5.87/2.26  tff(c_4498, plain, (![A_533, B_534]: (r2_hidden(k4_tarski(A_533, B_534), k2_zfmisc_1('#skF_7', '#skF_8')) | ~r2_hidden(B_534, '#skF_6') | ~r2_hidden(A_533, '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_4478])).
% 5.87/2.26  tff(c_4512, plain, (![B_534, A_533]: (r2_hidden(B_534, '#skF_8') | ~r2_hidden(B_534, '#skF_6') | ~r2_hidden(A_533, '#skF_5'))), inference(resolution, [status(thm)], [c_4498, c_30])).
% 5.87/2.26  tff(c_4819, plain, (![A_544]: (~r2_hidden(A_544, '#skF_5'))), inference(splitLeft, [status(thm)], [c_4512])).
% 5.87/2.26  tff(c_4938, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3658, c_4819])).
% 5.87/2.26  tff(c_38, plain, (![B_24]: (k2_zfmisc_1(k1_xboole_0, B_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.87/2.26  tff(c_5013, plain, (![B_24]: (k2_zfmisc_1('#skF_5', B_24)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4938, c_4938, c_38])).
% 5.87/2.26  tff(c_5014, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4938, c_42])).
% 5.87/2.26  tff(c_5263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5013, c_5014])).
% 5.87/2.26  tff(c_5265, plain, (![B_555]: (r2_hidden(B_555, '#skF_8') | ~r2_hidden(B_555, '#skF_6'))), inference(splitRight, [status(thm)], [c_4512])).
% 5.87/2.26  tff(c_5604, plain, (![B_567]: (r2_hidden('#skF_1'('#skF_6', B_567), '#skF_8') | r1_tarski('#skF_6', B_567))), inference(resolution, [status(thm)], [c_6, c_5265])).
% 5.87/2.26  tff(c_5613, plain, (r1_tarski('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_5604, c_4])).
% 5.87/2.26  tff(c_5619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2809, c_2809, c_5613])).
% 5.87/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.87/2.26  
% 5.87/2.26  Inference rules
% 5.87/2.26  ----------------------
% 5.87/2.26  #Ref     : 0
% 5.87/2.26  #Sup     : 1183
% 5.87/2.26  #Fact    : 0
% 5.87/2.26  #Define  : 0
% 5.87/2.26  #Split   : 14
% 5.87/2.26  #Chain   : 0
% 5.87/2.26  #Close   : 0
% 5.87/2.26  
% 5.87/2.26  Ordering : KBO
% 5.87/2.26  
% 5.87/2.26  Simplification rules
% 5.87/2.26  ----------------------
% 5.87/2.26  #Subsume      : 452
% 5.87/2.26  #Demod        : 616
% 5.87/2.26  #Tautology    : 201
% 5.87/2.26  #SimpNegUnit  : 31
% 5.87/2.26  #BackRed      : 258
% 5.87/2.26  
% 5.87/2.26  #Partial instantiations: 0
% 5.87/2.26  #Strategies tried      : 1
% 5.87/2.26  
% 5.87/2.26  Timing (in seconds)
% 5.87/2.26  ----------------------
% 5.87/2.26  Preprocessing        : 0.43
% 5.87/2.26  Parsing              : 0.26
% 5.87/2.26  CNF conversion       : 0.02
% 5.87/2.26  Main loop            : 1.04
% 5.87/2.26  Inferencing          : 0.37
% 5.87/2.26  Reduction            : 0.29
% 5.87/2.26  Demodulation         : 0.19
% 5.87/2.26  BG Simplification    : 0.03
% 5.87/2.26  Subsumption          : 0.26
% 5.87/2.26  Abstraction          : 0.04
% 5.87/2.26  MUC search           : 0.00
% 5.87/2.26  Cooper               : 0.00
% 5.87/2.26  Total                : 1.50
% 5.87/2.26  Index Insertion      : 0.00
% 5.87/2.26  Index Deletion       : 0.00
% 5.87/2.26  Index Matching       : 0.00
% 5.87/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
