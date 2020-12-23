%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:50 EST 2020

% Result     : Theorem 7.38s
% Output     : CNFRefutation 7.38s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 188 expanded)
%              Number of leaves         :   39 (  83 expanded)
%              Depth                    :   15
%              Number of atoms          :   98 ( 342 expanded)
%              Number of equality atoms :   27 (  85 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_6 > #skF_15 > #skF_13 > #skF_16 > #skF_12 > #skF_14 > #skF_10 > #skF_2 > #skF_9 > #skF_11 > #skF_3 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_13',type,(
    '#skF_13': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_141,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,C))
       => ( r2_hidden(k1_mcart_1(A),B)
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_123,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_121,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_134,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_96,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_14'),'#skF_16')
    | ~ r2_hidden(k1_mcart_1('#skF_14'),'#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_144,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_14'),'#skF_15') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_98,plain,(
    r2_hidden('#skF_14',k2_zfmisc_1('#skF_15','#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_88,plain,(
    ! [A_71,B_72] : v1_relat_1(k2_zfmisc_1(A_71,B_72)) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2315,plain,(
    ! [A_308,B_309] :
      ( k4_tarski('#skF_12'(A_308,B_309),'#skF_13'(A_308,B_309)) = B_309
      | ~ r2_hidden(B_309,A_308)
      | ~ v1_relat_1(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_92,plain,(
    ! [A_76,B_77] : k1_mcart_1(k4_tarski(A_76,B_77)) = A_76 ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2369,plain,(
    ! [B_314,A_315] :
      ( k1_mcart_1(B_314) = '#skF_12'(A_315,B_314)
      | ~ r2_hidden(B_314,A_315)
      | ~ v1_relat_1(A_315) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2315,c_92])).

tff(c_2417,plain,
    ( '#skF_12'(k2_zfmisc_1('#skF_15','#skF_16'),'#skF_14') = k1_mcart_1('#skF_14')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_15','#skF_16')) ),
    inference(resolution,[status(thm)],[c_98,c_2369])).

tff(c_2444,plain,(
    '#skF_12'(k2_zfmisc_1('#skF_15','#skF_16'),'#skF_14') = k1_mcart_1('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2417])).

tff(c_82,plain,(
    ! [A_53,B_68] :
      ( k4_tarski('#skF_12'(A_53,B_68),'#skF_13'(A_53,B_68)) = B_68
      | ~ r2_hidden(B_68,A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2449,plain,
    ( k4_tarski(k1_mcart_1('#skF_14'),'#skF_13'(k2_zfmisc_1('#skF_15','#skF_16'),'#skF_14')) = '#skF_14'
    | ~ r2_hidden('#skF_14',k2_zfmisc_1('#skF_15','#skF_16'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_15','#skF_16')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2444,c_82])).

tff(c_2453,plain,(
    k4_tarski(k1_mcart_1('#skF_14'),'#skF_13'(k2_zfmisc_1('#skF_15','#skF_16'),'#skF_14')) = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_98,c_2449])).

tff(c_64,plain,(
    ! [A_35,C_37,B_36,D_38] :
      ( r2_hidden(A_35,C_37)
      | ~ r2_hidden(k4_tarski(A_35,B_36),k2_zfmisc_1(C_37,D_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2552,plain,(
    ! [C_322,D_323] :
      ( r2_hidden(k1_mcart_1('#skF_14'),C_322)
      | ~ r2_hidden('#skF_14',k2_zfmisc_1(C_322,D_323)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2453,c_64])).

tff(c_2558,plain,(
    r2_hidden(k1_mcart_1('#skF_14'),'#skF_15') ),
    inference(resolution,[status(thm)],[c_98,c_2552])).

tff(c_2570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_2558])).

tff(c_2571,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_14'),'#skF_16') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_56,plain,(
    ! [B_32,A_31] :
      ( k3_xboole_0(B_32,k1_tarski(A_31)) = k1_tarski(A_31)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_86,plain,(
    ! [A_53] :
      ( r2_hidden('#skF_11'(A_53),A_53)
      | v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2694,plain,(
    ! [D_353,A_354,B_355] :
      ( r2_hidden(D_353,A_354)
      | ~ r2_hidden(D_353,k3_xboole_0(A_354,B_355)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2704,plain,(
    ! [A_354,B_355] :
      ( r2_hidden('#skF_11'(k3_xboole_0(A_354,B_355)),A_354)
      | v1_relat_1(k3_xboole_0(A_354,B_355)) ) ),
    inference(resolution,[status(thm)],[c_86,c_2694])).

tff(c_4465,plain,(
    ! [A_515,B_516] :
      ( k4_tarski('#skF_12'(A_515,B_516),'#skF_13'(A_515,B_516)) = B_516
      | ~ r2_hidden(B_516,A_515)
      | ~ v1_relat_1(A_515) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_84,plain,(
    ! [C_66,D_67,A_53] :
      ( k4_tarski(C_66,D_67) != '#skF_11'(A_53)
      | v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_4475,plain,(
    ! [B_516,A_53,A_515] :
      ( B_516 != '#skF_11'(A_53)
      | v1_relat_1(A_53)
      | ~ r2_hidden(B_516,A_515)
      | ~ v1_relat_1(A_515) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4465,c_84])).

tff(c_4535,plain,(
    ! [A_521,A_522] :
      ( v1_relat_1(A_521)
      | ~ r2_hidden('#skF_11'(A_521),A_522)
      | ~ v1_relat_1(A_522) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4475])).

tff(c_4582,plain,(
    ! [A_527,B_528] :
      ( ~ v1_relat_1(A_527)
      | v1_relat_1(k3_xboole_0(A_527,B_528)) ) ),
    inference(resolution,[status(thm)],[c_2704,c_4535])).

tff(c_4971,plain,(
    ! [B_549,A_550] :
      ( ~ v1_relat_1(B_549)
      | v1_relat_1(k1_tarski(A_550))
      | ~ r2_hidden(A_550,B_549) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_4582])).

tff(c_5005,plain,
    ( ~ v1_relat_1(k2_zfmisc_1('#skF_15','#skF_16'))
    | v1_relat_1(k1_tarski('#skF_14')) ),
    inference(resolution,[status(thm)],[c_98,c_4971])).

tff(c_5032,plain,(
    v1_relat_1(k1_tarski('#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_5005])).

tff(c_30,plain,(
    ! [C_18] : r2_hidden(C_18,k1_tarski(C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6023,plain,(
    ! [B_588,A_589] :
      ( k1_mcart_1(B_588) = '#skF_12'(A_589,B_588)
      | ~ r2_hidden(B_588,A_589)
      | ~ v1_relat_1(A_589) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4465,c_92])).

tff(c_6125,plain,(
    ! [C_590] :
      ( '#skF_12'(k1_tarski(C_590),C_590) = k1_mcart_1(C_590)
      | ~ v1_relat_1(k1_tarski(C_590)) ) ),
    inference(resolution,[status(thm)],[c_30,c_6023])).

tff(c_6143,plain,(
    '#skF_12'(k1_tarski('#skF_14'),'#skF_14') = k1_mcart_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_5032,c_6125])).

tff(c_6166,plain,
    ( k4_tarski(k1_mcart_1('#skF_14'),'#skF_13'(k1_tarski('#skF_14'),'#skF_14')) = '#skF_14'
    | ~ r2_hidden('#skF_14',k1_tarski('#skF_14'))
    | ~ v1_relat_1(k1_tarski('#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6143,c_82])).

tff(c_6170,plain,(
    k4_tarski(k1_mcart_1('#skF_14'),'#skF_13'(k1_tarski('#skF_14'),'#skF_14')) = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5032,c_30,c_6166])).

tff(c_94,plain,(
    ! [A_76,B_77] : k2_mcart_1(k4_tarski(A_76,B_77)) = B_77 ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_6199,plain,(
    '#skF_13'(k1_tarski('#skF_14'),'#skF_14') = k2_mcart_1('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_6170,c_94])).

tff(c_6237,plain,(
    k4_tarski(k1_mcart_1('#skF_14'),k2_mcart_1('#skF_14')) = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6199,c_6170])).

tff(c_62,plain,(
    ! [B_36,D_38,A_35,C_37] :
      ( r2_hidden(B_36,D_38)
      | ~ r2_hidden(k4_tarski(A_35,B_36),k2_zfmisc_1(C_37,D_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6761,plain,(
    ! [D_615,C_616] :
      ( r2_hidden(k2_mcart_1('#skF_14'),D_615)
      | ~ r2_hidden('#skF_14',k2_zfmisc_1(C_616,D_615)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6237,c_62])).

tff(c_6767,plain,(
    r2_hidden(k2_mcart_1('#skF_14'),'#skF_16') ),
    inference(resolution,[status(thm)],[c_98,c_6761])).

tff(c_6779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2571,c_6767])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.38/2.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.38/2.56  
% 7.38/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.38/2.56  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_6 > #skF_15 > #skF_13 > #skF_16 > #skF_12 > #skF_14 > #skF_10 > #skF_2 > #skF_9 > #skF_11 > #skF_3 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 7.38/2.56  
% 7.38/2.56  %Foreground sorts:
% 7.38/2.56  
% 7.38/2.56  
% 7.38/2.56  %Background operators:
% 7.38/2.56  
% 7.38/2.56  
% 7.38/2.56  %Foreground operators:
% 7.38/2.56  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.38/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.38/2.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.38/2.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.38/2.56  tff('#skF_15', type, '#skF_15': $i).
% 7.38/2.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.38/2.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.38/2.56  tff('#skF_13', type, '#skF_13': ($i * $i) > $i).
% 7.38/2.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.38/2.56  tff('#skF_16', type, '#skF_16': $i).
% 7.38/2.56  tff('#skF_12', type, '#skF_12': ($i * $i) > $i).
% 7.38/2.56  tff('#skF_14', type, '#skF_14': $i).
% 7.38/2.56  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 7.38/2.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.38/2.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.38/2.56  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 7.38/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.38/2.56  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 7.38/2.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.38/2.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.38/2.56  tff('#skF_11', type, '#skF_11': $i > $i).
% 7.38/2.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.38/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.38/2.56  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 7.38/2.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.38/2.56  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 7.38/2.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.38/2.56  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 7.38/2.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.38/2.56  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.38/2.56  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.38/2.56  
% 7.38/2.57  tff(f_141, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 7.38/2.57  tff(f_123, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.38/2.57  tff(f_121, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 7.38/2.57  tff(f_134, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 7.38/2.57  tff(f_83, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 7.38/2.57  tff(f_75, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 7.38/2.57  tff(f_46, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.38/2.57  tff(f_53, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 7.38/2.57  tff(c_96, plain, (~r2_hidden(k2_mcart_1('#skF_14'), '#skF_16') | ~r2_hidden(k1_mcart_1('#skF_14'), '#skF_15')), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.38/2.57  tff(c_144, plain, (~r2_hidden(k1_mcart_1('#skF_14'), '#skF_15')), inference(splitLeft, [status(thm)], [c_96])).
% 7.38/2.57  tff(c_98, plain, (r2_hidden('#skF_14', k2_zfmisc_1('#skF_15', '#skF_16'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.38/2.57  tff(c_88, plain, (![A_71, B_72]: (v1_relat_1(k2_zfmisc_1(A_71, B_72)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.38/2.57  tff(c_2315, plain, (![A_308, B_309]: (k4_tarski('#skF_12'(A_308, B_309), '#skF_13'(A_308, B_309))=B_309 | ~r2_hidden(B_309, A_308) | ~v1_relat_1(A_308))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.38/2.57  tff(c_92, plain, (![A_76, B_77]: (k1_mcart_1(k4_tarski(A_76, B_77))=A_76)), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.38/2.57  tff(c_2369, plain, (![B_314, A_315]: (k1_mcart_1(B_314)='#skF_12'(A_315, B_314) | ~r2_hidden(B_314, A_315) | ~v1_relat_1(A_315))), inference(superposition, [status(thm), theory('equality')], [c_2315, c_92])).
% 7.38/2.57  tff(c_2417, plain, ('#skF_12'(k2_zfmisc_1('#skF_15', '#skF_16'), '#skF_14')=k1_mcart_1('#skF_14') | ~v1_relat_1(k2_zfmisc_1('#skF_15', '#skF_16'))), inference(resolution, [status(thm)], [c_98, c_2369])).
% 7.38/2.57  tff(c_2444, plain, ('#skF_12'(k2_zfmisc_1('#skF_15', '#skF_16'), '#skF_14')=k1_mcart_1('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2417])).
% 7.38/2.57  tff(c_82, plain, (![A_53, B_68]: (k4_tarski('#skF_12'(A_53, B_68), '#skF_13'(A_53, B_68))=B_68 | ~r2_hidden(B_68, A_53) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.38/2.57  tff(c_2449, plain, (k4_tarski(k1_mcart_1('#skF_14'), '#skF_13'(k2_zfmisc_1('#skF_15', '#skF_16'), '#skF_14'))='#skF_14' | ~r2_hidden('#skF_14', k2_zfmisc_1('#skF_15', '#skF_16')) | ~v1_relat_1(k2_zfmisc_1('#skF_15', '#skF_16'))), inference(superposition, [status(thm), theory('equality')], [c_2444, c_82])).
% 7.38/2.57  tff(c_2453, plain, (k4_tarski(k1_mcart_1('#skF_14'), '#skF_13'(k2_zfmisc_1('#skF_15', '#skF_16'), '#skF_14'))='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_98, c_2449])).
% 7.38/2.57  tff(c_64, plain, (![A_35, C_37, B_36, D_38]: (r2_hidden(A_35, C_37) | ~r2_hidden(k4_tarski(A_35, B_36), k2_zfmisc_1(C_37, D_38)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.38/2.57  tff(c_2552, plain, (![C_322, D_323]: (r2_hidden(k1_mcart_1('#skF_14'), C_322) | ~r2_hidden('#skF_14', k2_zfmisc_1(C_322, D_323)))), inference(superposition, [status(thm), theory('equality')], [c_2453, c_64])).
% 7.38/2.57  tff(c_2558, plain, (r2_hidden(k1_mcart_1('#skF_14'), '#skF_15')), inference(resolution, [status(thm)], [c_98, c_2552])).
% 7.38/2.57  tff(c_2570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_2558])).
% 7.38/2.57  tff(c_2571, plain, (~r2_hidden(k2_mcart_1('#skF_14'), '#skF_16')), inference(splitRight, [status(thm)], [c_96])).
% 7.38/2.57  tff(c_56, plain, (![B_32, A_31]: (k3_xboole_0(B_32, k1_tarski(A_31))=k1_tarski(A_31) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.38/2.57  tff(c_86, plain, (![A_53]: (r2_hidden('#skF_11'(A_53), A_53) | v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.38/2.57  tff(c_2694, plain, (![D_353, A_354, B_355]: (r2_hidden(D_353, A_354) | ~r2_hidden(D_353, k3_xboole_0(A_354, B_355)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.38/2.57  tff(c_2704, plain, (![A_354, B_355]: (r2_hidden('#skF_11'(k3_xboole_0(A_354, B_355)), A_354) | v1_relat_1(k3_xboole_0(A_354, B_355)))), inference(resolution, [status(thm)], [c_86, c_2694])).
% 7.38/2.57  tff(c_4465, plain, (![A_515, B_516]: (k4_tarski('#skF_12'(A_515, B_516), '#skF_13'(A_515, B_516))=B_516 | ~r2_hidden(B_516, A_515) | ~v1_relat_1(A_515))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.38/2.57  tff(c_84, plain, (![C_66, D_67, A_53]: (k4_tarski(C_66, D_67)!='#skF_11'(A_53) | v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.38/2.57  tff(c_4475, plain, (![B_516, A_53, A_515]: (B_516!='#skF_11'(A_53) | v1_relat_1(A_53) | ~r2_hidden(B_516, A_515) | ~v1_relat_1(A_515))), inference(superposition, [status(thm), theory('equality')], [c_4465, c_84])).
% 7.38/2.57  tff(c_4535, plain, (![A_521, A_522]: (v1_relat_1(A_521) | ~r2_hidden('#skF_11'(A_521), A_522) | ~v1_relat_1(A_522))), inference(reflexivity, [status(thm), theory('equality')], [c_4475])).
% 7.38/2.57  tff(c_4582, plain, (![A_527, B_528]: (~v1_relat_1(A_527) | v1_relat_1(k3_xboole_0(A_527, B_528)))), inference(resolution, [status(thm)], [c_2704, c_4535])).
% 7.38/2.57  tff(c_4971, plain, (![B_549, A_550]: (~v1_relat_1(B_549) | v1_relat_1(k1_tarski(A_550)) | ~r2_hidden(A_550, B_549))), inference(superposition, [status(thm), theory('equality')], [c_56, c_4582])).
% 7.38/2.57  tff(c_5005, plain, (~v1_relat_1(k2_zfmisc_1('#skF_15', '#skF_16')) | v1_relat_1(k1_tarski('#skF_14'))), inference(resolution, [status(thm)], [c_98, c_4971])).
% 7.38/2.57  tff(c_5032, plain, (v1_relat_1(k1_tarski('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_5005])).
% 7.38/2.57  tff(c_30, plain, (![C_18]: (r2_hidden(C_18, k1_tarski(C_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.38/2.57  tff(c_6023, plain, (![B_588, A_589]: (k1_mcart_1(B_588)='#skF_12'(A_589, B_588) | ~r2_hidden(B_588, A_589) | ~v1_relat_1(A_589))), inference(superposition, [status(thm), theory('equality')], [c_4465, c_92])).
% 7.38/2.57  tff(c_6125, plain, (![C_590]: ('#skF_12'(k1_tarski(C_590), C_590)=k1_mcart_1(C_590) | ~v1_relat_1(k1_tarski(C_590)))), inference(resolution, [status(thm)], [c_30, c_6023])).
% 7.38/2.57  tff(c_6143, plain, ('#skF_12'(k1_tarski('#skF_14'), '#skF_14')=k1_mcart_1('#skF_14')), inference(resolution, [status(thm)], [c_5032, c_6125])).
% 7.38/2.57  tff(c_6166, plain, (k4_tarski(k1_mcart_1('#skF_14'), '#skF_13'(k1_tarski('#skF_14'), '#skF_14'))='#skF_14' | ~r2_hidden('#skF_14', k1_tarski('#skF_14')) | ~v1_relat_1(k1_tarski('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_6143, c_82])).
% 7.38/2.57  tff(c_6170, plain, (k4_tarski(k1_mcart_1('#skF_14'), '#skF_13'(k1_tarski('#skF_14'), '#skF_14'))='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_5032, c_30, c_6166])).
% 7.38/2.57  tff(c_94, plain, (![A_76, B_77]: (k2_mcart_1(k4_tarski(A_76, B_77))=B_77)), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.38/2.57  tff(c_6199, plain, ('#skF_13'(k1_tarski('#skF_14'), '#skF_14')=k2_mcart_1('#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_6170, c_94])).
% 7.38/2.57  tff(c_6237, plain, (k4_tarski(k1_mcart_1('#skF_14'), k2_mcart_1('#skF_14'))='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_6199, c_6170])).
% 7.38/2.57  tff(c_62, plain, (![B_36, D_38, A_35, C_37]: (r2_hidden(B_36, D_38) | ~r2_hidden(k4_tarski(A_35, B_36), k2_zfmisc_1(C_37, D_38)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.38/2.57  tff(c_6761, plain, (![D_615, C_616]: (r2_hidden(k2_mcart_1('#skF_14'), D_615) | ~r2_hidden('#skF_14', k2_zfmisc_1(C_616, D_615)))), inference(superposition, [status(thm), theory('equality')], [c_6237, c_62])).
% 7.38/2.57  tff(c_6767, plain, (r2_hidden(k2_mcart_1('#skF_14'), '#skF_16')), inference(resolution, [status(thm)], [c_98, c_6761])).
% 7.38/2.57  tff(c_6779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2571, c_6767])).
% 7.38/2.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.38/2.57  
% 7.38/2.57  Inference rules
% 7.38/2.57  ----------------------
% 7.38/2.57  #Ref     : 1
% 7.38/2.57  #Sup     : 1536
% 7.38/2.57  #Fact    : 0
% 7.38/2.57  #Define  : 0
% 7.38/2.57  #Split   : 15
% 7.38/2.57  #Chain   : 0
% 7.38/2.57  #Close   : 0
% 7.38/2.57  
% 7.38/2.57  Ordering : KBO
% 7.38/2.57  
% 7.38/2.57  Simplification rules
% 7.38/2.57  ----------------------
% 7.38/2.57  #Subsume      : 217
% 7.38/2.57  #Demod        : 256
% 7.38/2.57  #Tautology    : 320
% 7.38/2.57  #SimpNegUnit  : 66
% 7.38/2.58  #BackRed      : 11
% 7.38/2.58  
% 7.38/2.58  #Partial instantiations: 0
% 7.38/2.58  #Strategies tried      : 1
% 7.38/2.58  
% 7.38/2.58  Timing (in seconds)
% 7.38/2.58  ----------------------
% 7.38/2.58  Preprocessing        : 0.35
% 7.38/2.58  Parsing              : 0.19
% 7.38/2.58  CNF conversion       : 0.03
% 7.38/2.58  Main loop            : 1.38
% 7.38/2.58  Inferencing          : 0.46
% 7.38/2.58  Reduction            : 0.39
% 7.38/2.58  Demodulation         : 0.25
% 7.38/2.58  BG Simplification    : 0.05
% 7.38/2.58  Subsumption          : 0.33
% 7.38/2.58  Abstraction          : 0.06
% 7.38/2.58  MUC search           : 0.00
% 7.38/2.58  Cooper               : 0.00
% 7.38/2.58  Total                : 1.76
% 7.38/2.58  Index Insertion      : 0.00
% 7.38/2.58  Index Deletion       : 0.00
% 7.38/2.58  Index Matching       : 0.00
% 7.38/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
