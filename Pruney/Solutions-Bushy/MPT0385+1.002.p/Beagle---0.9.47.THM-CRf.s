%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0385+1.002 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 8.17s
% Output     : CNFRefutation 8.53s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 263 expanded)
%              Number of leaves         :   29 (  99 expanded)
%              Depth                    :   15
%              Number of atoms          :  119 ( 699 expanded)
%              Number of equality atoms :   26 ( 139 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_11 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_5 > #skF_4

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

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
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

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_78,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_setfam_1(A),k3_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_setfam_1)).

tff(f_71,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_63,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( r2_hidden('#skF_5'(A_20,B_21),A_20)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_115,plain,(
    ! [C_75,D_76,A_77] :
      ( r2_hidden(C_75,D_76)
      | ~ r2_hidden(D_76,A_77)
      | ~ r2_hidden(C_75,k1_setfam_1(A_77))
      | k1_xboole_0 = A_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_342,plain,(
    ! [C_108,A_109,B_110] :
      ( r2_hidden(C_108,'#skF_5'(A_109,B_110))
      | ~ r2_hidden(C_108,k1_setfam_1(A_109))
      | k1_xboole_0 = A_109
      | r1_tarski(A_109,B_110) ) ),
    inference(resolution,[status(thm)],[c_28,c_115])).

tff(c_3701,plain,(
    ! [A_287,B_288,B_289] :
      ( r2_hidden('#skF_5'(k1_setfam_1(A_287),B_288),'#skF_5'(A_287,B_289))
      | k1_xboole_0 = A_287
      | r1_tarski(A_287,B_289)
      | r1_tarski(k1_setfam_1(A_287),B_288) ) ),
    inference(resolution,[status(thm)],[c_28,c_342])).

tff(c_86,plain,(
    ! [C_63,A_64,D_65] :
      ( r2_hidden(C_63,k3_tarski(A_64))
      | ~ r2_hidden(D_65,A_64)
      | ~ r2_hidden(C_63,D_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_92,plain,(
    ! [C_63,A_20,B_21] :
      ( r2_hidden(C_63,k3_tarski(A_20))
      | ~ r2_hidden(C_63,'#skF_5'(A_20,B_21))
      | r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_28,c_86])).

tff(c_3857,plain,(
    ! [A_294,B_295,B_296] :
      ( r2_hidden('#skF_5'(k1_setfam_1(A_294),B_295),k3_tarski(A_294))
      | k1_xboole_0 = A_294
      | r1_tarski(A_294,B_296)
      | r1_tarski(k1_setfam_1(A_294),B_295) ) ),
    inference(resolution,[status(thm)],[c_3701,c_92])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( ~ r2_hidden('#skF_5'(A_20,B_21),B_21)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3979,plain,(
    ! [A_300,B_301] :
      ( k1_xboole_0 = A_300
      | r1_tarski(A_300,B_301)
      | r1_tarski(k1_setfam_1(A_300),k3_tarski(A_300)) ) ),
    inference(resolution,[status(thm)],[c_3857,c_26])).

tff(c_56,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_11'),k3_tarski('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4025,plain,(
    ! [B_301] :
      ( k1_xboole_0 = '#skF_11'
      | r1_tarski('#skF_11',B_301) ) ),
    inference(resolution,[status(thm)],[c_3979,c_56])).

tff(c_4028,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_4025])).

tff(c_52,plain,(
    ! [A_48] : r1_tarski(k1_xboole_0,A_48) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4075,plain,(
    ! [A_48] : r1_tarski('#skF_11',A_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4028,c_52])).

tff(c_22,plain,(
    k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4074,plain,(
    k1_setfam_1('#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4028,c_4028,c_22])).

tff(c_4081,plain,(
    ~ r1_tarski('#skF_11',k3_tarski('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4074,c_56])).

tff(c_4108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4075,c_4081])).

tff(c_4110,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitRight,[status(thm)],[c_4025])).

tff(c_48,plain,(
    ! [A_44] : m1_subset_1('#skF_10'(A_44),A_44) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4272,plain,(
    ! [B_307] : r1_tarski('#skF_11',B_307) ),
    inference(splitRight,[status(thm)],[c_4025])).

tff(c_50,plain,(
    ! [A_46,B_47] :
      ( r2_hidden(A_46,B_47)
      | v1_xboole_0(B_47)
      | ~ m1_subset_1(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_79,plain,(
    ! [C_60,B_61,A_62] :
      ( r2_hidden(C_60,B_61)
      | ~ r2_hidden(C_60,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_84,plain,(
    ! [A_46,B_61,B_47] :
      ( r2_hidden(A_46,B_61)
      | ~ r1_tarski(B_47,B_61)
      | v1_xboole_0(B_47)
      | ~ m1_subset_1(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_50,c_79])).

tff(c_4293,plain,(
    ! [A_46,B_307] :
      ( r2_hidden(A_46,B_307)
      | v1_xboole_0('#skF_11')
      | ~ m1_subset_1(A_46,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_4272,c_84])).

tff(c_4294,plain,(
    v1_xboole_0('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_4293])).

tff(c_54,plain,(
    ! [A_49] :
      ( k1_xboole_0 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4395,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_4294,c_54])).

tff(c_4399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4110,c_4395])).

tff(c_4402,plain,(
    ! [A_310,B_311] :
      ( r2_hidden(A_310,B_311)
      | ~ m1_subset_1(A_310,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_4293])).

tff(c_32,plain,(
    ! [A_25,C_40] :
      ( r2_hidden('#skF_9'(A_25,k3_tarski(A_25),C_40),A_25)
      | ~ r2_hidden(C_40,k3_tarski(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2932,plain,(
    ! [C_263,A_264,C_265] :
      ( r2_hidden(C_263,'#skF_9'(A_264,k3_tarski(A_264),C_265))
      | ~ r2_hidden(C_263,k1_setfam_1(A_264))
      | k1_xboole_0 = A_264
      | ~ r2_hidden(C_265,k3_tarski(A_264)) ) ),
    inference(resolution,[status(thm)],[c_32,c_115])).

tff(c_101,plain,(
    ! [A_70,C_71] :
      ( r2_hidden('#skF_9'(A_70,k3_tarski(A_70),C_71),A_70)
      | ~ r2_hidden(C_71,k3_tarski(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    ! [C_40,A_25,D_43] :
      ( r2_hidden(C_40,k3_tarski(A_25))
      | ~ r2_hidden(D_43,A_25)
      | ~ r2_hidden(C_40,D_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_106,plain,(
    ! [C_40,A_70,C_71] :
      ( r2_hidden(C_40,k3_tarski(A_70))
      | ~ r2_hidden(C_40,'#skF_9'(A_70,k3_tarski(A_70),C_71))
      | ~ r2_hidden(C_71,k3_tarski(A_70)) ) ),
    inference(resolution,[status(thm)],[c_101,c_30])).

tff(c_2969,plain,(
    ! [C_263,A_264,C_265] :
      ( r2_hidden(C_263,k3_tarski(A_264))
      | ~ r2_hidden(C_263,k1_setfam_1(A_264))
      | k1_xboole_0 = A_264
      | ~ r2_hidden(C_265,k3_tarski(A_264)) ) ),
    inference(resolution,[status(thm)],[c_2932,c_106])).

tff(c_4488,plain,(
    ! [C_263,A_264,A_310] :
      ( r2_hidden(C_263,k3_tarski(A_264))
      | ~ r2_hidden(C_263,k1_setfam_1(A_264))
      | k1_xboole_0 = A_264
      | ~ m1_subset_1(A_310,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_4402,c_2969])).

tff(c_7008,plain,(
    ! [A_392] : ~ m1_subset_1(A_392,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_4488])).

tff(c_7013,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_48,c_7008])).

tff(c_7015,plain,(
    ! [C_393,A_394] :
      ( r2_hidden(C_393,k3_tarski(A_394))
      | ~ r2_hidden(C_393,k1_setfam_1(A_394))
      | k1_xboole_0 = A_394 ) ),
    inference(splitRight,[status(thm)],[c_4488])).

tff(c_7271,plain,(
    ! [A_400,A_401] :
      ( r1_tarski(A_400,k3_tarski(A_401))
      | ~ r2_hidden('#skF_5'(A_400,k3_tarski(A_401)),k1_setfam_1(A_401))
      | k1_xboole_0 = A_401 ) ),
    inference(resolution,[status(thm)],[c_7015,c_26])).

tff(c_7294,plain,(
    ! [A_402] :
      ( k1_xboole_0 = A_402
      | r1_tarski(k1_setfam_1(A_402),k3_tarski(A_402)) ) ),
    inference(resolution,[status(thm)],[c_28,c_7271])).

tff(c_7305,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_7294,c_56])).

tff(c_7316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4110,c_7305])).

%------------------------------------------------------------------------------
