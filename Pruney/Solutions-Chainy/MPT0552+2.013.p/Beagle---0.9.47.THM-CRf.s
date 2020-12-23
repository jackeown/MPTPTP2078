%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:58 EST 2020

% Result     : Theorem 9.37s
% Output     : CNFRefutation 9.37s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 169 expanded)
%              Number of leaves         :   25 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  121 ( 369 expanded)
%              Number of equality atoms :    6 (  28 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k7_relat_1(A_11,B_12))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ! [B_27,A_26] :
      ( r1_tarski(k7_relat_1(B_27,A_26),B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [C_15,A_13,B_14] :
      ( k7_relat_1(k7_relat_1(C_15,A_13),B_14) = k7_relat_1(C_15,k3_xboole_0(A_13,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_857,plain,(
    ! [C_169,A_170,D_171,B_172] :
      ( r1_tarski(k7_relat_1(C_169,A_170),k7_relat_1(D_171,B_172))
      | ~ r1_tarski(A_170,B_172)
      | ~ r1_tarski(C_169,D_171)
      | ~ v1_relat_1(D_171)
      | ~ v1_relat_1(C_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_869,plain,(
    ! [B_172,A_13,D_171,B_14,C_15] :
      ( r1_tarski(k7_relat_1(C_15,k3_xboole_0(A_13,B_14)),k7_relat_1(D_171,B_172))
      | ~ r1_tarski(B_14,B_172)
      | ~ r1_tarski(k7_relat_1(C_15,A_13),D_171)
      | ~ v1_relat_1(D_171)
      | ~ v1_relat_1(k7_relat_1(C_15,A_13))
      | ~ v1_relat_1(C_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_857])).

tff(c_22,plain,(
    ! [B_22,A_21] :
      ( k2_relat_1(k7_relat_1(B_22,A_21)) = k9_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_121,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k2_relat_1(A_60),k2_relat_1(B_61))
      | ~ r1_tarski(A_60,B_61)
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1357,plain,(
    ! [A_238,B_239,A_240] :
      ( r1_tarski(k2_relat_1(A_238),k9_relat_1(B_239,A_240))
      | ~ r1_tarski(A_238,k7_relat_1(B_239,A_240))
      | ~ v1_relat_1(k7_relat_1(B_239,A_240))
      | ~ v1_relat_1(A_238)
      | ~ v1_relat_1(B_239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_121])).

tff(c_9684,plain,(
    ! [B_654,A_655,B_656,A_657] :
      ( r1_tarski(k9_relat_1(B_654,A_655),k9_relat_1(B_656,A_657))
      | ~ r1_tarski(k7_relat_1(B_654,A_655),k7_relat_1(B_656,A_657))
      | ~ v1_relat_1(k7_relat_1(B_656,A_657))
      | ~ v1_relat_1(k7_relat_1(B_654,A_655))
      | ~ v1_relat_1(B_656)
      | ~ v1_relat_1(B_654) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1357])).

tff(c_144,plain,(
    ! [C_64,A_65,B_66] :
      ( k7_relat_1(k7_relat_1(C_64,A_65),B_66) = k7_relat_1(C_64,k3_xboole_0(A_65,B_66))
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_29,A_28)),k2_relat_1(B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_465,plain,(
    ! [C_110,A_111,B_112] :
      ( r1_tarski(k2_relat_1(k7_relat_1(C_110,k3_xboole_0(A_111,B_112))),k2_relat_1(k7_relat_1(C_110,A_111)))
      | ~ v1_relat_1(k7_relat_1(C_110,A_111))
      | ~ v1_relat_1(C_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_30])).

tff(c_706,plain,(
    ! [B_146,A_147,B_148] :
      ( r1_tarski(k9_relat_1(B_146,k3_xboole_0(A_147,B_148)),k2_relat_1(k7_relat_1(B_146,A_147)))
      | ~ v1_relat_1(k7_relat_1(B_146,A_147))
      | ~ v1_relat_1(B_146)
      | ~ v1_relat_1(B_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_465])).

tff(c_768,plain,(
    ! [B_158,A_159,B_160] :
      ( r1_tarski(k9_relat_1(B_158,k3_xboole_0(A_159,B_160)),k9_relat_1(B_158,A_159))
      | ~ v1_relat_1(k7_relat_1(B_158,A_159))
      | ~ v1_relat_1(B_158)
      | ~ v1_relat_1(B_158)
      | ~ v1_relat_1(B_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_706])).

tff(c_108,plain,(
    ! [A_55,B_56,C_57] :
      ( r1_tarski(A_55,k3_xboole_0(B_56,C_57))
      | ~ r1_tarski(A_55,C_57)
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_117,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_108,c_32])).

tff(c_143,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_775,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_768,c_143])).

tff(c_792,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_775])).

tff(c_797,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_792])).

tff(c_801,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_797])).

tff(c_802,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_9698,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_9684,c_802])).

tff(c_9743,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_9698])).

tff(c_9746,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_9743])).

tff(c_9752,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_9746])).

tff(c_9758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_9752])).

tff(c_9759,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_9743])).

tff(c_9916,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_9759])).

tff(c_9919,plain,
    ( ~ r1_tarski('#skF_2','#skF_2')
    | ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_869,c_9916])).

tff(c_9928,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6,c_9919])).

tff(c_9934,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_9928])).

tff(c_9937,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_9934])).

tff(c_9941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_9937])).

tff(c_9942,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_9928])).

tff(c_10016,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_9942])).

tff(c_10020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10016])).

tff(c_10021,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_9759])).

tff(c_10025,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_10021])).

tff(c_10029,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10025])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n018.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 13:41:56 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.37/3.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.37/3.36  
% 9.37/3.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.37/3.36  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 9.37/3.36  
% 9.37/3.36  %Foreground sorts:
% 9.37/3.36  
% 9.37/3.36  
% 9.37/3.36  %Background operators:
% 9.37/3.36  
% 9.37/3.36  
% 9.37/3.36  %Foreground operators:
% 9.37/3.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.37/3.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.37/3.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.37/3.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.37/3.36  tff('#skF_2', type, '#skF_2': $i).
% 9.37/3.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.37/3.36  tff('#skF_3', type, '#skF_3': $i).
% 9.37/3.36  tff('#skF_1', type, '#skF_1': $i).
% 9.37/3.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.37/3.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.37/3.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.37/3.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.37/3.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.37/3.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.37/3.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.37/3.36  
% 9.37/3.37  tff(f_95, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 9.37/3.37  tff(f_52, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 9.37/3.37  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 9.37/3.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.37/3.37  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 9.37/3.37  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_relat_1)).
% 9.37/3.37  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 9.37/3.37  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 9.37/3.37  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 9.37/3.37  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 9.37/3.37  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.37/3.37  tff(c_16, plain, (![A_11, B_12]: (v1_relat_1(k7_relat_1(A_11, B_12)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.37/3.37  tff(c_28, plain, (![B_27, A_26]: (r1_tarski(k7_relat_1(B_27, A_26), B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.37/3.37  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.37/3.37  tff(c_18, plain, (![C_15, A_13, B_14]: (k7_relat_1(k7_relat_1(C_15, A_13), B_14)=k7_relat_1(C_15, k3_xboole_0(A_13, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.37/3.37  tff(c_857, plain, (![C_169, A_170, D_171, B_172]: (r1_tarski(k7_relat_1(C_169, A_170), k7_relat_1(D_171, B_172)) | ~r1_tarski(A_170, B_172) | ~r1_tarski(C_169, D_171) | ~v1_relat_1(D_171) | ~v1_relat_1(C_169))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.37/3.37  tff(c_869, plain, (![B_172, A_13, D_171, B_14, C_15]: (r1_tarski(k7_relat_1(C_15, k3_xboole_0(A_13, B_14)), k7_relat_1(D_171, B_172)) | ~r1_tarski(B_14, B_172) | ~r1_tarski(k7_relat_1(C_15, A_13), D_171) | ~v1_relat_1(D_171) | ~v1_relat_1(k7_relat_1(C_15, A_13)) | ~v1_relat_1(C_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_857])).
% 9.37/3.37  tff(c_22, plain, (![B_22, A_21]: (k2_relat_1(k7_relat_1(B_22, A_21))=k9_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.37/3.37  tff(c_121, plain, (![A_60, B_61]: (r1_tarski(k2_relat_1(A_60), k2_relat_1(B_61)) | ~r1_tarski(A_60, B_61) | ~v1_relat_1(B_61) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.37/3.37  tff(c_1357, plain, (![A_238, B_239, A_240]: (r1_tarski(k2_relat_1(A_238), k9_relat_1(B_239, A_240)) | ~r1_tarski(A_238, k7_relat_1(B_239, A_240)) | ~v1_relat_1(k7_relat_1(B_239, A_240)) | ~v1_relat_1(A_238) | ~v1_relat_1(B_239))), inference(superposition, [status(thm), theory('equality')], [c_22, c_121])).
% 9.37/3.37  tff(c_9684, plain, (![B_654, A_655, B_656, A_657]: (r1_tarski(k9_relat_1(B_654, A_655), k9_relat_1(B_656, A_657)) | ~r1_tarski(k7_relat_1(B_654, A_655), k7_relat_1(B_656, A_657)) | ~v1_relat_1(k7_relat_1(B_656, A_657)) | ~v1_relat_1(k7_relat_1(B_654, A_655)) | ~v1_relat_1(B_656) | ~v1_relat_1(B_654))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1357])).
% 9.37/3.37  tff(c_144, plain, (![C_64, A_65, B_66]: (k7_relat_1(k7_relat_1(C_64, A_65), B_66)=k7_relat_1(C_64, k3_xboole_0(A_65, B_66)) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.37/3.37  tff(c_30, plain, (![B_29, A_28]: (r1_tarski(k2_relat_1(k7_relat_1(B_29, A_28)), k2_relat_1(B_29)) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.37/3.37  tff(c_465, plain, (![C_110, A_111, B_112]: (r1_tarski(k2_relat_1(k7_relat_1(C_110, k3_xboole_0(A_111, B_112))), k2_relat_1(k7_relat_1(C_110, A_111))) | ~v1_relat_1(k7_relat_1(C_110, A_111)) | ~v1_relat_1(C_110))), inference(superposition, [status(thm), theory('equality')], [c_144, c_30])).
% 9.37/3.37  tff(c_706, plain, (![B_146, A_147, B_148]: (r1_tarski(k9_relat_1(B_146, k3_xboole_0(A_147, B_148)), k2_relat_1(k7_relat_1(B_146, A_147))) | ~v1_relat_1(k7_relat_1(B_146, A_147)) | ~v1_relat_1(B_146) | ~v1_relat_1(B_146))), inference(superposition, [status(thm), theory('equality')], [c_22, c_465])).
% 9.37/3.37  tff(c_768, plain, (![B_158, A_159, B_160]: (r1_tarski(k9_relat_1(B_158, k3_xboole_0(A_159, B_160)), k9_relat_1(B_158, A_159)) | ~v1_relat_1(k7_relat_1(B_158, A_159)) | ~v1_relat_1(B_158) | ~v1_relat_1(B_158) | ~v1_relat_1(B_158))), inference(superposition, [status(thm), theory('equality')], [c_22, c_706])).
% 9.37/3.37  tff(c_108, plain, (![A_55, B_56, C_57]: (r1_tarski(A_55, k3_xboole_0(B_56, C_57)) | ~r1_tarski(A_55, C_57) | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.37/3.37  tff(c_32, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.37/3.37  tff(c_117, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_108, c_32])).
% 9.37/3.37  tff(c_143, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_117])).
% 9.37/3.37  tff(c_775, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_768, c_143])).
% 9.37/3.37  tff(c_792, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_775])).
% 9.37/3.37  tff(c_797, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_792])).
% 9.37/3.37  tff(c_801, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_797])).
% 9.37/3.37  tff(c_802, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_117])).
% 9.37/3.37  tff(c_9698, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_9684, c_802])).
% 9.37/3.37  tff(c_9743, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_9698])).
% 9.37/3.37  tff(c_9746, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_9743])).
% 9.37/3.37  tff(c_9752, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_9746])).
% 9.37/3.37  tff(c_9758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_9752])).
% 9.37/3.37  tff(c_9759, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_9743])).
% 9.37/3.37  tff(c_9916, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_9759])).
% 9.37/3.37  tff(c_9919, plain, (~r1_tarski('#skF_2', '#skF_2') | ~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_869, c_9916])).
% 9.37/3.37  tff(c_9928, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6, c_9919])).
% 9.37/3.37  tff(c_9934, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_9928])).
% 9.37/3.37  tff(c_9937, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_9934])).
% 9.37/3.37  tff(c_9941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_9937])).
% 9.37/3.37  tff(c_9942, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_9928])).
% 9.37/3.37  tff(c_10016, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_9942])).
% 9.37/3.37  tff(c_10020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_10016])).
% 9.37/3.37  tff(c_10021, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_9759])).
% 9.37/3.37  tff(c_10025, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_10021])).
% 9.37/3.37  tff(c_10029, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_10025])).
% 9.37/3.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.37/3.37  
% 9.37/3.37  Inference rules
% 9.37/3.37  ----------------------
% 9.37/3.37  #Ref     : 0
% 9.37/3.37  #Sup     : 2875
% 9.37/3.37  #Fact    : 0
% 9.37/3.37  #Define  : 0
% 9.37/3.37  #Split   : 7
% 9.37/3.37  #Chain   : 0
% 9.37/3.37  #Close   : 0
% 9.37/3.37  
% 9.37/3.37  Ordering : KBO
% 9.37/3.37  
% 9.37/3.37  Simplification rules
% 9.37/3.37  ----------------------
% 9.37/3.37  #Subsume      : 665
% 9.37/3.37  #Demod        : 113
% 9.37/3.37  #Tautology    : 70
% 9.37/3.37  #SimpNegUnit  : 0
% 9.37/3.37  #BackRed      : 0
% 9.37/3.37  
% 9.37/3.37  #Partial instantiations: 0
% 9.37/3.37  #Strategies tried      : 1
% 9.37/3.37  
% 9.37/3.37  Timing (in seconds)
% 9.37/3.37  ----------------------
% 9.37/3.38  Preprocessing        : 0.29
% 9.37/3.38  Parsing              : 0.17
% 9.37/3.38  CNF conversion       : 0.02
% 9.37/3.38  Main loop            : 2.33
% 9.37/3.38  Inferencing          : 0.66
% 9.37/3.38  Reduction            : 0.46
% 9.37/3.38  Demodulation         : 0.30
% 9.37/3.38  BG Simplification    : 0.10
% 9.37/3.38  Subsumption          : 0.95
% 9.37/3.38  Abstraction          : 0.11
% 9.37/3.38  MUC search           : 0.00
% 9.37/3.38  Cooper               : 0.00
% 9.37/3.38  Total                : 2.65
% 9.37/3.38  Index Insertion      : 0.00
% 9.37/3.38  Index Deletion       : 0.00
% 9.37/3.38  Index Matching       : 0.00
% 9.37/3.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
