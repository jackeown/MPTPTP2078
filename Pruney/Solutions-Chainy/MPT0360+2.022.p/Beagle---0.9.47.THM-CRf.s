%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:21 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 457 expanded)
%              Number of leaves         :   24 ( 164 expanded)
%              Depth                    :   16
%              Number of atoms          :  107 ( 831 expanded)
%              Number of equality atoms :   36 ( 319 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_580,plain,(
    ! [A_69,B_70,C_71] :
      ( ~ r2_hidden('#skF_1'(A_69,B_70,C_71),B_70)
      | r2_hidden('#skF_2'(A_69,B_70,C_71),C_71)
      | k4_xboole_0(A_69,B_70) = C_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_601,plain,(
    ! [A_72,C_73] :
      ( r2_hidden('#skF_2'(A_72,A_72,C_73),C_73)
      | k4_xboole_0(A_72,A_72) = C_73 ) ),
    inference(resolution,[status(thm)],[c_18,c_580])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_59,plain,(
    ! [B_8] : k3_xboole_0(B_8,B_8) = B_8 ),
    inference(resolution,[status(thm)],[c_24,c_44])).

tff(c_95,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_104,plain,(
    ! [B_8] : k5_xboole_0(B_8,B_8) = k4_xboole_0(B_8,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_95])).

tff(c_30,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_58,plain,(
    ! [A_13] : k3_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_44])).

tff(c_113,plain,(
    ! [A_13] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_95])).

tff(c_259,plain,(
    ! [D_46,A_47,B_48] :
      ( r2_hidden(D_46,k4_xboole_0(A_47,B_48))
      | r2_hidden(D_46,B_48)
      | ~ r2_hidden(D_46,A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_286,plain,(
    ! [D_46,A_13] :
      ( r2_hidden(D_46,k5_xboole_0(k1_xboole_0,k1_xboole_0))
      | r2_hidden(D_46,A_13)
      | ~ r2_hidden(D_46,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_259])).

tff(c_378,plain,(
    ! [D_60,A_61] :
      ( r2_hidden(D_60,k4_xboole_0(k1_xboole_0,k1_xboole_0))
      | r2_hidden(D_60,A_61)
      | ~ r2_hidden(D_60,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_286])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_428,plain,(
    ! [D_60,A_61] :
      ( r2_hidden(D_60,A_61)
      | ~ r2_hidden(D_60,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_378,c_4])).

tff(c_639,plain,(
    ! [A_72,A_61] :
      ( r2_hidden('#skF_2'(A_72,A_72,k1_xboole_0),A_61)
      | k4_xboole_0(A_72,A_72) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_601,c_428])).

tff(c_649,plain,(
    ! [A_74,A_75] :
      ( r2_hidden('#skF_2'(A_74,A_74,k1_xboole_0),A_75)
      | k4_xboole_0(A_74,A_74) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_601,c_428])).

tff(c_38,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_60,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_44])).

tff(c_110,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_95])).

tff(c_125,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k4_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_110])).

tff(c_327,plain,(
    ! [D_54] :
      ( r2_hidden(D_54,k4_xboole_0('#skF_4','#skF_4'))
      | r2_hidden(D_54,'#skF_5')
      | ~ r2_hidden(D_54,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_259])).

tff(c_347,plain,(
    ! [D_55] :
      ( r2_hidden(D_55,'#skF_5')
      | ~ r2_hidden(D_55,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_327,c_4])).

tff(c_130,plain,(
    ! [A_25] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_95])).

tff(c_133,plain,(
    ! [A_25,A_13] : k4_xboole_0(k1_xboole_0,A_25) = k4_xboole_0(k1_xboole_0,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_113])).

tff(c_201,plain,(
    ! [D_31,B_32,A_33] :
      ( ~ r2_hidden(D_31,B_32)
      | ~ r2_hidden(D_31,k4_xboole_0(A_33,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_207,plain,(
    ! [D_31,A_25,A_13] :
      ( ~ r2_hidden(D_31,A_25)
      | ~ r2_hidden(D_31,k4_xboole_0(k1_xboole_0,A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_201])).

tff(c_350,plain,(
    ! [D_55,A_13] :
      ( ~ r2_hidden(D_55,k4_xboole_0(k1_xboole_0,A_13))
      | ~ r2_hidden(D_55,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_347,c_207])).

tff(c_697,plain,(
    ! [A_76] :
      ( ~ r2_hidden('#skF_2'(A_76,A_76,k1_xboole_0),'#skF_4')
      | k4_xboole_0(A_76,A_76) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_649,c_350])).

tff(c_702,plain,(
    ! [A_72] : k4_xboole_0(A_72,A_72) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_639,c_697])).

tff(c_597,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k4_xboole_0(A_1,A_1) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_580])).

tff(c_716,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k1_xboole_0 = C_3 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_597])).

tff(c_346,plain,(
    ! [D_54] :
      ( r2_hidden(D_54,'#skF_5')
      | ~ r2_hidden(D_54,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_327,c_4])).

tff(c_36,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_57,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_44])).

tff(c_107,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = k5_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_95])).

tff(c_229,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = k4_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_107])).

tff(c_719,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_229])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k4_xboole_0(A_1,B_2))
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1168,plain,(
    ! [D_111] :
      ( r2_hidden(D_111,k1_xboole_0)
      | r2_hidden(D_111,k3_subset_1('#skF_3','#skF_5'))
      | ~ r2_hidden(D_111,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_2])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_243,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = k3_subset_1(A_43,B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_247,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_243])).

tff(c_254,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,'#skF_5')
      | ~ r2_hidden(D_6,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_4])).

tff(c_1224,plain,(
    ! [D_114] :
      ( ~ r2_hidden(D_114,'#skF_5')
      | r2_hidden(D_114,k1_xboole_0)
      | ~ r2_hidden(D_114,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1168,c_254])).

tff(c_721,plain,(
    ! [B_8] : k5_xboole_0(B_8,B_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_104])).

tff(c_770,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_113])).

tff(c_778,plain,(
    ! [D_55] :
      ( ~ r2_hidden(D_55,k1_xboole_0)
      | ~ r2_hidden(D_55,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_350])).

tff(c_1269,plain,(
    ! [D_115] :
      ( ~ r2_hidden(D_115,'#skF_5')
      | ~ r2_hidden(D_115,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1224,c_778])).

tff(c_1303,plain,(
    ! [D_116] : ~ r2_hidden(D_116,'#skF_4') ),
    inference(resolution,[status(thm)],[c_346,c_1269])).

tff(c_1317,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_716,c_1303])).

tff(c_1333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:20:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.50  
% 3.22/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.51  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 3.22/1.51  
% 3.22/1.51  %Foreground sorts:
% 3.22/1.51  
% 3.22/1.51  
% 3.22/1.51  %Background operators:
% 3.22/1.51  
% 3.22/1.51  
% 3.22/1.51  %Foreground operators:
% 3.22/1.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.22/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.22/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.22/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.51  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.22/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.22/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.22/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.22/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.22/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.51  
% 3.22/1.52  tff(f_62, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 3.22/1.52  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.22/1.52  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.22/1.52  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.22/1.52  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.22/1.52  tff(f_49, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.22/1.52  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.22/1.52  tff(c_34, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.22/1.52  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.52  tff(c_580, plain, (![A_69, B_70, C_71]: (~r2_hidden('#skF_1'(A_69, B_70, C_71), B_70) | r2_hidden('#skF_2'(A_69, B_70, C_71), C_71) | k4_xboole_0(A_69, B_70)=C_71)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.52  tff(c_601, plain, (![A_72, C_73]: (r2_hidden('#skF_2'(A_72, A_72, C_73), C_73) | k4_xboole_0(A_72, A_72)=C_73)), inference(resolution, [status(thm)], [c_18, c_580])).
% 3.22/1.52  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.22/1.52  tff(c_44, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.22/1.52  tff(c_59, plain, (![B_8]: (k3_xboole_0(B_8, B_8)=B_8)), inference(resolution, [status(thm)], [c_24, c_44])).
% 3.22/1.52  tff(c_95, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.22/1.52  tff(c_104, plain, (![B_8]: (k5_xboole_0(B_8, B_8)=k4_xboole_0(B_8, B_8))), inference(superposition, [status(thm), theory('equality')], [c_59, c_95])).
% 3.22/1.52  tff(c_30, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.22/1.52  tff(c_58, plain, (![A_13]: (k3_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_44])).
% 3.22/1.52  tff(c_113, plain, (![A_13]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_13))), inference(superposition, [status(thm), theory('equality')], [c_58, c_95])).
% 3.22/1.52  tff(c_259, plain, (![D_46, A_47, B_48]: (r2_hidden(D_46, k4_xboole_0(A_47, B_48)) | r2_hidden(D_46, B_48) | ~r2_hidden(D_46, A_47))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.52  tff(c_286, plain, (![D_46, A_13]: (r2_hidden(D_46, k5_xboole_0(k1_xboole_0, k1_xboole_0)) | r2_hidden(D_46, A_13) | ~r2_hidden(D_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_113, c_259])).
% 3.22/1.52  tff(c_378, plain, (![D_60, A_61]: (r2_hidden(D_60, k4_xboole_0(k1_xboole_0, k1_xboole_0)) | r2_hidden(D_60, A_61) | ~r2_hidden(D_60, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_286])).
% 3.22/1.52  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.52  tff(c_428, plain, (![D_60, A_61]: (r2_hidden(D_60, A_61) | ~r2_hidden(D_60, k1_xboole_0))), inference(resolution, [status(thm)], [c_378, c_4])).
% 3.22/1.52  tff(c_639, plain, (![A_72, A_61]: (r2_hidden('#skF_2'(A_72, A_72, k1_xboole_0), A_61) | k4_xboole_0(A_72, A_72)=k1_xboole_0)), inference(resolution, [status(thm)], [c_601, c_428])).
% 3.22/1.52  tff(c_649, plain, (![A_74, A_75]: (r2_hidden('#skF_2'(A_74, A_74, k1_xboole_0), A_75) | k4_xboole_0(A_74, A_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_601, c_428])).
% 3.22/1.52  tff(c_38, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.22/1.52  tff(c_60, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_38, c_44])).
% 3.22/1.52  tff(c_110, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_60, c_95])).
% 3.22/1.52  tff(c_125, plain, (k4_xboole_0('#skF_4', '#skF_5')=k4_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_110])).
% 3.22/1.52  tff(c_327, plain, (![D_54]: (r2_hidden(D_54, k4_xboole_0('#skF_4', '#skF_4')) | r2_hidden(D_54, '#skF_5') | ~r2_hidden(D_54, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_125, c_259])).
% 3.22/1.52  tff(c_347, plain, (![D_55]: (r2_hidden(D_55, '#skF_5') | ~r2_hidden(D_55, '#skF_4'))), inference(resolution, [status(thm)], [c_327, c_4])).
% 3.22/1.52  tff(c_130, plain, (![A_25]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_25))), inference(superposition, [status(thm), theory('equality')], [c_58, c_95])).
% 3.22/1.52  tff(c_133, plain, (![A_25, A_13]: (k4_xboole_0(k1_xboole_0, A_25)=k4_xboole_0(k1_xboole_0, A_13))), inference(superposition, [status(thm), theory('equality')], [c_130, c_113])).
% 3.22/1.52  tff(c_201, plain, (![D_31, B_32, A_33]: (~r2_hidden(D_31, B_32) | ~r2_hidden(D_31, k4_xboole_0(A_33, B_32)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.52  tff(c_207, plain, (![D_31, A_25, A_13]: (~r2_hidden(D_31, A_25) | ~r2_hidden(D_31, k4_xboole_0(k1_xboole_0, A_13)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_201])).
% 3.22/1.52  tff(c_350, plain, (![D_55, A_13]: (~r2_hidden(D_55, k4_xboole_0(k1_xboole_0, A_13)) | ~r2_hidden(D_55, '#skF_4'))), inference(resolution, [status(thm)], [c_347, c_207])).
% 3.22/1.52  tff(c_697, plain, (![A_76]: (~r2_hidden('#skF_2'(A_76, A_76, k1_xboole_0), '#skF_4') | k4_xboole_0(A_76, A_76)=k1_xboole_0)), inference(resolution, [status(thm)], [c_649, c_350])).
% 3.22/1.52  tff(c_702, plain, (![A_72]: (k4_xboole_0(A_72, A_72)=k1_xboole_0)), inference(resolution, [status(thm)], [c_639, c_697])).
% 3.22/1.52  tff(c_597, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k4_xboole_0(A_1, A_1)=C_3)), inference(resolution, [status(thm)], [c_18, c_580])).
% 3.22/1.52  tff(c_716, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k1_xboole_0=C_3)), inference(demodulation, [status(thm), theory('equality')], [c_702, c_597])).
% 3.22/1.52  tff(c_346, plain, (![D_54]: (r2_hidden(D_54, '#skF_5') | ~r2_hidden(D_54, '#skF_4'))), inference(resolution, [status(thm)], [c_327, c_4])).
% 3.22/1.52  tff(c_36, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.22/1.52  tff(c_57, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_36, c_44])).
% 3.22/1.52  tff(c_107, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))=k5_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_57, c_95])).
% 3.22/1.52  tff(c_229, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))=k4_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_107])).
% 3.22/1.52  tff(c_719, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_702, c_229])).
% 3.22/1.52  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k4_xboole_0(A_1, B_2)) | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.52  tff(c_1168, plain, (![D_111]: (r2_hidden(D_111, k1_xboole_0) | r2_hidden(D_111, k3_subset_1('#skF_3', '#skF_5')) | ~r2_hidden(D_111, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_719, c_2])).
% 3.22/1.52  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.22/1.52  tff(c_243, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=k3_subset_1(A_43, B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.22/1.52  tff(c_247, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_243])).
% 3.22/1.52  tff(c_254, plain, (![D_6]: (~r2_hidden(D_6, '#skF_5') | ~r2_hidden(D_6, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_247, c_4])).
% 3.22/1.52  tff(c_1224, plain, (![D_114]: (~r2_hidden(D_114, '#skF_5') | r2_hidden(D_114, k1_xboole_0) | ~r2_hidden(D_114, '#skF_4'))), inference(resolution, [status(thm)], [c_1168, c_254])).
% 3.22/1.52  tff(c_721, plain, (![B_8]: (k5_xboole_0(B_8, B_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_702, c_104])).
% 3.22/1.52  tff(c_770, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_721, c_113])).
% 3.22/1.52  tff(c_778, plain, (![D_55]: (~r2_hidden(D_55, k1_xboole_0) | ~r2_hidden(D_55, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_770, c_350])).
% 3.22/1.52  tff(c_1269, plain, (![D_115]: (~r2_hidden(D_115, '#skF_5') | ~r2_hidden(D_115, '#skF_4'))), inference(resolution, [status(thm)], [c_1224, c_778])).
% 3.22/1.52  tff(c_1303, plain, (![D_116]: (~r2_hidden(D_116, '#skF_4'))), inference(resolution, [status(thm)], [c_346, c_1269])).
% 3.22/1.52  tff(c_1317, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_716, c_1303])).
% 3.22/1.52  tff(c_1333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1317])).
% 3.22/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.52  
% 3.22/1.52  Inference rules
% 3.22/1.52  ----------------------
% 3.22/1.52  #Ref     : 0
% 3.22/1.52  #Sup     : 289
% 3.22/1.52  #Fact    : 2
% 3.22/1.52  #Define  : 0
% 3.22/1.52  #Split   : 3
% 3.22/1.52  #Chain   : 0
% 3.22/1.52  #Close   : 0
% 3.22/1.52  
% 3.22/1.52  Ordering : KBO
% 3.22/1.52  
% 3.22/1.52  Simplification rules
% 3.22/1.52  ----------------------
% 3.22/1.52  #Subsume      : 88
% 3.22/1.52  #Demod        : 68
% 3.22/1.52  #Tautology    : 73
% 3.22/1.52  #SimpNegUnit  : 6
% 3.22/1.52  #BackRed      : 18
% 3.22/1.52  
% 3.22/1.52  #Partial instantiations: 0
% 3.22/1.52  #Strategies tried      : 1
% 3.22/1.52  
% 3.22/1.52  Timing (in seconds)
% 3.22/1.52  ----------------------
% 3.22/1.52  Preprocessing        : 0.29
% 3.22/1.52  Parsing              : 0.15
% 3.22/1.52  CNF conversion       : 0.02
% 3.22/1.52  Main loop            : 0.46
% 3.22/1.52  Inferencing          : 0.17
% 3.22/1.52  Reduction            : 0.14
% 3.22/1.52  Demodulation         : 0.10
% 3.22/1.52  BG Simplification    : 0.02
% 3.22/1.52  Subsumption          : 0.10
% 3.22/1.52  Abstraction          : 0.02
% 3.22/1.53  MUC search           : 0.00
% 3.22/1.53  Cooper               : 0.00
% 3.22/1.53  Total                : 0.79
% 3.22/1.53  Index Insertion      : 0.00
% 3.22/1.53  Index Deletion       : 0.00
% 3.22/1.53  Index Matching       : 0.00
% 3.22/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
