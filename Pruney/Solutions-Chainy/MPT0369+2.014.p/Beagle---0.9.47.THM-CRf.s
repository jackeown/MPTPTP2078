%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:52 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 131 expanded)
%              Number of leaves         :   31 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  107 ( 248 expanded)
%              Number of equality atoms :   25 (  45 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_58,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_60,plain,(
    m1_subset_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_90,plain,(
    ! [B_43,A_44] :
      ( v1_xboole_0(B_43)
      | ~ m1_subset_1(B_43,A_44)
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_102,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_90])).

tff(c_103,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_48,plain,(
    ! [B_28,A_27] :
      ( r2_hidden(B_28,A_27)
      | ~ m1_subset_1(B_28,A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_58,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_618,plain,(
    ! [A_99,B_100] :
      ( k4_xboole_0(A_99,B_100) = k3_subset_1(A_99,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_632,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_618])).

tff(c_722,plain,(
    ! [D_103,A_104,B_105] :
      ( r2_hidden(D_103,k4_xboole_0(A_104,B_105))
      | r2_hidden(D_103,B_105)
      | ~ r2_hidden(D_103,A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_780,plain,(
    ! [D_107] :
      ( r2_hidden(D_107,k3_subset_1('#skF_5','#skF_6'))
      | r2_hidden(D_107,'#skF_6')
      | ~ r2_hidden(D_107,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_722])).

tff(c_56,plain,(
    ~ r2_hidden('#skF_7',k3_subset_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_802,plain,
    ( r2_hidden('#skF_7','#skF_6')
    | ~ r2_hidden('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_780,c_56])).

tff(c_817,plain,(
    ~ r2_hidden('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_802])).

tff(c_821,plain,
    ( ~ m1_subset_1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_817])).

tff(c_824,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_821])).

tff(c_826,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_824])).

tff(c_828,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_38,plain,(
    ! [A_20] : k3_xboole_0(A_20,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_841,plain,(
    ! [A_113,B_114] : k5_xboole_0(A_113,k3_xboole_0(A_113,B_114)) = k4_xboole_0(A_113,B_114) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_850,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = k4_xboole_0(A_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_841])).

tff(c_853,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_850])).

tff(c_907,plain,(
    ! [D_120,B_121,A_122] :
      ( ~ r2_hidden(D_120,B_121)
      | ~ r2_hidden(D_120,k4_xboole_0(A_122,B_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_927,plain,(
    ! [D_125,A_126] :
      ( ~ r2_hidden(D_125,k1_xboole_0)
      | ~ r2_hidden(D_125,A_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_853,c_907])).

tff(c_939,plain,(
    ! [A_126] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0),A_126)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_927])).

tff(c_942,plain,(
    ! [A_127] : ~ r2_hidden('#skF_1'(k1_xboole_0),A_127) ),
    inference(splitLeft,[status(thm)],[c_939])).

tff(c_952,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_942])).

tff(c_892,plain,(
    ! [A_118,B_119] :
      ( r2_hidden('#skF_2'(A_118,B_119),A_118)
      | r1_tarski(A_118,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_906,plain,(
    ! [A_118,B_119] :
      ( ~ v1_xboole_0(A_118)
      | r1_tarski(A_118,B_119) ) ),
    inference(resolution,[status(thm)],[c_892,c_2])).

tff(c_990,plain,(
    ! [B_132,A_133] :
      ( B_132 = A_133
      | ~ r1_tarski(B_132,A_133)
      | ~ r1_tarski(A_133,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1000,plain,(
    ! [B_134,A_135] :
      ( B_134 = A_135
      | ~ r1_tarski(B_134,A_135)
      | ~ v1_xboole_0(A_135) ) ),
    inference(resolution,[status(thm)],[c_906,c_990])).

tff(c_1010,plain,(
    ! [B_136,A_137] :
      ( B_136 = A_137
      | ~ v1_xboole_0(B_136)
      | ~ v1_xboole_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_906,c_1000])).

tff(c_1020,plain,(
    ! [A_138] :
      ( A_138 = '#skF_5'
      | ~ v1_xboole_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_828,c_1010])).

tff(c_1023,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_952,c_1020])).

tff(c_1033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1023])).

tff(c_1034,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_939])).

tff(c_1035,plain,(
    ! [B_139,A_140] :
      ( B_139 = A_140
      | ~ r1_tarski(B_139,A_140)
      | ~ r1_tarski(A_140,B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1045,plain,(
    ! [B_141,A_142] :
      ( B_141 = A_142
      | ~ r1_tarski(B_141,A_142)
      | ~ v1_xboole_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_906,c_1035])).

tff(c_1055,plain,(
    ! [B_143,A_144] :
      ( B_143 = A_144
      | ~ v1_xboole_0(B_143)
      | ~ v1_xboole_0(A_144) ) ),
    inference(resolution,[status(thm)],[c_906,c_1045])).

tff(c_1065,plain,(
    ! [A_145] :
      ( k1_xboole_0 = A_145
      | ~ v1_xboole_0(A_145) ) ),
    inference(resolution,[status(thm)],[c_1034,c_1055])).

tff(c_1071,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_828,c_1065])).

tff(c_1080,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1071])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:37:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.44  
% 2.84/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.44  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 2.84/1.44  
% 2.84/1.44  %Foreground sorts:
% 2.84/1.44  
% 2.84/1.44  
% 2.84/1.44  %Background operators:
% 2.84/1.44  
% 2.84/1.44  
% 2.84/1.44  %Foreground operators:
% 2.84/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.84/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.84/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.44  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.84/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.84/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.84/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.44  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.84/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.84/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.84/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.84/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.84/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.84/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.84/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.84/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.84/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.84/1.44  
% 2.84/1.45  tff(f_96, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 2.84/1.45  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.84/1.45  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.84/1.45  tff(f_48, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.84/1.45  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.84/1.45  tff(f_60, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.84/1.45  tff(f_58, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.84/1.45  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.84/1.45  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.84/1.45  tff(f_54, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.84/1.45  tff(c_64, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.84/1.45  tff(c_60, plain, (m1_subset_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.84/1.45  tff(c_90, plain, (![B_43, A_44]: (v1_xboole_0(B_43) | ~m1_subset_1(B_43, A_44) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.84/1.45  tff(c_102, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_60, c_90])).
% 2.84/1.45  tff(c_103, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_102])).
% 2.84/1.45  tff(c_48, plain, (![B_28, A_27]: (r2_hidden(B_28, A_27) | ~m1_subset_1(B_28, A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.84/1.45  tff(c_58, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.84/1.45  tff(c_62, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.84/1.45  tff(c_618, plain, (![A_99, B_100]: (k4_xboole_0(A_99, B_100)=k3_subset_1(A_99, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.84/1.45  tff(c_632, plain, (k4_xboole_0('#skF_5', '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_618])).
% 2.84/1.45  tff(c_722, plain, (![D_103, A_104, B_105]: (r2_hidden(D_103, k4_xboole_0(A_104, B_105)) | r2_hidden(D_103, B_105) | ~r2_hidden(D_103, A_104))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.45  tff(c_780, plain, (![D_107]: (r2_hidden(D_107, k3_subset_1('#skF_5', '#skF_6')) | r2_hidden(D_107, '#skF_6') | ~r2_hidden(D_107, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_632, c_722])).
% 2.84/1.45  tff(c_56, plain, (~r2_hidden('#skF_7', k3_subset_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.84/1.45  tff(c_802, plain, (r2_hidden('#skF_7', '#skF_6') | ~r2_hidden('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_780, c_56])).
% 2.84/1.45  tff(c_817, plain, (~r2_hidden('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_802])).
% 2.84/1.45  tff(c_821, plain, (~m1_subset_1('#skF_7', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_48, c_817])).
% 2.84/1.45  tff(c_824, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_821])).
% 2.84/1.45  tff(c_826, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_824])).
% 2.84/1.45  tff(c_828, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_102])).
% 2.84/1.45  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.45  tff(c_40, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.84/1.45  tff(c_38, plain, (![A_20]: (k3_xboole_0(A_20, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.84/1.45  tff(c_841, plain, (![A_113, B_114]: (k5_xboole_0(A_113, k3_xboole_0(A_113, B_114))=k4_xboole_0(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.84/1.45  tff(c_850, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=k4_xboole_0(A_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_841])).
% 2.84/1.45  tff(c_853, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_850])).
% 2.84/1.45  tff(c_907, plain, (![D_120, B_121, A_122]: (~r2_hidden(D_120, B_121) | ~r2_hidden(D_120, k4_xboole_0(A_122, B_121)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.45  tff(c_927, plain, (![D_125, A_126]: (~r2_hidden(D_125, k1_xboole_0) | ~r2_hidden(D_125, A_126))), inference(superposition, [status(thm), theory('equality')], [c_853, c_907])).
% 2.84/1.45  tff(c_939, plain, (![A_126]: (~r2_hidden('#skF_1'(k1_xboole_0), A_126) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_927])).
% 2.84/1.45  tff(c_942, plain, (![A_127]: (~r2_hidden('#skF_1'(k1_xboole_0), A_127))), inference(splitLeft, [status(thm)], [c_939])).
% 2.84/1.45  tff(c_952, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_942])).
% 2.84/1.45  tff(c_892, plain, (![A_118, B_119]: (r2_hidden('#skF_2'(A_118, B_119), A_118) | r1_tarski(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.84/1.45  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.45  tff(c_906, plain, (![A_118, B_119]: (~v1_xboole_0(A_118) | r1_tarski(A_118, B_119))), inference(resolution, [status(thm)], [c_892, c_2])).
% 2.84/1.45  tff(c_990, plain, (![B_132, A_133]: (B_132=A_133 | ~r1_tarski(B_132, A_133) | ~r1_tarski(A_133, B_132))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.84/1.45  tff(c_1000, plain, (![B_134, A_135]: (B_134=A_135 | ~r1_tarski(B_134, A_135) | ~v1_xboole_0(A_135))), inference(resolution, [status(thm)], [c_906, c_990])).
% 2.84/1.45  tff(c_1010, plain, (![B_136, A_137]: (B_136=A_137 | ~v1_xboole_0(B_136) | ~v1_xboole_0(A_137))), inference(resolution, [status(thm)], [c_906, c_1000])).
% 2.84/1.45  tff(c_1020, plain, (![A_138]: (A_138='#skF_5' | ~v1_xboole_0(A_138))), inference(resolution, [status(thm)], [c_828, c_1010])).
% 2.84/1.45  tff(c_1023, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_952, c_1020])).
% 2.84/1.45  tff(c_1033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1023])).
% 2.84/1.45  tff(c_1034, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_939])).
% 2.84/1.45  tff(c_1035, plain, (![B_139, A_140]: (B_139=A_140 | ~r1_tarski(B_139, A_140) | ~r1_tarski(A_140, B_139))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.84/1.45  tff(c_1045, plain, (![B_141, A_142]: (B_141=A_142 | ~r1_tarski(B_141, A_142) | ~v1_xboole_0(A_142))), inference(resolution, [status(thm)], [c_906, c_1035])).
% 2.84/1.45  tff(c_1055, plain, (![B_143, A_144]: (B_143=A_144 | ~v1_xboole_0(B_143) | ~v1_xboole_0(A_144))), inference(resolution, [status(thm)], [c_906, c_1045])).
% 2.84/1.45  tff(c_1065, plain, (![A_145]: (k1_xboole_0=A_145 | ~v1_xboole_0(A_145))), inference(resolution, [status(thm)], [c_1034, c_1055])).
% 2.84/1.45  tff(c_1071, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_828, c_1065])).
% 2.84/1.45  tff(c_1080, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1071])).
% 2.84/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.45  
% 2.84/1.45  Inference rules
% 2.84/1.45  ----------------------
% 2.84/1.45  #Ref     : 0
% 2.84/1.45  #Sup     : 215
% 2.84/1.45  #Fact    : 0
% 2.84/1.45  #Define  : 0
% 2.84/1.45  #Split   : 11
% 2.84/1.45  #Chain   : 0
% 2.84/1.45  #Close   : 0
% 2.84/1.45  
% 2.84/1.45  Ordering : KBO
% 2.84/1.45  
% 2.84/1.45  Simplification rules
% 2.84/1.45  ----------------------
% 2.84/1.45  #Subsume      : 12
% 2.84/1.45  #Demod        : 52
% 2.84/1.45  #Tautology    : 83
% 2.84/1.45  #SimpNegUnit  : 15
% 2.84/1.45  #BackRed      : 0
% 2.84/1.45  
% 2.84/1.45  #Partial instantiations: 0
% 2.84/1.45  #Strategies tried      : 1
% 2.84/1.45  
% 2.84/1.45  Timing (in seconds)
% 2.84/1.45  ----------------------
% 2.84/1.46  Preprocessing        : 0.32
% 2.84/1.46  Parsing              : 0.16
% 2.84/1.46  CNF conversion       : 0.02
% 2.84/1.46  Main loop            : 0.37
% 2.84/1.46  Inferencing          : 0.14
% 2.84/1.46  Reduction            : 0.11
% 2.84/1.46  Demodulation         : 0.07
% 2.84/1.46  BG Simplification    : 0.02
% 2.84/1.46  Subsumption          : 0.07
% 2.84/1.46  Abstraction          : 0.02
% 2.84/1.46  MUC search           : 0.00
% 2.84/1.46  Cooper               : 0.00
% 2.84/1.46  Total                : 0.72
% 2.84/1.46  Index Insertion      : 0.00
% 2.84/1.46  Index Deletion       : 0.00
% 2.84/1.46  Index Matching       : 0.00
% 2.84/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
