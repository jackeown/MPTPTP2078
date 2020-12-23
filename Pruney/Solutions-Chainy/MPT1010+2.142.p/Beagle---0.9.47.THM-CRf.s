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
% DateTime   : Thu Dec  3 10:15:24 EST 2020

% Result     : Theorem 6.90s
% Output     : CNFRefutation 6.90s
% Verified   : 
% Statistics : Number of formulae       :   61 (  69 expanded)
%              Number of leaves         :   38 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 103 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_1 > #skF_11 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_6 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_107,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_119,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_112,plain,(
    k1_funct_1('#skF_11','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_22,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_104,plain,(
    ! [A_54] :
      ( r2_hidden('#skF_7'(A_54),A_54)
      | k1_xboole_0 = A_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_172,plain,(
    ! [D_79,A_80,B_81] :
      ( r2_hidden(D_79,A_80)
      | ~ r2_hidden(D_79,k4_xboole_0(A_80,B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2232,plain,(
    ! [A_4412,B_4413] :
      ( r2_hidden('#skF_7'(k4_xboole_0(A_4412,B_4413)),A_4412)
      | k4_xboole_0(A_4412,B_4413) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_104,c_172])).

tff(c_166,plain,(
    ! [D_76,B_77,A_78] :
      ( ~ r2_hidden(D_76,B_77)
      | ~ r2_hidden(D_76,k4_xboole_0(A_78,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_171,plain,(
    ! [A_78,B_77] :
      ( ~ r2_hidden('#skF_7'(k4_xboole_0(A_78,B_77)),B_77)
      | k4_xboole_0(A_78,B_77) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_104,c_166])).

tff(c_2269,plain,(
    ! [A_4414] : k4_xboole_0(A_4414,A_4414) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2232,c_171])).

tff(c_46,plain,(
    ! [A_40,B_41] :
      ( ~ r2_hidden(A_40,B_41)
      | k4_xboole_0(k1_tarski(A_40),B_41) != k1_tarski(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2284,plain,(
    ! [A_40] :
      ( ~ r2_hidden(A_40,k1_tarski(A_40))
      | k1_tarski(A_40) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2269,c_46])).

tff(c_2305,plain,(
    ! [A_40] : k1_tarski(A_40) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2284])).

tff(c_120,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_118,plain,(
    v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_116,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k1_tarski('#skF_9')))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_114,plain,(
    r2_hidden('#skF_10','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_7831,plain,(
    ! [D_49826,C_49827,B_49828,A_49829] :
      ( r2_hidden(k1_funct_1(D_49826,C_49827),B_49828)
      | k1_xboole_0 = B_49828
      | ~ r2_hidden(C_49827,A_49829)
      | ~ m1_subset_1(D_49826,k1_zfmisc_1(k2_zfmisc_1(A_49829,B_49828)))
      | ~ v1_funct_2(D_49826,A_49829,B_49828)
      | ~ v1_funct_1(D_49826) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_8007,plain,(
    ! [D_51621,B_51622] :
      ( r2_hidden(k1_funct_1(D_51621,'#skF_10'),B_51622)
      | k1_xboole_0 = B_51622
      | ~ m1_subset_1(D_51621,k1_zfmisc_1(k2_zfmisc_1('#skF_8',B_51622)))
      | ~ v1_funct_2(D_51621,'#skF_8',B_51622)
      | ~ v1_funct_1(D_51621) ) ),
    inference(resolution,[status(thm)],[c_114,c_7831])).

tff(c_8022,plain,
    ( r2_hidden(k1_funct_1('#skF_11','#skF_10'),k1_tarski('#skF_9'))
    | k1_tarski('#skF_9') = k1_xboole_0
    | ~ v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9'))
    | ~ v1_funct_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_116,c_8007])).

tff(c_8025,plain,
    ( r2_hidden(k1_funct_1('#skF_11','#skF_10'),k1_tarski('#skF_9'))
    | k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_118,c_8022])).

tff(c_8026,plain,(
    r2_hidden(k1_funct_1('#skF_11','#skF_10'),k1_tarski('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_2305,c_8025])).

tff(c_20,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8045,plain,(
    k1_funct_1('#skF_11','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_8026,c_20])).

tff(c_8126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_8045])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n004.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:14:38 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.90/2.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.90/2.38  
% 6.90/2.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.90/2.38  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_1 > #skF_11 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_6 > #skF_5 > #skF_4
% 6.90/2.38  
% 6.90/2.38  %Foreground sorts:
% 6.90/2.38  
% 6.90/2.38  
% 6.90/2.38  %Background operators:
% 6.90/2.38  
% 6.90/2.38  
% 6.90/2.38  %Foreground operators:
% 6.90/2.38  tff('#skF_7', type, '#skF_7': $i > $i).
% 6.90/2.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.90/2.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.90/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.90/2.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.90/2.38  tff('#skF_11', type, '#skF_11': $i).
% 6.90/2.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.90/2.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.90/2.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.90/2.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.90/2.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.90/2.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.90/2.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.90/2.38  tff('#skF_10', type, '#skF_10': $i).
% 6.90/2.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.90/2.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.90/2.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.90/2.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.90/2.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.90/2.38  tff('#skF_9', type, '#skF_9': $i).
% 6.90/2.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.90/2.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.90/2.38  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.90/2.38  tff('#skF_8', type, '#skF_8': $i).
% 6.90/2.38  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.90/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.90/2.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.90/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.90/2.38  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.90/2.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.90/2.38  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.90/2.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.90/2.38  
% 6.90/2.39  tff(f_130, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 6.90/2.39  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 6.90/2.39  tff(f_107, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 6.90/2.39  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.90/2.39  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 6.90/2.39  tff(f_119, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 6.90/2.39  tff(c_112, plain, (k1_funct_1('#skF_11', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.90/2.39  tff(c_22, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.90/2.39  tff(c_104, plain, (![A_54]: (r2_hidden('#skF_7'(A_54), A_54) | k1_xboole_0=A_54)), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.90/2.39  tff(c_172, plain, (![D_79, A_80, B_81]: (r2_hidden(D_79, A_80) | ~r2_hidden(D_79, k4_xboole_0(A_80, B_81)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.90/2.39  tff(c_2232, plain, (![A_4412, B_4413]: (r2_hidden('#skF_7'(k4_xboole_0(A_4412, B_4413)), A_4412) | k4_xboole_0(A_4412, B_4413)=k1_xboole_0)), inference(resolution, [status(thm)], [c_104, c_172])).
% 6.90/2.39  tff(c_166, plain, (![D_76, B_77, A_78]: (~r2_hidden(D_76, B_77) | ~r2_hidden(D_76, k4_xboole_0(A_78, B_77)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.90/2.39  tff(c_171, plain, (![A_78, B_77]: (~r2_hidden('#skF_7'(k4_xboole_0(A_78, B_77)), B_77) | k4_xboole_0(A_78, B_77)=k1_xboole_0)), inference(resolution, [status(thm)], [c_104, c_166])).
% 6.90/2.39  tff(c_2269, plain, (![A_4414]: (k4_xboole_0(A_4414, A_4414)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2232, c_171])).
% 6.90/2.39  tff(c_46, plain, (![A_40, B_41]: (~r2_hidden(A_40, B_41) | k4_xboole_0(k1_tarski(A_40), B_41)!=k1_tarski(A_40))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.90/2.39  tff(c_2284, plain, (![A_40]: (~r2_hidden(A_40, k1_tarski(A_40)) | k1_tarski(A_40)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2269, c_46])).
% 6.90/2.39  tff(c_2305, plain, (![A_40]: (k1_tarski(A_40)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2284])).
% 6.90/2.39  tff(c_120, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.90/2.39  tff(c_118, plain, (v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.90/2.39  tff(c_116, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k1_tarski('#skF_9'))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.90/2.39  tff(c_114, plain, (r2_hidden('#skF_10', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.90/2.39  tff(c_7831, plain, (![D_49826, C_49827, B_49828, A_49829]: (r2_hidden(k1_funct_1(D_49826, C_49827), B_49828) | k1_xboole_0=B_49828 | ~r2_hidden(C_49827, A_49829) | ~m1_subset_1(D_49826, k1_zfmisc_1(k2_zfmisc_1(A_49829, B_49828))) | ~v1_funct_2(D_49826, A_49829, B_49828) | ~v1_funct_1(D_49826))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.90/2.39  tff(c_8007, plain, (![D_51621, B_51622]: (r2_hidden(k1_funct_1(D_51621, '#skF_10'), B_51622) | k1_xboole_0=B_51622 | ~m1_subset_1(D_51621, k1_zfmisc_1(k2_zfmisc_1('#skF_8', B_51622))) | ~v1_funct_2(D_51621, '#skF_8', B_51622) | ~v1_funct_1(D_51621))), inference(resolution, [status(thm)], [c_114, c_7831])).
% 6.90/2.39  tff(c_8022, plain, (r2_hidden(k1_funct_1('#skF_11', '#skF_10'), k1_tarski('#skF_9')) | k1_tarski('#skF_9')=k1_xboole_0 | ~v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9')) | ~v1_funct_1('#skF_11')), inference(resolution, [status(thm)], [c_116, c_8007])).
% 6.90/2.39  tff(c_8025, plain, (r2_hidden(k1_funct_1('#skF_11', '#skF_10'), k1_tarski('#skF_9')) | k1_tarski('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_120, c_118, c_8022])).
% 6.90/2.39  tff(c_8026, plain, (r2_hidden(k1_funct_1('#skF_11', '#skF_10'), k1_tarski('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_2305, c_8025])).
% 6.90/2.39  tff(c_20, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.90/2.39  tff(c_8045, plain, (k1_funct_1('#skF_11', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_8026, c_20])).
% 6.90/2.39  tff(c_8126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_8045])).
% 6.90/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.90/2.39  
% 6.90/2.39  Inference rules
% 6.90/2.39  ----------------------
% 6.90/2.39  #Ref     : 0
% 6.90/2.39  #Sup     : 1058
% 6.90/2.39  #Fact    : 0
% 6.90/2.39  #Define  : 0
% 6.90/2.39  #Split   : 13
% 6.90/2.39  #Chain   : 0
% 6.90/2.39  #Close   : 0
% 6.90/2.39  
% 6.90/2.39  Ordering : KBO
% 6.90/2.39  
% 6.90/2.39  Simplification rules
% 6.90/2.39  ----------------------
% 6.90/2.39  #Subsume      : 153
% 6.90/2.39  #Demod        : 181
% 6.90/2.39  #Tautology    : 265
% 6.90/2.39  #SimpNegUnit  : 107
% 6.90/2.39  #BackRed      : 9
% 6.90/2.39  
% 6.90/2.39  #Partial instantiations: 11959
% 6.90/2.39  #Strategies tried      : 1
% 6.90/2.39  
% 6.90/2.39  Timing (in seconds)
% 6.90/2.39  ----------------------
% 6.90/2.39  Preprocessing        : 0.37
% 6.90/2.39  Parsing              : 0.18
% 6.90/2.39  CNF conversion       : 0.03
% 6.90/2.39  Main loop            : 1.28
% 6.90/2.39  Inferencing          : 0.68
% 6.90/2.39  Reduction            : 0.26
% 6.90/2.39  Demodulation         : 0.17
% 6.90/2.39  BG Simplification    : 0.06
% 6.90/2.39  Subsumption          : 0.22
% 6.90/2.39  Abstraction          : 0.06
% 6.90/2.39  MUC search           : 0.00
% 6.90/2.39  Cooper               : 0.00
% 6.90/2.39  Total                : 1.67
% 6.90/2.39  Index Insertion      : 0.00
% 6.90/2.39  Index Deletion       : 0.00
% 6.90/2.39  Index Matching       : 0.00
% 6.90/2.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
