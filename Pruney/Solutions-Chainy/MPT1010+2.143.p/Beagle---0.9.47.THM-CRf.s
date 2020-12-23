%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:24 EST 2020

% Result     : Theorem 6.77s
% Output     : CNFRefutation 6.77s
% Verified   : 
% Statistics : Number of formulae       :   61 (  69 expanded)
%              Number of leaves         :   38 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 103 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k4_mcart_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_1 > #skF_11 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_6 > #skF_5 > #skF_4

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

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
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

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
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

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
    ! [D_87,A_88,B_89] :
      ( r2_hidden(D_87,A_88)
      | ~ r2_hidden(D_87,k4_xboole_0(A_88,B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_177,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_7'(k4_xboole_0(A_88,B_89)),A_88)
      | k4_xboole_0(A_88,B_89) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_104,c_172])).

tff(c_166,plain,(
    ! [D_84,B_85,A_86] :
      ( ~ r2_hidden(D_84,B_85)
      | ~ r2_hidden(D_84,k4_xboole_0(A_86,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_238,plain,(
    ! [A_102,B_103] :
      ( ~ r2_hidden('#skF_7'(k4_xboole_0(A_102,B_103)),B_103)
      | k4_xboole_0(A_102,B_103) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_104,c_166])).

tff(c_248,plain,(
    ! [A_112] : k4_xboole_0(A_112,A_112) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_177,c_238])).

tff(c_46,plain,(
    ! [B_41,A_40] :
      ( ~ r2_hidden(B_41,A_40)
      | k4_xboole_0(A_40,k1_tarski(B_41)) != A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_264,plain,(
    ! [B_41] :
      ( ~ r2_hidden(B_41,k1_tarski(B_41))
      | k1_tarski(B_41) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_46])).

tff(c_282,plain,(
    ! [B_41] : k1_tarski(B_41) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_264])).

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

tff(c_8711,plain,(
    ! [D_47713,C_47714,B_47715,A_47716] :
      ( r2_hidden(k1_funct_1(D_47713,C_47714),B_47715)
      | k1_xboole_0 = B_47715
      | ~ r2_hidden(C_47714,A_47716)
      | ~ m1_subset_1(D_47713,k1_zfmisc_1(k2_zfmisc_1(A_47716,B_47715)))
      | ~ v1_funct_2(D_47713,A_47716,B_47715)
      | ~ v1_funct_1(D_47713) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_8907,plain,(
    ! [D_49556,B_49557] :
      ( r2_hidden(k1_funct_1(D_49556,'#skF_10'),B_49557)
      | k1_xboole_0 = B_49557
      | ~ m1_subset_1(D_49556,k1_zfmisc_1(k2_zfmisc_1('#skF_8',B_49557)))
      | ~ v1_funct_2(D_49556,'#skF_8',B_49557)
      | ~ v1_funct_1(D_49556) ) ),
    inference(resolution,[status(thm)],[c_114,c_8711])).

tff(c_8922,plain,
    ( r2_hidden(k1_funct_1('#skF_11','#skF_10'),k1_tarski('#skF_9'))
    | k1_tarski('#skF_9') = k1_xboole_0
    | ~ v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9'))
    | ~ v1_funct_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_116,c_8907])).

tff(c_8925,plain,
    ( r2_hidden(k1_funct_1('#skF_11','#skF_10'),k1_tarski('#skF_9'))
    | k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_118,c_8922])).

tff(c_8926,plain,(
    r2_hidden(k1_funct_1('#skF_11','#skF_10'),k1_tarski('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_8925])).

tff(c_20,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8945,plain,(
    k1_funct_1('#skF_11','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_8926,c_20])).

tff(c_9028,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_8945])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 14:00:01 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.77/2.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.77/2.32  
% 6.77/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.77/2.32  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k4_mcart_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_1 > #skF_11 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_6 > #skF_5 > #skF_4
% 6.77/2.32  
% 6.77/2.32  %Foreground sorts:
% 6.77/2.32  
% 6.77/2.32  
% 6.77/2.32  %Background operators:
% 6.77/2.32  
% 6.77/2.32  
% 6.77/2.32  %Foreground operators:
% 6.77/2.32  tff('#skF_7', type, '#skF_7': $i > $i).
% 6.77/2.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.77/2.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.77/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.77/2.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.77/2.32  tff('#skF_11', type, '#skF_11': $i).
% 6.77/2.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.77/2.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.77/2.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.77/2.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.77/2.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.77/2.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.77/2.32  tff('#skF_10', type, '#skF_10': $i).
% 6.77/2.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.77/2.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.77/2.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.77/2.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.77/2.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.77/2.32  tff('#skF_9', type, '#skF_9': $i).
% 6.77/2.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.77/2.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.77/2.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.77/2.32  tff('#skF_8', type, '#skF_8': $i).
% 6.77/2.32  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.77/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.77/2.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.77/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.77/2.32  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.77/2.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.77/2.32  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 6.77/2.32  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.77/2.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.77/2.32  
% 6.77/2.33  tff(f_130, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 6.77/2.33  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 6.77/2.33  tff(f_107, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 6.77/2.33  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.77/2.33  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 6.77/2.33  tff(f_119, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 6.77/2.33  tff(c_112, plain, (k1_funct_1('#skF_11', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.77/2.33  tff(c_22, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.77/2.33  tff(c_104, plain, (![A_54]: (r2_hidden('#skF_7'(A_54), A_54) | k1_xboole_0=A_54)), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.77/2.33  tff(c_172, plain, (![D_87, A_88, B_89]: (r2_hidden(D_87, A_88) | ~r2_hidden(D_87, k4_xboole_0(A_88, B_89)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.77/2.33  tff(c_177, plain, (![A_88, B_89]: (r2_hidden('#skF_7'(k4_xboole_0(A_88, B_89)), A_88) | k4_xboole_0(A_88, B_89)=k1_xboole_0)), inference(resolution, [status(thm)], [c_104, c_172])).
% 6.77/2.33  tff(c_166, plain, (![D_84, B_85, A_86]: (~r2_hidden(D_84, B_85) | ~r2_hidden(D_84, k4_xboole_0(A_86, B_85)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.77/2.33  tff(c_238, plain, (![A_102, B_103]: (~r2_hidden('#skF_7'(k4_xboole_0(A_102, B_103)), B_103) | k4_xboole_0(A_102, B_103)=k1_xboole_0)), inference(resolution, [status(thm)], [c_104, c_166])).
% 6.77/2.33  tff(c_248, plain, (![A_112]: (k4_xboole_0(A_112, A_112)=k1_xboole_0)), inference(resolution, [status(thm)], [c_177, c_238])).
% 6.77/2.33  tff(c_46, plain, (![B_41, A_40]: (~r2_hidden(B_41, A_40) | k4_xboole_0(A_40, k1_tarski(B_41))!=A_40)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.77/2.33  tff(c_264, plain, (![B_41]: (~r2_hidden(B_41, k1_tarski(B_41)) | k1_tarski(B_41)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_248, c_46])).
% 6.77/2.33  tff(c_282, plain, (![B_41]: (k1_tarski(B_41)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_264])).
% 6.77/2.33  tff(c_120, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.77/2.33  tff(c_118, plain, (v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.77/2.33  tff(c_116, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k1_tarski('#skF_9'))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.77/2.33  tff(c_114, plain, (r2_hidden('#skF_10', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.77/2.33  tff(c_8711, plain, (![D_47713, C_47714, B_47715, A_47716]: (r2_hidden(k1_funct_1(D_47713, C_47714), B_47715) | k1_xboole_0=B_47715 | ~r2_hidden(C_47714, A_47716) | ~m1_subset_1(D_47713, k1_zfmisc_1(k2_zfmisc_1(A_47716, B_47715))) | ~v1_funct_2(D_47713, A_47716, B_47715) | ~v1_funct_1(D_47713))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.77/2.33  tff(c_8907, plain, (![D_49556, B_49557]: (r2_hidden(k1_funct_1(D_49556, '#skF_10'), B_49557) | k1_xboole_0=B_49557 | ~m1_subset_1(D_49556, k1_zfmisc_1(k2_zfmisc_1('#skF_8', B_49557))) | ~v1_funct_2(D_49556, '#skF_8', B_49557) | ~v1_funct_1(D_49556))), inference(resolution, [status(thm)], [c_114, c_8711])).
% 6.77/2.33  tff(c_8922, plain, (r2_hidden(k1_funct_1('#skF_11', '#skF_10'), k1_tarski('#skF_9')) | k1_tarski('#skF_9')=k1_xboole_0 | ~v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9')) | ~v1_funct_1('#skF_11')), inference(resolution, [status(thm)], [c_116, c_8907])).
% 6.77/2.33  tff(c_8925, plain, (r2_hidden(k1_funct_1('#skF_11', '#skF_10'), k1_tarski('#skF_9')) | k1_tarski('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_120, c_118, c_8922])).
% 6.77/2.33  tff(c_8926, plain, (r2_hidden(k1_funct_1('#skF_11', '#skF_10'), k1_tarski('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_282, c_8925])).
% 6.77/2.33  tff(c_20, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.77/2.33  tff(c_8945, plain, (k1_funct_1('#skF_11', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_8926, c_20])).
% 6.77/2.33  tff(c_9028, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_8945])).
% 6.77/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.77/2.33  
% 6.77/2.33  Inference rules
% 6.77/2.33  ----------------------
% 6.77/2.33  #Ref     : 0
% 6.77/2.33  #Sup     : 1094
% 6.77/2.33  #Fact    : 4
% 6.77/2.33  #Define  : 0
% 6.77/2.33  #Split   : 8
% 6.77/2.33  #Chain   : 0
% 6.77/2.33  #Close   : 0
% 6.77/2.33  
% 6.77/2.33  Ordering : KBO
% 6.77/2.33  
% 6.77/2.33  Simplification rules
% 6.77/2.33  ----------------------
% 6.77/2.33  #Subsume      : 196
% 6.77/2.33  #Demod        : 264
% 6.77/2.33  #Tautology    : 258
% 6.77/2.33  #SimpNegUnit  : 76
% 6.77/2.33  #BackRed      : 1
% 6.77/2.33  
% 6.77/2.33  #Partial instantiations: 10743
% 6.77/2.33  #Strategies tried      : 1
% 6.77/2.33  
% 6.77/2.33  Timing (in seconds)
% 6.77/2.33  ----------------------
% 6.77/2.33  Preprocessing        : 0.37
% 6.77/2.33  Parsing              : 0.17
% 6.77/2.33  CNF conversion       : 0.03
% 6.77/2.33  Main loop            : 1.22
% 6.77/2.33  Inferencing          : 0.63
% 6.77/2.33  Reduction            : 0.26
% 6.77/2.33  Demodulation         : 0.18
% 6.77/2.33  BG Simplification    : 0.05
% 6.77/2.33  Subsumption          : 0.22
% 6.77/2.33  Abstraction          : 0.06
% 6.77/2.33  MUC search           : 0.00
% 6.77/2.33  Cooper               : 0.00
% 6.77/2.33  Total                : 1.61
% 6.77/2.33  Index Insertion      : 0.00
% 6.77/2.33  Index Deletion       : 0.00
% 6.77/2.33  Index Matching       : 0.00
% 6.77/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
