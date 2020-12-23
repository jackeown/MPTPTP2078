%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:24 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.49s
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
    ! [D_87,A_88,B_89] :
      ( r2_hidden(D_87,A_88)
      | ~ r2_hidden(D_87,k4_xboole_0(A_88,B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_908,plain,(
    ! [A_160,B_161] :
      ( r2_hidden('#skF_7'(k4_xboole_0(A_160,B_161)),A_160)
      | k4_xboole_0(A_160,B_161) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_104,c_172])).

tff(c_166,plain,(
    ! [D_84,B_85,A_86] :
      ( ~ r2_hidden(D_84,B_85)
      | ~ r2_hidden(D_84,k4_xboole_0(A_86,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_171,plain,(
    ! [A_86,B_85] :
      ( ~ r2_hidden('#skF_7'(k4_xboole_0(A_86,B_85)),B_85)
      | k4_xboole_0(A_86,B_85) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_104,c_166])).

tff(c_943,plain,(
    ! [A_170] : k4_xboole_0(A_170,A_170) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_908,c_171])).

tff(c_46,plain,(
    ! [A_40,B_41] :
      ( ~ r2_hidden(A_40,B_41)
      | k4_xboole_0(k1_tarski(A_40),B_41) != k1_tarski(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_955,plain,(
    ! [A_40] :
      ( ~ r2_hidden(A_40,k1_tarski(A_40))
      | k1_tarski(A_40) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_943,c_46])).

tff(c_976,plain,(
    ! [A_40] : k1_tarski(A_40) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_955])).

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

tff(c_8011,plain,(
    ! [D_61658,C_61659,B_61660,A_61661] :
      ( r2_hidden(k1_funct_1(D_61658,C_61659),B_61660)
      | k1_xboole_0 = B_61660
      | ~ r2_hidden(C_61659,A_61661)
      | ~ m1_subset_1(D_61658,k1_zfmisc_1(k2_zfmisc_1(A_61661,B_61660)))
      | ~ v1_funct_2(D_61658,A_61661,B_61660)
      | ~ v1_funct_1(D_61658) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_8381,plain,(
    ! [D_63500,B_63501] :
      ( r2_hidden(k1_funct_1(D_63500,'#skF_10'),B_63501)
      | k1_xboole_0 = B_63501
      | ~ m1_subset_1(D_63500,k1_zfmisc_1(k2_zfmisc_1('#skF_8',B_63501)))
      | ~ v1_funct_2(D_63500,'#skF_8',B_63501)
      | ~ v1_funct_1(D_63500) ) ),
    inference(resolution,[status(thm)],[c_114,c_8011])).

tff(c_8396,plain,
    ( r2_hidden(k1_funct_1('#skF_11','#skF_10'),k1_tarski('#skF_9'))
    | k1_tarski('#skF_9') = k1_xboole_0
    | ~ v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9'))
    | ~ v1_funct_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_116,c_8381])).

tff(c_8399,plain,
    ( r2_hidden(k1_funct_1('#skF_11','#skF_10'),k1_tarski('#skF_9'))
    | k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_118,c_8396])).

tff(c_8400,plain,(
    r2_hidden(k1_funct_1('#skF_11','#skF_10'),k1_tarski('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_976,c_8399])).

tff(c_20,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8431,plain,(
    k1_funct_1('#skF_11','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_8400,c_20])).

tff(c_8518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_8431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.49/2.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.49/2.51  
% 7.49/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.49/2.51  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k4_mcart_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_1 > #skF_11 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_6 > #skF_5 > #skF_4
% 7.49/2.51  
% 7.49/2.51  %Foreground sorts:
% 7.49/2.51  
% 7.49/2.51  
% 7.49/2.51  %Background operators:
% 7.49/2.51  
% 7.49/2.51  
% 7.49/2.51  %Foreground operators:
% 7.49/2.51  tff('#skF_7', type, '#skF_7': $i > $i).
% 7.49/2.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.49/2.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.49/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.49/2.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.49/2.51  tff('#skF_11', type, '#skF_11': $i).
% 7.49/2.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.49/2.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.49/2.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.49/2.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.49/2.51  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.49/2.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.49/2.51  tff('#skF_10', type, '#skF_10': $i).
% 7.49/2.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.49/2.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.49/2.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.49/2.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.49/2.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.49/2.51  tff('#skF_9', type, '#skF_9': $i).
% 7.49/2.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.49/2.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.49/2.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.49/2.51  tff('#skF_8', type, '#skF_8': $i).
% 7.49/2.51  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.49/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.49/2.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.49/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.49/2.51  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.49/2.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.49/2.51  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 7.49/2.51  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.49/2.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.49/2.51  
% 7.49/2.52  tff(f_130, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 7.49/2.52  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 7.49/2.52  tff(f_107, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 7.49/2.52  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.49/2.52  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 7.49/2.52  tff(f_119, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 7.49/2.52  tff(c_112, plain, (k1_funct_1('#skF_11', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.49/2.52  tff(c_22, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.49/2.52  tff(c_104, plain, (![A_54]: (r2_hidden('#skF_7'(A_54), A_54) | k1_xboole_0=A_54)), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.49/2.52  tff(c_172, plain, (![D_87, A_88, B_89]: (r2_hidden(D_87, A_88) | ~r2_hidden(D_87, k4_xboole_0(A_88, B_89)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.49/2.52  tff(c_908, plain, (![A_160, B_161]: (r2_hidden('#skF_7'(k4_xboole_0(A_160, B_161)), A_160) | k4_xboole_0(A_160, B_161)=k1_xboole_0)), inference(resolution, [status(thm)], [c_104, c_172])).
% 7.49/2.52  tff(c_166, plain, (![D_84, B_85, A_86]: (~r2_hidden(D_84, B_85) | ~r2_hidden(D_84, k4_xboole_0(A_86, B_85)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.49/2.52  tff(c_171, plain, (![A_86, B_85]: (~r2_hidden('#skF_7'(k4_xboole_0(A_86, B_85)), B_85) | k4_xboole_0(A_86, B_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_104, c_166])).
% 7.49/2.52  tff(c_943, plain, (![A_170]: (k4_xboole_0(A_170, A_170)=k1_xboole_0)), inference(resolution, [status(thm)], [c_908, c_171])).
% 7.49/2.52  tff(c_46, plain, (![A_40, B_41]: (~r2_hidden(A_40, B_41) | k4_xboole_0(k1_tarski(A_40), B_41)!=k1_tarski(A_40))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.49/2.52  tff(c_955, plain, (![A_40]: (~r2_hidden(A_40, k1_tarski(A_40)) | k1_tarski(A_40)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_943, c_46])).
% 7.49/2.52  tff(c_976, plain, (![A_40]: (k1_tarski(A_40)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_955])).
% 7.49/2.52  tff(c_120, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.49/2.52  tff(c_118, plain, (v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.49/2.52  tff(c_116, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k1_tarski('#skF_9'))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.49/2.52  tff(c_114, plain, (r2_hidden('#skF_10', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.49/2.52  tff(c_8011, plain, (![D_61658, C_61659, B_61660, A_61661]: (r2_hidden(k1_funct_1(D_61658, C_61659), B_61660) | k1_xboole_0=B_61660 | ~r2_hidden(C_61659, A_61661) | ~m1_subset_1(D_61658, k1_zfmisc_1(k2_zfmisc_1(A_61661, B_61660))) | ~v1_funct_2(D_61658, A_61661, B_61660) | ~v1_funct_1(D_61658))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.49/2.52  tff(c_8381, plain, (![D_63500, B_63501]: (r2_hidden(k1_funct_1(D_63500, '#skF_10'), B_63501) | k1_xboole_0=B_63501 | ~m1_subset_1(D_63500, k1_zfmisc_1(k2_zfmisc_1('#skF_8', B_63501))) | ~v1_funct_2(D_63500, '#skF_8', B_63501) | ~v1_funct_1(D_63500))), inference(resolution, [status(thm)], [c_114, c_8011])).
% 7.49/2.52  tff(c_8396, plain, (r2_hidden(k1_funct_1('#skF_11', '#skF_10'), k1_tarski('#skF_9')) | k1_tarski('#skF_9')=k1_xboole_0 | ~v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9')) | ~v1_funct_1('#skF_11')), inference(resolution, [status(thm)], [c_116, c_8381])).
% 7.49/2.52  tff(c_8399, plain, (r2_hidden(k1_funct_1('#skF_11', '#skF_10'), k1_tarski('#skF_9')) | k1_tarski('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_120, c_118, c_8396])).
% 7.49/2.52  tff(c_8400, plain, (r2_hidden(k1_funct_1('#skF_11', '#skF_10'), k1_tarski('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_976, c_8399])).
% 7.49/2.52  tff(c_20, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.49/2.52  tff(c_8431, plain, (k1_funct_1('#skF_11', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_8400, c_20])).
% 7.49/2.52  tff(c_8518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_8431])).
% 7.49/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.49/2.52  
% 7.49/2.52  Inference rules
% 7.49/2.52  ----------------------
% 7.49/2.52  #Ref     : 0
% 7.49/2.52  #Sup     : 1292
% 7.49/2.52  #Fact    : 0
% 7.49/2.52  #Define  : 0
% 7.49/2.52  #Split   : 10
% 7.49/2.52  #Chain   : 0
% 7.49/2.52  #Close   : 0
% 7.49/2.52  
% 7.49/2.52  Ordering : KBO
% 7.49/2.52  
% 7.49/2.52  Simplification rules
% 7.49/2.52  ----------------------
% 7.49/2.52  #Subsume      : 164
% 7.49/2.52  #Demod        : 248
% 7.49/2.52  #Tautology    : 304
% 7.49/2.52  #SimpNegUnit  : 118
% 7.49/2.52  #BackRed      : 4
% 7.49/2.52  
% 7.49/2.52  #Partial instantiations: 13695
% 7.49/2.52  #Strategies tried      : 1
% 7.49/2.52  
% 7.49/2.52  Timing (in seconds)
% 7.49/2.52  ----------------------
% 7.49/2.53  Preprocessing        : 0.36
% 7.49/2.53  Parsing              : 0.17
% 7.49/2.53  CNF conversion       : 0.03
% 7.49/2.53  Main loop            : 1.37
% 7.49/2.53  Inferencing          : 0.68
% 7.49/2.53  Reduction            : 0.31
% 7.49/2.53  Demodulation         : 0.22
% 7.49/2.53  BG Simplification    : 0.06
% 7.49/2.53  Subsumption          : 0.24
% 7.49/2.53  Abstraction          : 0.07
% 7.49/2.53  MUC search           : 0.00
% 7.49/2.53  Cooper               : 0.00
% 7.49/2.53  Total                : 1.75
% 7.49/2.53  Index Insertion      : 0.00
% 7.49/2.53  Index Deletion       : 0.00
% 7.49/2.53  Index Matching       : 0.00
% 7.49/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
