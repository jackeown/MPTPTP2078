%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:24 EST 2020

% Result     : Theorem 7.29s
% Output     : CNFRefutation 7.29s
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
    ! [D_79,A_80,B_81] :
      ( r2_hidden(D_79,A_80)
      | ~ r2_hidden(D_79,k4_xboole_0(A_80,B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_177,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_7'(k4_xboole_0(A_80,B_81)),A_80)
      | k4_xboole_0(A_80,B_81) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_104,c_172])).

tff(c_166,plain,(
    ! [D_76,B_77,A_78] :
      ( ~ r2_hidden(D_76,B_77)
      | ~ r2_hidden(D_76,k4_xboole_0(A_78,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_298,plain,(
    ! [A_126,B_127] :
      ( ~ r2_hidden('#skF_7'(k4_xboole_0(A_126,B_127)),B_127)
      | k4_xboole_0(A_126,B_127) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_104,c_166])).

tff(c_307,plain,(
    ! [A_128] : k4_xboole_0(A_128,A_128) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_177,c_298])).

tff(c_46,plain,(
    ! [B_41,A_40] :
      ( ~ r2_hidden(B_41,A_40)
      | k4_xboole_0(A_40,k1_tarski(B_41)) != A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_323,plain,(
    ! [B_41] :
      ( ~ r2_hidden(B_41,k1_tarski(B_41))
      | k1_tarski(B_41) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_46])).

tff(c_341,plain,(
    ! [B_41] : k1_tarski(B_41) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_323])).

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

tff(c_9166,plain,(
    ! [D_51614,C_51615,B_51616,A_51617] :
      ( r2_hidden(k1_funct_1(D_51614,C_51615),B_51616)
      | k1_xboole_0 = B_51616
      | ~ r2_hidden(C_51615,A_51617)
      | ~ m1_subset_1(D_51614,k1_zfmisc_1(k2_zfmisc_1(A_51617,B_51616)))
      | ~ v1_funct_2(D_51614,A_51617,B_51616)
      | ~ v1_funct_1(D_51614) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_9381,plain,(
    ! [D_53406,B_53407] :
      ( r2_hidden(k1_funct_1(D_53406,'#skF_10'),B_53407)
      | k1_xboole_0 = B_53407
      | ~ m1_subset_1(D_53406,k1_zfmisc_1(k2_zfmisc_1('#skF_8',B_53407)))
      | ~ v1_funct_2(D_53406,'#skF_8',B_53407)
      | ~ v1_funct_1(D_53406) ) ),
    inference(resolution,[status(thm)],[c_114,c_9166])).

tff(c_9396,plain,
    ( r2_hidden(k1_funct_1('#skF_11','#skF_10'),k1_tarski('#skF_9'))
    | k1_tarski('#skF_9') = k1_xboole_0
    | ~ v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9'))
    | ~ v1_funct_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_116,c_9381])).

tff(c_9399,plain,
    ( r2_hidden(k1_funct_1('#skF_11','#skF_10'),k1_tarski('#skF_9'))
    | k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_118,c_9396])).

tff(c_9400,plain,(
    r2_hidden(k1_funct_1('#skF_11','#skF_10'),k1_tarski('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_341,c_9399])).

tff(c_20,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_9419,plain,(
    k1_funct_1('#skF_11','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_9400,c_20])).

tff(c_9502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_9419])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:46:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.29/2.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.29/2.55  
% 7.29/2.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.29/2.55  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_1 > #skF_11 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_6 > #skF_5 > #skF_4
% 7.29/2.55  
% 7.29/2.55  %Foreground sorts:
% 7.29/2.55  
% 7.29/2.55  
% 7.29/2.55  %Background operators:
% 7.29/2.55  
% 7.29/2.55  
% 7.29/2.55  %Foreground operators:
% 7.29/2.55  tff('#skF_7', type, '#skF_7': $i > $i).
% 7.29/2.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.29/2.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.29/2.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.29/2.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.29/2.55  tff('#skF_11', type, '#skF_11': $i).
% 7.29/2.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.29/2.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.29/2.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.29/2.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.29/2.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.29/2.55  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.29/2.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.29/2.55  tff('#skF_10', type, '#skF_10': $i).
% 7.29/2.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.29/2.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.29/2.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.29/2.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.29/2.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.29/2.55  tff('#skF_9', type, '#skF_9': $i).
% 7.29/2.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.29/2.55  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.29/2.55  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.29/2.55  tff('#skF_8', type, '#skF_8': $i).
% 7.29/2.55  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.29/2.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.29/2.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.29/2.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.29/2.55  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.29/2.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.29/2.55  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.29/2.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.29/2.55  
% 7.29/2.56  tff(f_130, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 7.29/2.56  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 7.29/2.56  tff(f_107, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 7.29/2.56  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.29/2.56  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 7.29/2.56  tff(f_119, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 7.29/2.56  tff(c_112, plain, (k1_funct_1('#skF_11', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.29/2.56  tff(c_22, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.29/2.56  tff(c_104, plain, (![A_54]: (r2_hidden('#skF_7'(A_54), A_54) | k1_xboole_0=A_54)), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.29/2.56  tff(c_172, plain, (![D_79, A_80, B_81]: (r2_hidden(D_79, A_80) | ~r2_hidden(D_79, k4_xboole_0(A_80, B_81)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.29/2.56  tff(c_177, plain, (![A_80, B_81]: (r2_hidden('#skF_7'(k4_xboole_0(A_80, B_81)), A_80) | k4_xboole_0(A_80, B_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_104, c_172])).
% 7.29/2.56  tff(c_166, plain, (![D_76, B_77, A_78]: (~r2_hidden(D_76, B_77) | ~r2_hidden(D_76, k4_xboole_0(A_78, B_77)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.29/2.56  tff(c_298, plain, (![A_126, B_127]: (~r2_hidden('#skF_7'(k4_xboole_0(A_126, B_127)), B_127) | k4_xboole_0(A_126, B_127)=k1_xboole_0)), inference(resolution, [status(thm)], [c_104, c_166])).
% 7.29/2.56  tff(c_307, plain, (![A_128]: (k4_xboole_0(A_128, A_128)=k1_xboole_0)), inference(resolution, [status(thm)], [c_177, c_298])).
% 7.29/2.56  tff(c_46, plain, (![B_41, A_40]: (~r2_hidden(B_41, A_40) | k4_xboole_0(A_40, k1_tarski(B_41))!=A_40)), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.29/2.56  tff(c_323, plain, (![B_41]: (~r2_hidden(B_41, k1_tarski(B_41)) | k1_tarski(B_41)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_307, c_46])).
% 7.29/2.56  tff(c_341, plain, (![B_41]: (k1_tarski(B_41)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_323])).
% 7.29/2.56  tff(c_120, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.29/2.56  tff(c_118, plain, (v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.29/2.56  tff(c_116, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k1_tarski('#skF_9'))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.29/2.56  tff(c_114, plain, (r2_hidden('#skF_10', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.29/2.56  tff(c_9166, plain, (![D_51614, C_51615, B_51616, A_51617]: (r2_hidden(k1_funct_1(D_51614, C_51615), B_51616) | k1_xboole_0=B_51616 | ~r2_hidden(C_51615, A_51617) | ~m1_subset_1(D_51614, k1_zfmisc_1(k2_zfmisc_1(A_51617, B_51616))) | ~v1_funct_2(D_51614, A_51617, B_51616) | ~v1_funct_1(D_51614))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.29/2.56  tff(c_9381, plain, (![D_53406, B_53407]: (r2_hidden(k1_funct_1(D_53406, '#skF_10'), B_53407) | k1_xboole_0=B_53407 | ~m1_subset_1(D_53406, k1_zfmisc_1(k2_zfmisc_1('#skF_8', B_53407))) | ~v1_funct_2(D_53406, '#skF_8', B_53407) | ~v1_funct_1(D_53406))), inference(resolution, [status(thm)], [c_114, c_9166])).
% 7.29/2.56  tff(c_9396, plain, (r2_hidden(k1_funct_1('#skF_11', '#skF_10'), k1_tarski('#skF_9')) | k1_tarski('#skF_9')=k1_xboole_0 | ~v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9')) | ~v1_funct_1('#skF_11')), inference(resolution, [status(thm)], [c_116, c_9381])).
% 7.29/2.56  tff(c_9399, plain, (r2_hidden(k1_funct_1('#skF_11', '#skF_10'), k1_tarski('#skF_9')) | k1_tarski('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_120, c_118, c_9396])).
% 7.29/2.56  tff(c_9400, plain, (r2_hidden(k1_funct_1('#skF_11', '#skF_10'), k1_tarski('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_341, c_9399])).
% 7.29/2.56  tff(c_20, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.29/2.56  tff(c_9419, plain, (k1_funct_1('#skF_11', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_9400, c_20])).
% 7.29/2.56  tff(c_9502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_9419])).
% 7.29/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.29/2.56  
% 7.29/2.56  Inference rules
% 7.29/2.56  ----------------------
% 7.29/2.56  #Ref     : 2
% 7.29/2.56  #Sup     : 1131
% 7.29/2.56  #Fact    : 4
% 7.29/2.56  #Define  : 0
% 7.29/2.56  #Split   : 8
% 7.29/2.56  #Chain   : 0
% 7.29/2.56  #Close   : 0
% 7.29/2.56  
% 7.29/2.56  Ordering : KBO
% 7.29/2.56  
% 7.29/2.56  Simplification rules
% 7.29/2.56  ----------------------
% 7.29/2.56  #Subsume      : 209
% 7.29/2.56  #Demod        : 253
% 7.29/2.56  #Tautology    : 244
% 7.29/2.56  #SimpNegUnit  : 77
% 7.29/2.56  #BackRed      : 3
% 7.29/2.56  
% 7.29/2.56  #Partial instantiations: 11883
% 7.29/2.56  #Strategies tried      : 1
% 7.29/2.56  
% 7.29/2.56  Timing (in seconds)
% 7.29/2.56  ----------------------
% 7.29/2.56  Preprocessing        : 0.38
% 7.29/2.56  Parsing              : 0.17
% 7.29/2.57  CNF conversion       : 0.03
% 7.29/2.57  Main loop            : 1.40
% 7.29/2.57  Inferencing          : 0.72
% 7.29/2.57  Reduction            : 0.31
% 7.29/2.57  Demodulation         : 0.22
% 7.29/2.57  BG Simplification    : 0.07
% 7.29/2.57  Subsumption          : 0.24
% 7.29/2.57  Abstraction          : 0.07
% 7.29/2.57  MUC search           : 0.00
% 7.29/2.57  Cooper               : 0.00
% 7.29/2.57  Total                : 1.81
% 7.29/2.57  Index Insertion      : 0.00
% 7.29/2.57  Index Deletion       : 0.00
% 7.29/2.57  Index Matching       : 0.00
% 7.29/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
