%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:19 EST 2020

% Result     : Theorem 6.82s
% Output     : CNFRefutation 7.05s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 147 expanded)
%              Number of leaves         :   31 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  110 ( 299 expanded)
%              Number of equality atoms :   11 (  22 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_5 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_74,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_92,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_30,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_7018,plain,(
    ! [A_707,B_708] :
      ( r1_ordinal1(A_707,B_708)
      | ~ r1_tarski(A_707,B_708)
      | ~ v3_ordinal1(B_708)
      | ~ v3_ordinal1(A_707) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_7031,plain,(
    ! [B_709] :
      ( r1_ordinal1(B_709,B_709)
      | ~ v3_ordinal1(B_709) ) ),
    inference(resolution,[status(thm)],[c_30,c_7018])).

tff(c_80,plain,(
    ! [B_33] : r2_hidden(B_33,k1_ordinal1(B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_90,plain,(
    v3_ordinal1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_100,plain,
    ( r2_hidden('#skF_6',k1_ordinal1('#skF_7'))
    | r1_ordinal1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_123,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_76,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | ~ r1_ordinal1(A_30,B_31)
      | ~ v3_ordinal1(B_31)
      | ~ v3_ordinal1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_105,plain,(
    ! [A_46] :
      ( v1_ordinal1(A_46)
      | ~ v3_ordinal1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_113,plain,(
    v1_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_92,c_105])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( r2_xboole_0(A_7,B_8)
      | B_8 = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1035,plain,(
    ! [A_173,B_174] :
      ( r2_hidden(A_173,B_174)
      | ~ r2_xboole_0(A_173,B_174)
      | ~ v3_ordinal1(B_174)
      | ~ v1_ordinal1(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_5427,plain,(
    ! [A_599,B_600] :
      ( r2_hidden(A_599,B_600)
      | ~ v3_ordinal1(B_600)
      | ~ v1_ordinal1(A_599)
      | B_600 = A_599
      | ~ r1_tarski(A_599,B_600) ) ),
    inference(resolution,[status(thm)],[c_20,c_1035])).

tff(c_173,plain,(
    ! [A_67,B_68] :
      ( ~ r2_hidden(A_67,B_68)
      | r2_hidden(A_67,k1_ordinal1(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_94,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_155,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_94])).

tff(c_180,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_173,c_155])).

tff(c_6025,plain,
    ( ~ v3_ordinal1('#skF_7')
    | ~ v1_ordinal1('#skF_6')
    | '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_5427,c_180])).

tff(c_6192,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_90,c_6025])).

tff(c_6197,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_6192])).

tff(c_6200,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_6197])).

tff(c_6204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_123,c_6200])).

tff(c_6205,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6192])).

tff(c_6210,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6205,c_155])).

tff(c_6217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6210])).

tff(c_6219,plain,(
    ~ r1_ordinal1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_112,plain,(
    v1_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_90,c_105])).

tff(c_6218,plain,(
    r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_6220,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_6222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6218,c_6220])).

tff(c_6224,plain,(
    r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_6632,plain,(
    ! [B_679,A_680] :
      ( B_679 = A_680
      | r2_hidden(A_680,B_679)
      | ~ r2_hidden(A_680,k1_ordinal1(B_679)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6648,plain,
    ( '#skF_7' = '#skF_6'
    | r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_6224,c_6632])).

tff(c_6651,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_6648])).

tff(c_68,plain,(
    ! [B_29,A_26] :
      ( r1_tarski(B_29,A_26)
      | ~ r2_hidden(B_29,A_26)
      | ~ v1_ordinal1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6654,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | ~ v1_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6651,c_68])).

tff(c_6660,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_6654])).

tff(c_6887,plain,(
    ! [A_694,B_695] :
      ( r1_ordinal1(A_694,B_695)
      | ~ r1_tarski(A_694,B_695)
      | ~ v3_ordinal1(B_695)
      | ~ v3_ordinal1(A_694) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6896,plain,
    ( r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6660,c_6887])).

tff(c_6907,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_6896])).

tff(c_6909,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6219,c_6907])).

tff(c_6910,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6648])).

tff(c_6916,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6910,c_6219])).

tff(c_7034,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_7031,c_6916])).

tff(c_7038,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_7034])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:24:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.82/2.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.82/2.49  
% 6.82/2.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.82/2.49  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_5 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 6.82/2.49  
% 6.82/2.49  %Foreground sorts:
% 6.82/2.49  
% 6.82/2.49  
% 6.82/2.49  %Background operators:
% 6.82/2.49  
% 6.82/2.49  
% 6.82/2.49  %Foreground operators:
% 6.82/2.49  tff('#skF_5', type, '#skF_5': $i > $i).
% 6.82/2.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.82/2.49  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 6.82/2.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.82/2.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.82/2.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.82/2.49  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 6.82/2.49  tff('#skF_7', type, '#skF_7': $i).
% 6.82/2.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.82/2.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.82/2.49  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 6.82/2.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.82/2.49  tff('#skF_6', type, '#skF_6': $i).
% 6.82/2.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.82/2.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.82/2.49  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 6.82/2.49  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 6.82/2.49  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 6.82/2.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 6.82/2.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.82/2.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.82/2.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.82/2.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.82/2.49  
% 7.05/2.50  tff(f_130, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 7.05/2.50  tff(f_47, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.05/2.50  tff(f_91, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 7.05/2.50  tff(f_97, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 7.05/2.50  tff(f_74, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 7.05/2.50  tff(f_41, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 7.05/2.50  tff(f_106, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_ordinal1)).
% 7.05/2.50  tff(f_83, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 7.05/2.50  tff(c_92, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.05/2.50  tff(c_30, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.05/2.50  tff(c_7018, plain, (![A_707, B_708]: (r1_ordinal1(A_707, B_708) | ~r1_tarski(A_707, B_708) | ~v3_ordinal1(B_708) | ~v3_ordinal1(A_707))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.05/2.50  tff(c_7031, plain, (![B_709]: (r1_ordinal1(B_709, B_709) | ~v3_ordinal1(B_709))), inference(resolution, [status(thm)], [c_30, c_7018])).
% 7.05/2.50  tff(c_80, plain, (![B_33]: (r2_hidden(B_33, k1_ordinal1(B_33)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.05/2.50  tff(c_90, plain, (v3_ordinal1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.05/2.50  tff(c_100, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7')) | r1_ordinal1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.05/2.50  tff(c_123, plain, (r1_ordinal1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_100])).
% 7.05/2.50  tff(c_76, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | ~r1_ordinal1(A_30, B_31) | ~v3_ordinal1(B_31) | ~v3_ordinal1(A_30))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.05/2.50  tff(c_105, plain, (![A_46]: (v1_ordinal1(A_46) | ~v3_ordinal1(A_46))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.05/2.50  tff(c_113, plain, (v1_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_92, c_105])).
% 7.05/2.50  tff(c_20, plain, (![A_7, B_8]: (r2_xboole_0(A_7, B_8) | B_8=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.05/2.50  tff(c_1035, plain, (![A_173, B_174]: (r2_hidden(A_173, B_174) | ~r2_xboole_0(A_173, B_174) | ~v3_ordinal1(B_174) | ~v1_ordinal1(A_173))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.05/2.50  tff(c_5427, plain, (![A_599, B_600]: (r2_hidden(A_599, B_600) | ~v3_ordinal1(B_600) | ~v1_ordinal1(A_599) | B_600=A_599 | ~r1_tarski(A_599, B_600))), inference(resolution, [status(thm)], [c_20, c_1035])).
% 7.05/2.50  tff(c_173, plain, (![A_67, B_68]: (~r2_hidden(A_67, B_68) | r2_hidden(A_67, k1_ordinal1(B_68)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.05/2.50  tff(c_94, plain, (~r1_ordinal1('#skF_6', '#skF_7') | ~r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.05/2.50  tff(c_155, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_94])).
% 7.05/2.50  tff(c_180, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_173, c_155])).
% 7.05/2.50  tff(c_6025, plain, (~v3_ordinal1('#skF_7') | ~v1_ordinal1('#skF_6') | '#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_5427, c_180])).
% 7.05/2.50  tff(c_6192, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_90, c_6025])).
% 7.05/2.50  tff(c_6197, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_6192])).
% 7.05/2.50  tff(c_6200, plain, (~r1_ordinal1('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_6197])).
% 7.05/2.50  tff(c_6204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_123, c_6200])).
% 7.05/2.50  tff(c_6205, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_6192])).
% 7.05/2.50  tff(c_6210, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6205, c_155])).
% 7.05/2.50  tff(c_6217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_6210])).
% 7.05/2.50  tff(c_6219, plain, (~r1_ordinal1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_100])).
% 7.05/2.50  tff(c_112, plain, (v1_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_90, c_105])).
% 7.05/2.50  tff(c_6218, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(splitRight, [status(thm)], [c_100])).
% 7.05/2.50  tff(c_6220, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(splitLeft, [status(thm)], [c_94])).
% 7.05/2.50  tff(c_6222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6218, c_6220])).
% 7.05/2.50  tff(c_6224, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(splitRight, [status(thm)], [c_94])).
% 7.05/2.50  tff(c_6632, plain, (![B_679, A_680]: (B_679=A_680 | r2_hidden(A_680, B_679) | ~r2_hidden(A_680, k1_ordinal1(B_679)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.05/2.50  tff(c_6648, plain, ('#skF_7'='#skF_6' | r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_6224, c_6632])).
% 7.05/2.50  tff(c_6651, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_6648])).
% 7.05/2.50  tff(c_68, plain, (![B_29, A_26]: (r1_tarski(B_29, A_26) | ~r2_hidden(B_29, A_26) | ~v1_ordinal1(A_26))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.05/2.50  tff(c_6654, plain, (r1_tarski('#skF_6', '#skF_7') | ~v1_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_6651, c_68])).
% 7.05/2.50  tff(c_6660, plain, (r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_6654])).
% 7.05/2.50  tff(c_6887, plain, (![A_694, B_695]: (r1_ordinal1(A_694, B_695) | ~r1_tarski(A_694, B_695) | ~v3_ordinal1(B_695) | ~v3_ordinal1(A_694))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.05/2.50  tff(c_6896, plain, (r1_ordinal1('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_6660, c_6887])).
% 7.05/2.50  tff(c_6907, plain, (r1_ordinal1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_6896])).
% 7.05/2.50  tff(c_6909, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6219, c_6907])).
% 7.05/2.50  tff(c_6910, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_6648])).
% 7.05/2.50  tff(c_6916, plain, (~r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6910, c_6219])).
% 7.05/2.50  tff(c_7034, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_7031, c_6916])).
% 7.05/2.50  tff(c_7038, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_7034])).
% 7.05/2.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/2.50  
% 7.05/2.50  Inference rules
% 7.05/2.50  ----------------------
% 7.05/2.50  #Ref     : 0
% 7.05/2.50  #Sup     : 1411
% 7.05/2.50  #Fact    : 6
% 7.05/2.50  #Define  : 0
% 7.05/2.50  #Split   : 7
% 7.05/2.50  #Chain   : 0
% 7.05/2.50  #Close   : 0
% 7.05/2.50  
% 7.05/2.50  Ordering : KBO
% 7.05/2.50  
% 7.05/2.50  Simplification rules
% 7.05/2.50  ----------------------
% 7.05/2.50  #Subsume      : 200
% 7.05/2.50  #Demod        : 56
% 7.05/2.50  #Tautology    : 61
% 7.05/2.50  #SimpNegUnit  : 22
% 7.05/2.50  #BackRed      : 15
% 7.05/2.50  
% 7.05/2.50  #Partial instantiations: 0
% 7.05/2.50  #Strategies tried      : 1
% 7.05/2.50  
% 7.05/2.50  Timing (in seconds)
% 7.05/2.50  ----------------------
% 7.05/2.51  Preprocessing        : 0.33
% 7.05/2.51  Parsing              : 0.16
% 7.05/2.51  CNF conversion       : 0.03
% 7.05/2.51  Main loop            : 1.41
% 7.05/2.51  Inferencing          : 0.41
% 7.05/2.51  Reduction            : 0.40
% 7.05/2.51  Demodulation         : 0.23
% 7.05/2.51  BG Simplification    : 0.05
% 7.05/2.51  Subsumption          : 0.44
% 7.05/2.51  Abstraction          : 0.07
% 7.05/2.51  MUC search           : 0.00
% 7.05/2.51  Cooper               : 0.00
% 7.05/2.51  Total                : 1.77
% 7.05/2.51  Index Insertion      : 0.00
% 7.05/2.51  Index Deletion       : 0.00
% 7.05/2.51  Index Matching       : 0.00
% 7.05/2.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
