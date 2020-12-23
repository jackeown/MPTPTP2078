%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:22 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 165 expanded)
%              Number of leaves         :   25 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  108 ( 348 expanded)
%              Number of equality atoms :   14 (  46 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_53,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_76,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_81,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_46,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_48,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_636,plain,(
    ! [B_724,A_725] :
      ( r1_ordinal1(B_724,A_725)
      | r1_ordinal1(A_725,B_724)
      | ~ v3_ordinal1(B_724)
      | ~ v3_ordinal1(A_725) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,
    ( r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | r1_ordinal1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_88,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_22,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_tarski(A_15)) = k1_ordinal1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_107,plain,(
    ! [D_37,B_38,A_39] :
      ( ~ r2_hidden(D_37,B_38)
      | r2_hidden(D_37,k2_xboole_0(A_39,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_145,plain,(
    ! [D_50,A_51] :
      ( ~ r2_hidden(D_50,k1_tarski(A_51))
      | r2_hidden(D_50,k1_ordinal1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_107])).

tff(c_149,plain,(
    ! [C_11] : r2_hidden(C_11,k1_ordinal1(C_11)) ),
    inference(resolution,[status(thm)],[c_22,c_145])).

tff(c_40,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ r1_ordinal1(A_16,B_17)
      | ~ v3_ordinal1(B_17)
      | ~ v3_ordinal1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_440,plain,(
    ! [B_647,A_648] :
      ( r2_hidden(B_647,A_648)
      | B_647 = A_648
      | r2_hidden(A_648,B_647)
      | ~ v3_ordinal1(B_647)
      | ~ v3_ordinal1(A_648) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_90,plain,(
    ! [D_32,A_33,B_34] :
      ( ~ r2_hidden(D_32,A_33)
      | r2_hidden(D_32,k2_xboole_0(A_33,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_98,plain,(
    ! [D_35,A_36] :
      ( ~ r2_hidden(D_35,A_36)
      | r2_hidden(D_35,k1_ordinal1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_90])).

tff(c_50,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_89,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_105,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_98,c_89])).

tff(c_455,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_440,c_105])).

tff(c_492,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_455])).

tff(c_503,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_492])).

tff(c_44,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_507,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_503,c_44])).

tff(c_510,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_507])).

tff(c_514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_88,c_510])).

tff(c_515,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_492])).

tff(c_519,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_89])).

tff(c_524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_519])).

tff(c_525,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_525])).

tff(c_530,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_643,plain,
    ( r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_636,c_530])).

tff(c_654,plain,(
    r1_ordinal1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_643])).

tff(c_529,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_864,plain,(
    ! [D_1260,B_1261,A_1262] :
      ( r2_hidden(D_1260,B_1261)
      | r2_hidden(D_1260,A_1262)
      | ~ r2_hidden(D_1260,k2_xboole_0(A_1262,B_1261)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_952,plain,(
    ! [D_1331,A_1332] :
      ( r2_hidden(D_1331,k1_tarski(A_1332))
      | r2_hidden(D_1331,A_1332)
      | ~ r2_hidden(D_1331,k1_ordinal1(A_1332)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_864])).

tff(c_20,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_996,plain,(
    ! [D_1349,A_1350] :
      ( D_1349 = A_1350
      | r2_hidden(D_1349,A_1350)
      | ~ r2_hidden(D_1349,k1_ordinal1(A_1350)) ) ),
    inference(resolution,[status(thm)],[c_952,c_20])).

tff(c_1020,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_529,c_996])).

tff(c_1021,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1020])).

tff(c_1025,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_1021,c_44])).

tff(c_1028,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_1025])).

tff(c_1032,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_654,c_1028])).

tff(c_1033,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1020])).

tff(c_1091,plain,(
    r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1033,c_654])).

tff(c_1094,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1033,c_530])).

tff(c_1110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1091,c_1094])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:28:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.57  
% 3.33/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.57  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.33/1.57  
% 3.33/1.57  %Foreground sorts:
% 3.33/1.57  
% 3.33/1.57  
% 3.33/1.57  %Background operators:
% 3.33/1.57  
% 3.33/1.57  
% 3.33/1.57  %Foreground operators:
% 3.33/1.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.33/1.57  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.33/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.33/1.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.33/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.57  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.33/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.33/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.33/1.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.33/1.57  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.33/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.33/1.57  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.33/1.57  
% 3.33/1.58  tff(f_91, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 3.33/1.58  tff(f_51, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 3.33/1.58  tff(f_41, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.33/1.58  tff(f_53, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 3.33/1.58  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.33/1.58  tff(f_61, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.33/1.58  tff(f_76, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 3.33/1.58  tff(f_81, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.33/1.58  tff(c_46, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.33/1.58  tff(c_48, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.33/1.58  tff(c_636, plain, (![B_724, A_725]: (r1_ordinal1(B_724, A_725) | r1_ordinal1(A_725, B_724) | ~v3_ordinal1(B_724) | ~v3_ordinal1(A_725))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.33/1.58  tff(c_56, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6')) | r1_ordinal1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.33/1.58  tff(c_88, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_56])).
% 3.33/1.58  tff(c_22, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.33/1.58  tff(c_36, plain, (![A_15]: (k2_xboole_0(A_15, k1_tarski(A_15))=k1_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.33/1.58  tff(c_107, plain, (![D_37, B_38, A_39]: (~r2_hidden(D_37, B_38) | r2_hidden(D_37, k2_xboole_0(A_39, B_38)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.33/1.58  tff(c_145, plain, (![D_50, A_51]: (~r2_hidden(D_50, k1_tarski(A_51)) | r2_hidden(D_50, k1_ordinal1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_107])).
% 3.33/1.58  tff(c_149, plain, (![C_11]: (r2_hidden(C_11, k1_ordinal1(C_11)))), inference(resolution, [status(thm)], [c_22, c_145])).
% 3.33/1.58  tff(c_40, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~r1_ordinal1(A_16, B_17) | ~v3_ordinal1(B_17) | ~v3_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.33/1.58  tff(c_440, plain, (![B_647, A_648]: (r2_hidden(B_647, A_648) | B_647=A_648 | r2_hidden(A_648, B_647) | ~v3_ordinal1(B_647) | ~v3_ordinal1(A_648))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.33/1.58  tff(c_90, plain, (![D_32, A_33, B_34]: (~r2_hidden(D_32, A_33) | r2_hidden(D_32, k2_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.33/1.58  tff(c_98, plain, (![D_35, A_36]: (~r2_hidden(D_35, A_36) | r2_hidden(D_35, k1_ordinal1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_90])).
% 3.33/1.58  tff(c_50, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.33/1.58  tff(c_89, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitLeft, [status(thm)], [c_50])).
% 3.33/1.58  tff(c_105, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_98, c_89])).
% 3.33/1.58  tff(c_455, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_440, c_105])).
% 3.33/1.58  tff(c_492, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_455])).
% 3.33/1.58  tff(c_503, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_492])).
% 3.33/1.58  tff(c_44, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.33/1.58  tff(c_507, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_503, c_44])).
% 3.33/1.58  tff(c_510, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_507])).
% 3.33/1.58  tff(c_514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_88, c_510])).
% 3.33/1.58  tff(c_515, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_492])).
% 3.33/1.58  tff(c_519, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_515, c_89])).
% 3.33/1.58  tff(c_524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149, c_519])).
% 3.33/1.58  tff(c_525, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 3.33/1.58  tff(c_528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_525])).
% 3.33/1.58  tff(c_530, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_56])).
% 3.33/1.58  tff(c_643, plain, (r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_636, c_530])).
% 3.33/1.58  tff(c_654, plain, (r1_ordinal1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_643])).
% 3.33/1.58  tff(c_529, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitRight, [status(thm)], [c_56])).
% 3.33/1.58  tff(c_864, plain, (![D_1260, B_1261, A_1262]: (r2_hidden(D_1260, B_1261) | r2_hidden(D_1260, A_1262) | ~r2_hidden(D_1260, k2_xboole_0(A_1262, B_1261)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.33/1.58  tff(c_952, plain, (![D_1331, A_1332]: (r2_hidden(D_1331, k1_tarski(A_1332)) | r2_hidden(D_1331, A_1332) | ~r2_hidden(D_1331, k1_ordinal1(A_1332)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_864])).
% 3.33/1.58  tff(c_20, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.33/1.58  tff(c_996, plain, (![D_1349, A_1350]: (D_1349=A_1350 | r2_hidden(D_1349, A_1350) | ~r2_hidden(D_1349, k1_ordinal1(A_1350)))), inference(resolution, [status(thm)], [c_952, c_20])).
% 3.33/1.58  tff(c_1020, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_529, c_996])).
% 3.33/1.58  tff(c_1021, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_1020])).
% 3.33/1.58  tff(c_1025, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_1021, c_44])).
% 3.33/1.58  tff(c_1028, plain, (~r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_1025])).
% 3.33/1.58  tff(c_1032, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_654, c_1028])).
% 3.33/1.58  tff(c_1033, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_1020])).
% 3.33/1.58  tff(c_1091, plain, (r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1033, c_654])).
% 3.33/1.58  tff(c_1094, plain, (~r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1033, c_530])).
% 3.33/1.58  tff(c_1110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1091, c_1094])).
% 3.33/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.58  
% 3.33/1.58  Inference rules
% 3.33/1.58  ----------------------
% 3.33/1.58  #Ref     : 0
% 3.33/1.58  #Sup     : 144
% 3.33/1.58  #Fact    : 8
% 3.33/1.58  #Define  : 0
% 3.33/1.58  #Split   : 6
% 3.33/1.58  #Chain   : 0
% 3.33/1.58  #Close   : 0
% 3.33/1.58  
% 3.33/1.58  Ordering : KBO
% 3.33/1.58  
% 3.33/1.58  Simplification rules
% 3.33/1.58  ----------------------
% 3.33/1.58  #Subsume      : 14
% 3.33/1.58  #Demod        : 37
% 3.33/1.58  #Tautology    : 29
% 3.33/1.58  #SimpNegUnit  : 0
% 3.33/1.58  #BackRed      : 11
% 3.33/1.58  
% 3.33/1.58  #Partial instantiations: 820
% 3.33/1.58  #Strategies tried      : 1
% 3.33/1.58  
% 3.33/1.58  Timing (in seconds)
% 3.33/1.58  ----------------------
% 3.33/1.58  Preprocessing        : 0.33
% 3.33/1.58  Parsing              : 0.17
% 3.33/1.58  CNF conversion       : 0.02
% 3.33/1.58  Main loop            : 0.41
% 3.33/1.59  Inferencing          : 0.19
% 3.33/1.59  Reduction            : 0.09
% 3.33/1.59  Demodulation         : 0.06
% 3.33/1.59  BG Simplification    : 0.02
% 3.33/1.59  Subsumption          : 0.07
% 3.33/1.59  Abstraction          : 0.02
% 3.33/1.59  MUC search           : 0.00
% 3.33/1.59  Cooper               : 0.00
% 3.33/1.59  Total                : 0.76
% 3.33/1.59  Index Insertion      : 0.00
% 3.33/1.59  Index Deletion       : 0.00
% 3.33/1.59  Index Matching       : 0.00
% 3.33/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
